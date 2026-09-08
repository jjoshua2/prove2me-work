#!/usr/bin/env python3
"""Publish and prove audited Natura/Hirsch helper results.

The script is idempotent, never prints credentials, and refuses to reuse a
same-named platform declaration whose formal content differs from the reviewed
local declaration.
"""
from __future__ import annotations

import datetime
import json
import os
from pathlib import Path
import re
import time
import urllib.parse
import urllib.request
import uuid

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "natura_publish_packet"
BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
DEF_NAME = "Hirsch_circuit_slack_model"
THEOREM_NAME = "HirschCircuit.rowMap_injective_of_bounded"

PREAMBLE = """import Definitions.Def_Hirsch_circuit_slack_model

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch
"""

FORMAL = """namespace HirschCircuit

theorem rowMap_injective_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) :
    Function.Injective (rowMap a) := by sorry

end HirschCircuit"""

EXPLANATION = """A bounded nonempty H-polytope cannot have a nonzero direction annihilated by every retained row. If p-q is in the kernel of the row-evaluation map, then every point x+t(p-q) satisfies exactly the same inequalities for all real t. Choosing t large enough contradicts boundedness. This is the injectivity bridge used to identify an H-polytope with its nonnegative slack slice."""


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError("authenticated redirects disabled")


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.expires = 0.0
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode(),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with self.opener.open(req, timeout=45) as response:
            data = json.load(response)
        self.token = data["access_token"]
        self.expires = float(data.get("expires_at", time.time() + 3500))
        self.version = data.get("version")

    def request(self, path: str, data=None, method: str = "GET", content_type: str = "application/json"):
        if not path.startswith("/") or path.startswith("//"):
            raise ValueError("relative API path required")
        if not self.token or time.time() + 60 >= self.expires:
            self.refresh()
        body = json.dumps(data).encode() if data is not None and not isinstance(data, bytes) else data
        req = urllib.request.Request(
            BASE + path,
            data=body,
            headers={"Authorization": "Bearer " + self.token, "Content-Type": content_type},
            method=method,
        )
        with self.opener.open(req, timeout=60) as response:
            return json.load(response)

    def verify(self, theorem_id: str, proof: str, explanation: str):
        boundary = "----Prove2Me" + uuid.uuid4().hex
        parts = []
        for name, value in [
            ("theorem_id", theorem_id),
            ("proof_type", "prove"),
            ("explanation", explanation),
        ]:
            parts.append(
                f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n'
            )
        parts.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
            f'Content-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n'
        )
        return self.request(
            "/verify",
            "".join(parts).encode(),
            "POST",
            "multipart/form-data; boundary=" + boundary,
        )


def normalize(text: str) -> str:
    return re.sub(r"\s+", "", text or "")


def write(name: str, value) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def rows(api: API, theorem_name: str):
    query = urllib.parse.urlencode(
        {"env": PIN, "theorem_name": theorem_name, "limit": 50, "offset": 0}
    )
    result = api.request("/theorems?" + query)
    return result.get("theorems", [])


def wait_job(api: API, job_id: str, timeout: int = 300):
    end = time.monotonic() + timeout
    while True:
        item = api.request("/publish-jobs/" + job_id)
        if item.get("status") in {"PUBLISHED", "FAILED", "ERROR"}:
            return item
        if time.monotonic() >= end:
            return item
        time.sleep(6)


def wait_verdict(api: API, submission_id: str, timeout: int = 300):
    end = time.monotonic() + timeout
    terminal = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
    while True:
        item = api.request("/verify?" + urllib.parse.urlencode({"submission_id": submission_id}))
        if item.get("status") in terminal:
            return item
        if time.monotonic() >= end:
            return item
        time.sleep(6)


def main() -> int:
    OUT.mkdir(exist_ok=True)
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    state = {
        "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "credential_present": bool(key),
        "definition_name": DEF_NAME,
        "theorem_name": THEOREM_NAME,
        "env": PIN,
    }
    if not key:
        state["error"] = "PROVE2ME_API_KEY unavailable"
        write("status.json", state)
        return 2

    api = API(key)
    definition_code = (ROOT / "Definitions/Def_Hirsch_circuit_slack_model.lean").read_text()
    proof = (ROOT / "Solutions/Sol_HirschCircuit_rowMap_injective_of_bounded.lean").read_text()

    # Publish/reuse the exact reviewed definition module.
    existing_defs = rows(api, DEF_NAME)
    if existing_defs:
        if len(existing_defs) != 1 or existing_defs[0].get("status") != "Definition":
            raise RuntimeError("definition-name collision")
        full = api.request("/theorems/" + existing_defs[0]["theorem_id"])
        server_code = full.get("definition") or full.get("definitions") or full.get("formal_statement") or ""
        if normalize(server_code) != normalize(definition_code):
            raise RuntimeError("existing definition differs from reviewed module")
        definition_id = full["theorem_id"]
    else:
        queued = api.request(
            "/submit-definition",
            {
                "definition_name": DEF_NAME,
                "definition_title": "Circuit slack-coordinate model",
                "definition": definition_code,
                "natural_language_statement": "Slack coordinates for finite H-polytope presentations, including the row-evaluation linear map, support-minimal elementary directions, the nonnegative slack image, maximal circuit steps, and padded circuit walks.",
                "source": "Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Sections 2–3; adapted to the Polynomial Hirsch formalization.",
                "tags": ["hirsch-conjecture", "polyhedra", "circuits", "slack-coordinates"],
                "env": PIN,
                "private": False,
            },
            "POST",
        )
        write("definition-queued.json", queued)
        job = wait_job(api, queued["job_id"])
        write("definition-job.json", job)
        if job.get("status") != "PUBLISHED":
            raise RuntimeError("definition publication failed: " + str(job.get("error_message", ""))[:500])
        definition_id = job["theorem_id"]
    state["definition_id"] = definition_id

    # Publish/reuse the exact theorem statement.
    existing = rows(api, THEOREM_NAME)
    if existing:
        if len(existing) != 1:
            raise RuntimeError("theorem-name collision")
        theorem = api.request("/theorems/" + existing[0]["theorem_id"])
        if normalize(theorem.get("formal_statement", "")) != normalize(FORMAL):
            raise RuntimeError("existing theorem statement differs from reviewed statement")
        theorem_id = theorem["theorem_id"]
    else:
        queued = api.request(
            "/submit-problem",
            {
                "env": PIN,
                "private": False,
                "problems": [
                    {
                        "theorem_name": THEOREM_NAME,
                        "theorem_title": "Bounded H-polytope row map is injective",
                        "formal_statement": FORMAL,
                        "natural_language_statement": "For a nonempty bounded H-polytope, the linear map sending a direction to all row inner products is injective. Otherwise a nonzero kernel direction would generate an entire feasible affine line, contradicting boundedness.",
                        "preamble": PREAMBLE,
                        "source": "Standard recession-space argument for bounded polyhedra; used in the slack-coordinate reduction of Bento Natura, arXiv:2602.06958v2, Sections 2–3.",
                        "tags": ["hirsch-conjecture", "polyhedra", "circuits", "slack-coordinates"],
                    }
                ],
            },
            "POST",
        )
        write("theorem-queued.json", queued)
        if queued.get("errors") or len(queued.get("jobs", [])) != 1:
            raise RuntimeError("problem publication did not queue exactly one job")
        job = wait_job(api, queued["jobs"][0]["job_id"])
        write("theorem-job.json", job)
        if job.get("status") != "PUBLISHED":
            raise RuntimeError("problem publication failed: " + str(job.get("error_message", ""))[:500])
        theorem_id = job["theorem_id"]
    state["theorem_id"] = theorem_id

    theorem = api.request("/theorems/" + theorem_id)
    state["status_before_verify"] = theorem.get("status")
    if theorem.get("status") == "Proved":
        state["status_after_verify"] = "Proved"
        state["skipped_verify"] = True
        write("status.json", state)
        print(json.dumps(state))
        return 0
    if theorem.get("status") != "Open":
        raise RuntimeError("unexpected theorem status before verification")

    queued = api.verify(theorem_id, proof, EXPLANATION)
    write("proof-queued.json", queued)
    submission_id = queued["submission_id"]
    state["submission_id"] = submission_id
    verdict = wait_verdict(api, submission_id)
    write("proof-verdict.json", verdict)
    state["verdict"] = verdict.get("status")
    state["status_after_verify"] = api.request("/theorems/" + theorem_id).get("status")
    write("status.json", state)
    print(json.dumps(state))
    return 0 if state["verdict"] == "ACCEPTED" and state["status_after_verify"] == "Proved" else 3


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        # Do not serialize request objects, headers, API keys, or bearer tokens.
        OUT.mkdir(exist_ok=True)
        failure = {
            "failed_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "error_type": type(exc).__name__,
            "error": str(exc)[:700] if isinstance(exc, RuntimeError) else "publication failed",
        }
        write("failure.json", failure)
        print(json.dumps(failure))
        raise SystemExit(2)
