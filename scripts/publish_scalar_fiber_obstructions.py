#!/usr/bin/env python3
"""Publish the reviewed PR #11 scalar-fiber definition and two Open targets.

This script never submits a proof.  It first checks for exact-name collisions,
publishes the shared definition, then publishes the two theorem statements as
Open formalization targets in the pinned Hirsch environment.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import time
import urllib.parse
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "scalar_fiber_packet"
BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
DEF_NAME = "Hirsch_scalar_fiber_model"
THEOREMS = [
    (
        "Hirsch.scalar_height_fiber_monotone_path_bound",
        "Scalar-height gluing synchronizes strictly monotone factor paths additively",
        "If each factor has a genuine edge path of L_i strictly decreasing in its affine height, with aligned endpoint heights, then the common-height fiber has an endpoint edge walk of at most 1 + sum_i (L_i - 1) steps. This is the class-wide obstruction proved mathematically in prove2me-work PR #11. For the Q28 six-edge monotone apex path it implies every independently scalar-glued/projectively skewed k-copy construction has apex distance at most 5k+1. This is an Open Lean formalization target, not a conjecture inferred from finite experiments.",
    ),
    (
        "Hirsch.scalar_height_fiber_diameter_linear",
        "Affine scalar-height fibers of fixed bounded seeds have linear graph diameter",
        "For finitely many nonempty compact convex seed polytopes with at most v_i vertices and e_i undirected edges, represented by explicit finite covers, the common affine-height fiber has graph diameter at most sum_i (3*v_i + e_i - 1). This is the general scalar-fiber obstruction proved mathematically in prove2me-work PR #11: descend both endpoints to the common bottom level, then route in the product of bottom sections. For k Q28 copies (274 vertices, 720 edges each), the bound is 1541k. Thus arbitrary scalar-height choices on fixed seeds cannot yield a superpolynomial family. This is an Open Lean formalization target, not a literature-priority claim.",
    ),
]


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.expires = 0.0

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode(),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=45) as response:
            data = json.load(response)
        self.token = data["access_token"]
        self.expires = float(data.get("expires_at", time.time() + 3500))
        print("AUTH ok version=" + str(data.get("version", "unknown")))

    def request(self, path: str, data=None, method: str = "GET"):
        if not self.token or time.time() + 60 >= self.expires:
            self.refresh()
        body = None if data is None else json.dumps(data).encode()
        headers = {"Authorization": "Bearer " + self.token, "Accept": "application/json"}
        if data is not None:
            headers["Content-Type"] = "application/json"
        req = urllib.request.Request(BASE + path, data=body, headers=headers, method=method)
        with urllib.request.urlopen(req, timeout=60) as response:
            return json.load(response)


def exact_rows(api: API, name: str):
    query = urllib.parse.urlencode({"env": PIN, "theorem_name": name, "limit": 100, "offset": 0})
    data = api.request("/theorems?" + query)
    return [
        row for row in data.get("theorems", [])
        if row.get("theorem_name") == name and row.get("mathlib_rev") == PIN
    ]


def wait_job(api: API, job_id: str, timeout: float = 300.0):
    stop = time.monotonic() + timeout
    while True:
        row = api.request("/publish-jobs/" + job_id)
        if row.get("status") in {"PUBLISHED", "FAILED", "ERROR"}:
            return row
        if time.monotonic() >= stop:
            raise RuntimeError("publish job timed out")
        time.sleep(7)


def theorem_decl(path: Path, name: str) -> str:
    text = path.read_text()
    marker = "theorem " + name
    if marker not in text:
        raise RuntimeError("missing theorem declaration: " + name)
    decl = marker + text.split(marker, 1)[1]
    if not re.search(r":= by sorry\s*$", decl):
        raise RuntimeError("theorem stub shape changed: " + name)
    return decl.strip()


def main() -> int:
    OUT.mkdir(exist_ok=True)
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)
    api.refresh()

    definition_path = ROOT / "Definitions/Def_Hirsch_scalar_fiber_model.lean"
    definition_code = definition_path.read_text()
    definition_payload = {
        "env": PIN,
        "private": False,
        "definition_name": DEF_NAME,
        "definition_title": "Common affine-height fibers, endpoint walks, and finite vertex/edge covers",
        "definition": definition_code,
        "natural_language_statement": "Definitions for common scalar-height fibers of finitely many Euclidean factor sets; fixed-endpoint padded graph walks; strictly height-decreasing edge walks; and explicit finite covers witnessing upper bounds on the number of vertices and undirected edges.",
        "source": "Definitions introduced to formalize the scalar-fiber obstruction arguments in jjoshua2/prove2me-work PR #11 (2026-09-08).",
        "tags": ["convex-geometry", "polytopes"],
    }

    prior_def = exact_rows(api, DEF_NAME)
    if prior_def:
        if len(prior_def) != 1 or prior_def[0].get("status") != "Definition":
            raise RuntimeError("definition-name collision requires review")
        definition_id = prior_def[0].get("theorem_id")
        print("DEFINITION existing id=" + str(definition_id))
    else:
        queued = api.request("/submit-definition", definition_payload, "POST")
        (OUT / "definition-queued.json").write_text(json.dumps(queued, indent=2) + "\n")
        job_id = queued.get("job_id")
        if not job_id:
            raise RuntimeError("definition publication returned no job")
        verdict = wait_job(api, job_id)
        (OUT / "definition-status.json").write_text(json.dumps(verdict, indent=2) + "\n")
        if verdict.get("status") != "PUBLISHED":
            raise RuntimeError("definition publication failed")
        definition_id = verdict.get("theorem_id")
        print("DEFINITION published id=" + str(definition_id))

    preamble = (
        "import Definitions.Def_Hirsch_scalar_fiber_model\n"
        "set_option autoImplicit false\n"
        "open scoped RealInnerProductSpace BigOperators"
    )
    results = {"definition_id": definition_id, "theorems": {}}
    for name, title, description in THEOREMS:
        prior = exact_rows(api, name)
        if prior:
            if len(prior) != 1:
                raise RuntimeError("theorem-name collision requires review: " + name)
            results["theorems"][name] = {
                "theorem_id": prior[0].get("theorem_id"),
                "status": prior[0].get("status"),
                "existing": True,
            }
            print(name + " existing status=" + str(prior[0].get("status")))
            continue

        file_name = "Thm_" + name.replace(".", "_") + ".lean"
        decl = theorem_decl(ROOT / "Theorems" / file_name, name)
        payload = {
            "env": PIN,
            "private": False,
            "problems": [{
                "theorem_name": name,
                "theorem_title": title,
                "formal_statement": decl,
                "preamble": preamble,
                "natural_language_statement": description,
                "source": "Original mathematical argument developed in jjoshua2/prove2me-work PR #11 (2026-09-08); no literature-priority claim.",
                "tags": ["convex-geometry", "polytopes"],
            }],
        }
        queued = api.request("/submit-problem", payload, "POST")
        safe = name.replace(".", "_")
        (OUT / (safe + "-queued.json")).write_text(json.dumps(queued, indent=2) + "\n")
        jobs = queued.get("jobs", [])
        if queued.get("errors") or len(jobs) != 1:
            raise RuntimeError("problem publication did not return exactly one job: " + name)
        verdict = wait_job(api, jobs[0]["job_id"])
        (OUT / (safe + "-status.json")).write_text(json.dumps(verdict, indent=2) + "\n")
        if verdict.get("status") != "PUBLISHED":
            raise RuntimeError("problem publication failed: " + name)
        results["theorems"][name] = {
            "theorem_id": verdict.get("theorem_id"),
            "status": "Open",
            "existing": False,
        }
        print(name + " published id=" + str(verdict.get("theorem_id")))

    (OUT / "publication.json").write_text(json.dumps(results, indent=2) + "\n")
    print("SCALAR_FIBER_PUBLICATION " + json.dumps(results, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
