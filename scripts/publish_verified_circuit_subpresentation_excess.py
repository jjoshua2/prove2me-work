#!/usr/bin/env python3
"""Publish the independently compiled common-face subpresentation excess theorem.

Fail-closed publication from immutable GitHub Actions run 34516191146 at source
commit 47df3997447a3e0494fa7d7480c69e319c2a3564.  The publisher validates the
standalone proof hash and axiom receipts, checks public definition dependencies,
publishes/verifies the exact statement on Prove2Me 0.9.9, and asserts that the
Polynomial-Hirsch edge-refinement frontier remains Open before and after.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

BASE = "https://prove2.me/api/v1"
VERSION = "0.9.9"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
SOURCE_COMMIT = "47df3997447a3e0494fa7d7480c69e319c2a3564"
SOURCE_RUN = "34516191146"
MISSION_ID = "6078cb2d-3594-44b1-a01a-fd452ddae274"
FRONTIER_ID = "099c6686-560c-48fc-b2c2-18b6a620a06e"
COMMENT_MARKER = "circuit-subpresentation-excess:47df3997"

PUBLIC_DEPS = {
    "dc9161e6-0dae-4da5-ab82-91b871e2409e": ("Hirsch_common_face_geometry", "Definition"),
    "26b46900-d139-4f6c-b2e7-5088faed7b9e": ("Hirsch_circuit_slack_model", "Definition"),
}
PUBLIC_IMPORTS = [
    "Mathlib",
    "Definitions.Def_Hirsch_common_face_geometry",
    "Definitions.Def_Hirsch_circuit_slack_model",
]
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
AXIOM_REPORT = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.S)
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s", re.M)

THEOREM_NAME = "Hirsch.row_circuit_common_face_subpresentation_excess_defect"
THEOREM_TITLE = "Equivalent common-face subpresentations obey a circuit excess/defect budget"
PROOF_FILE = "subpresentation-solution.lean"
MANIFEST_FILE = "subpresentation-manifest.json"
ADAPTER_LOG = "subpresentation-adapter.log"
STANDALONE_LOG = "subpresentation-standalone.log"
ROOT_MODULE = "Solutions.Sol_Hirsch_row_circuit_common_face_subpresentation_excess_defect"
PROOF_SHA256 = "ca39305fe72a000f4e6aa2137b89e6592c34750e2585c339255019ebbaeb2502"

PREAMBLE = """import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Module Hirsch
"""

FORMAL = r"""namespace Hirsch

theorem row_circuit_common_face_subpresentation_excess_defect
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (M : ℕ)
    (hsub : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u v M) :
    ∃ m : ℕ, m ≤ M ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b u v (e j))
          (fun j => HirschCommonFace.commonFaceB a b u v (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b u v)
          (HirschCommonFace.commonFaceB a b u v) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b u v
      HirschCommonFace.commonFaceDim a b u v ≤ F.card ∧
      F.card ≤ M ∧
      (F.card - HirschCommonFace.commonFaceDim a b u v) +
          ((HirschCommonFace.commonFaceDim a b u v - 1) -
            Module.finrank ℝ
              (((HirschCommonFace.rowEvalMap a
                (F ∩ Finset.univ.filter (fun i =>
                  a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
                (HirschCommonFace.commonDirection a b u v)).range)) ≤
        n - d := by sorry

end Hirsch"""

NATURAL = (
    "Let u be a vertex of an n-row H-polyhedron in ambient dimension d and suppose v-u is a "
    "support-minimal row circuit. Let h be the dimension of the common-direction space cut out "
    "by the nonzero rows tight at both endpoints. If the canonical coordinate H-presentation of "
    "that common face has an equivalent subpresentation using at most M original rows, then one "
    "can choose such a subpresentation and discard exactly the chosen rows whose restricted "
    "normals vanish. For the remaining effective selected-row set F, h <= |F| <= M and the "
    "presentation excess |F|-h plus the selected neutral-rank defect is at most the ambient row "
    "excess n-d. This is a theorem about equivalent describing-row subpresentations; it does not "
    "identify |F| with the geometric number of genuine facets."
)

EXPLANATION = (
    "A row circuit has neutral rank exactly h-1 after restriction to the common-direction space. "
    "Deleting selected effective rows can reduce that neutral rank by no more than the number of "
    "deleted rows, while common tight rows and effective restricted rows satisfy the ambient count "
    "budget effective_count + d <= n+h. For an actual equivalent common-face subpresentation, the "
    "source vertex becomes the zero coordinate vertex; vertex extremality forces its nonzero "
    "selected normals to span h dimensions, hence h <= |F|. An ambient vertex likewise implies "
    "d <= n. These facts turn the subtraction-free selected-row budget into "
    "(|F|-h)+defect <= n-d. No claim equating the minimum row subpresentation with a genuine facet "
    "count is used."
)

TAGS = ["polyhedra", "hirsch-conjecture", "circuits", "common-faces", "rank-defect"]


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError("authenticated redirects disabled")


class API:
    def __init__(self, api_key: str):
        self.key = api_key
        self.token = ""
        self.expires = 0.0
        self.version = None
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode(),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with self.opener.open(req, timeout=45) as r:
            data = json.load(r)
        self.version = data.get("version")
        if self.version != VERSION:
            raise RuntimeError(f"unexpected Prove2Me version: {self.version!r}; expected {VERSION}")
        self.token = data["access_token"]
        self.expires = float(data.get("expires_at", time.time() + 3500))

    def request(self, path: str, data=None, method: str = "GET", content_type: str = "application/json"):
        if not self.token or time.time() + 60 >= self.expires:
            self.refresh()
        body = json.dumps(data).encode() if data is not None and not isinstance(data, bytes) else data
        req = urllib.request.Request(
            BASE + path,
            data=body,
            headers={"Authorization": "Bearer " + self.token, "Content-Type": content_type},
            method=method,
        )
        try:
            with self.opener.open(req, timeout=90) as r:
                if r.status == 204:
                    return {}
                return json.load(r)
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", "replace")[:3000]
            raise RuntimeError(f"Prove2Me HTTP {exc.code} on {method} {path}: {detail}") from exc

    def verify(self, theorem_id: str, proof: str, explanation: str):
        boundary = "----Prove2Me" + uuid.uuid4().hex
        chunks: list[str] = []
        for key, value in [
            ("theorem_id", theorem_id),
            ("proof_type", "prove"),
            ("explanation", explanation),
        ]:
            chunks.append(
                f'--{boundary}\r\nContent-Disposition: form-data; name="{key}"\r\n\r\n{value}\r\n'
            )
        chunks.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
            f'Content-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n'
        )
        return self.request(
            "/verify", "".join(chunks).encode(), "POST", "multipart/form-data; boundary=" + boundary
        )


def norm(s: str | None) -> str:
    return re.sub(r"\s+", "", s or "")


def sha256(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def save(out: Path, name: str, data) -> None:
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def locate(root: Path, name: str) -> Path:
    hits = list(root.rglob(name))
    if len(hits) != 1:
        raise RuntimeError(f"expected exactly one {name}, found {len(hits)}")
    return hits[0]


def audit_axioms(text: str, *, label: str) -> None:
    if "sorryAx" in text:
        raise RuntimeError(f"{label}: contains sorryAx")
    reports = AXIOM_REPORT.findall(text)
    if not reports:
        raise RuntimeError(f"{label}: no axiom report found")
    for name, raw in reports:
        axioms = {x.strip() for x in raw.split(",") if x.strip()}
        extra = axioms - ALLOWED_AXIOMS
        if extra:
            raise RuntimeError(f"{label}: {name} has nonstandard axioms {sorted(extra)}")


def validate_artifact(root: Path) -> str:
    source_commit = locate(root, "source-commit.txt").read_text(encoding="utf-8").strip()
    if source_commit != SOURCE_COMMIT:
        raise RuntimeError(f"source commit mismatch: {source_commit!r}")
    proof = locate(root, PROOF_FILE).read_text(encoding="utf-8")
    manifest = json.loads(locate(root, MANIFEST_FILE).read_text(encoding="utf-8"))
    core_log = locate(root, "core.log").read_text(encoding="utf-8")
    adapter_log = locate(root, ADAPTER_LOG).read_text(encoding="utf-8")
    standalone_log = locate(root, STANDALONE_LOG).read_text(encoding="utf-8")
    if sha256(proof) != PROOF_SHA256:
        raise RuntimeError("standalone proof hash mismatch")
    if manifest.get("output_sha256") != PROOF_SHA256:
        raise RuntimeError("manifest output hash mismatch")
    if manifest.get("root_module") != ROOT_MODULE:
        raise RuntimeError("manifest root-module mismatch")
    if manifest.get("public_imports") != PUBLIC_IMPORTS:
        raise RuntimeError("manifest public import set mismatch")
    if FORBIDDEN.search(proof):
        raise RuntimeError("standalone proof contains forbidden token/declaration")
    if len(re.findall(r"(?m)^\s*theorem\s+solution\b", proof)) != 1:
        raise RuntimeError("standalone proof must contain exactly one theorem solution")
    audit_axioms(core_log, label="core.log")
    audit_axioms(adapter_log, label=ADAPTER_LOG)
    audit_axioms(standalone_log, label=STANDALONE_LOG)
    if "'solution' depends on axioms:" not in standalone_log and "'solution' does not depend on any axioms" not in standalone_log:
        raise RuntimeError("standalone solution axiom receipt missing")
    return proof


def theorem_rows(api: API, name: str):
    qs = urllib.parse.urlencode({"env": PIN, "theorem_name": name, "limit": 20, "offset": 0})
    return [
        row for row in api.request("/theorems?" + qs).get("theorems", [])
        if row.get("theorem_name") == name and not row.get("deprecated_at")
    ]


def poll_publish(api: API, job_id: str, timeout: int = 300):
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        item = api.request("/publish-jobs/" + job_id)
        if item.get("status") in {"PUBLISHED", "FAILED", "ERROR"}:
            return item
        time.sleep(4)
    raise TimeoutError("publication job timed out")


def poll_verify(api: API, submission_id: str, timeout: int = 900):
    end = time.monotonic() + timeout
    terminal = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
    while time.monotonic() < end:
        item = api.request("/verify?" + urllib.parse.urlencode({"submission_id": submission_id}))
        if item.get("status") in terminal:
            return item
        time.sleep(4)
    raise TimeoutError("proof verification timed out")


def ensure_public_dependencies(api: API, out: Path) -> None:
    rows = {}
    for theorem_id, (name, status) in PUBLIC_DEPS.items():
        item = api.request("/theorems/" + theorem_id)
        rows[theorem_id] = item
        if item.get("theorem_name") != name or item.get("status") != status or item.get("deprecated_at"):
            raise RuntimeError(f"public dependency mismatch for {theorem_id}")
    save(out, "public-dependencies.json", rows)


def ensure_frontier_open(api: API, out: Path, suffix: str) -> None:
    item = api.request("/theorems/" + FRONTIER_ID)
    save(out, f"frontier-{suffix}.json", item)
    if item.get("theorem_name") != "Hirsch.polynomial_edge_refinement_of_circuit_walks":
        raise RuntimeError("frontier theorem identity changed")
    if item.get("status") != "Open":
        raise RuntimeError(f"frontier no longer Open: {item.get('status')}")


def register_or_reuse(api: API, out: Path) -> str:
    rows = theorem_rows(api, THEOREM_NAME)
    if rows:
        if len(rows) != 1:
            raise RuntimeError(f"{THEOREM_NAME}: name collision with {len(rows)} live rows")
        theorem = api.request("/theorems/" + rows[0]["theorem_id"])
        if norm(theorem.get("formal_statement")) != norm(FORMAL):
            raise RuntimeError("existing theorem has a different formal statement")
        save(out, "reused-theorem.json", theorem)
        return theorem["theorem_id"]

    queued = api.request(
        "/submit-problem",
        {
            "env": PIN,
            "private": False,
            "problems": [{
                "theorem_name": THEOREM_NAME,
                "theorem_title": THEOREM_TITLE,
                "formal_statement": FORMAL,
                "natural_language_statement": NATURAL,
                "preamble": PREAMBLE,
                "source": (
                    "Kernel- and standalone-verified proof from jjoshua2/prove2me-work "
                    f"commit {SOURCE_COMMIT}, Actions run {SOURCE_RUN}. This proves an equivalent "
                    "row-subpresentation defect/excess statement, not a geometric facet-count theorem."
                ),
                "tags": TAGS,
            }],
        },
        "POST",
    )
    save(out, "problem-queued.json", queued)
    if queued.get("errors") or len(queued.get("jobs", [])) != 1:
        raise RuntimeError("problem publication did not queue exactly one job")
    job = poll_publish(api, queued["jobs"][0]["job_id"])
    save(out, "problem-job.json", job)
    if job.get("status") != "PUBLISHED" or not job.get("theorem_id"):
        raise RuntimeError(f"problem publication failed: {job.get('status')}")
    return job["theorem_id"]


def verify_one(api: API, theorem_id: str, proof: str, out: Path) -> dict:
    theorem = api.request("/theorems/" + theorem_id)
    save(out, "theorem-before-verify.json", theorem)
    if norm(theorem.get("formal_statement")) != norm(FORMAL):
        raise RuntimeError("server formal statement mismatch before verify")
    if theorem.get("status") == "Proved":
        return {"theorem_id": theorem_id, "status": "Proved", "verification": "SKIPPED_ALREADY_PROVED"}
    if theorem.get("status") != "Open":
        raise RuntimeError(f"unexpected theorem status {theorem.get('status')}")
    queued = api.verify(theorem_id, proof, EXPLANATION)
    save(out, "proof-queued.json", queued)
    sid = queued.get("submission_id")
    if not sid:
        raise RuntimeError("verification did not return submission_id")
    verdict = poll_verify(api, sid)
    save(out, "proof-verdict.json", verdict)
    final = api.request("/theorems/" + theorem_id)
    save(out, "theorem-final.json", final)
    if verdict.get("status") != "ACCEPTED" or final.get("status") != "Proved":
        raise RuntimeError(
            f"proof not accepted: verdict={verdict.get('status')} final={final.get('status')}"
        )
    return {
        "theorem_id": theorem_id,
        "submission_id": sid,
        "verdict": verdict.get("status"),
        "status": final.get("status"),
    }


def post_mission_comment(api: API, result: dict, out: Path) -> str:
    comments = api.request(f"/missions/{MISSION_ID}/comments?limit=100&offset=0")
    existing = [
        c for c in comments.get("comments", [])
        if COMMENT_MARKER in (c.get("body_md") or "")
    ]
    if existing:
        if len(existing) != 1:
            raise RuntimeError("multiple existing publication comments with marker")
        save(out, "mission-comment-reused.json", existing[0])
        return existing[0]["id"]

    body = f"""## Formal circuit defect/excess update

A stronger common-face rank-defect result is now kernel-checked and Prove2Me-verified:

- [equivalent common-face subpresentations obey a circuit excess/defect budget](p2m:theorem/{result['theorem_id']}): an actual equivalent common-face row subpresentation yields an effective selected-row set `F` with `h <= |F|` and `( |F|-h ) + neutral-rank-defect <= n-d`.

This closes the **row-subpresentation** version of the defect/excess charging step. It deliberately does **not** identify `|F|` with the geometric number of genuine facets; that semantic facet-representative bridge remains separate. It also supplies no ordinary edge route. The formal Open frontier therefore remains [polynomial edge refinement of circuit walks](p2m:theorem/{FRONTIER_ID}). No new child or cyclic decomposition was created.

Verification provenance: source commit `{SOURCE_COMMIT}`, Actions run `{SOURCE_RUN}`, standalone SHA-256 `{PROOF_SHA256}`; only `propext`, `Classical.choice`, and `Quot.sound` occur in the audited proof.

<!-- {COMMENT_MARKER} -->
"""
    created = api.request(
        f"/missions/{MISSION_ID}/comments",
        {"body_md": body, "tags": ["strategy", "reference"]},
        "POST",
    )
    save(out, "mission-comment-created.json", created)
    cid = created.get("id")
    if not cid:
        raise RuntimeError("mission comment response missing id")
    readback = api.request(f"/missions/{MISSION_ID}/comments?limit=100&offset=0")
    save(out, "mission-comments-readback.json", readback)
    matches = [c for c in readback.get("comments", []) if c.get("id") == cid]
    if len(matches) != 1:
        raise RuntimeError("mission comment not found on readback")
    refs = {(r.get("type"), r.get("id")) for r in matches[0].get("references", [])}
    expected = {("theorem", result["theorem_id"]), ("theorem", FRONTIER_ID)}
    if not expected.issubset(refs):
        raise RuntimeError(f"mission comment reference readback mismatch: {refs}")
    return cid


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--artifact-root", type=Path, required=True)
    p.add_argument("--out", type=Path, default=Path("prove2me_circuit_subpresentation_excess_receipts"))
    args = p.parse_args()
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")

    proof = validate_artifact(args.artifact_root)
    out = args.out
    summary = {
        "started_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "platform_expected": VERSION,
        "env": PIN,
        "source_commit": SOURCE_COMMIT,
        "source_run": SOURCE_RUN,
        "artifact_validation": "PASSED",
        "proof_sha256": PROOF_SHA256,
        "theorem_name": THEOREM_NAME,
    }
    save(out, "validation.json", summary)

    api = API(key)
    api.refresh()
    summary["platform_version"] = api.version
    ensure_public_dependencies(api, out)
    ensure_frontier_open(api, out, "before")
    theorem_id = register_or_reuse(api, out)
    result = verify_one(api, theorem_id, proof, out)
    ensure_frontier_open(api, out, "after")
    comment_id = post_mission_comment(api, result, out)
    summary.update(
        result=result,
        frontier_id=FRONTIER_ID,
        frontier_status="Open",
        mission_comment_id=comment_id,
        completed_at=dt.datetime.now(dt.timezone.utc).isoformat(),
        status="PUBLISHED_VERIFIED_AND_READ_BACK",
    )
    save(out, "status.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        save(
            Path("prove2me_circuit_subpresentation_excess_receipts"),
            "failure.json",
            {"error_type": type(exc).__name__, "error": str(exc)[:3000]},
        )
        raise
