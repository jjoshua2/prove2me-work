#!/usr/bin/env python3
"""Publish two independently compiled circuit rank/defect theorems to Prove2Me.

Fail-closed publication from immutable GitHub Actions run 34510652994 at source
commit a3b23e33d4ce9689c13fc11de4faebf83c102625.  The publisher validates the
standalone proof hashes and axiom receipts, checks the already-public definition
dependencies, publishes/verifies exact statements on Prove2Me 0.9.9, and
asserts that the existing Polynomial-Hirsch edge-refinement frontier stays Open.
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
SOURCE_COMMIT = "a3b23e33d4ce9689c13fc11de4faebf83c102625"
SOURCE_RUN = "34510652994"
MISSION_ID = "6078cb2d-3594-44b1-a01a-fd452ddae274"
FRONTIER_ID = "099c6686-560c-48fc-b2c2-18b6a620a06e"
COMMENT_MARKER = "circuit-neutral-rank-defect:a3b23e33"

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

PREAMBLE = """import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model

open scoped RealInnerProductSpace
open Set Module Hirsch
"""

SPECS = [
    {
        "key": "neutral",
        "name": "Hirsch.row_circuit_common_face_neutral_rank",
        "title": "A row circuit has codimension-one neutral rank on its common face",
        "proof_file": "neutral-solution.lean",
        "manifest_file": "neutral-manifest.json",
        "adapter_log": "neutral-adapter.log",
        "standalone_log": "neutral-standalone.log",
        "root_module": "Solutions.Sol_Hirsch_row_circuit_common_face_neutral_rank",
        "sha256": "b8ed5634d1767f65038eae0949fc522aff3f3ef8565fa84d7b3dbaabf1fb23b7",
        "formal": r"""namespace Hirsch

theorem row_circuit_common_face_neutral_rank
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((HirschCommonFace.rowEvalMap a
          (Finset.univ.filter (fun i =>
            a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
          (HirschCommonFace.commonDirection a b u v)).range) =
      HirschCommonFace.commonFaceDim a b u v - 1 := by sorry

end Hirsch""",
        "natural": (
            "Let u be a vertex of an n-row H-polytope in ambient dimension d, and suppose "
            "the displacement v-u is a support-minimal row circuit. Restrict to the linear "
            "direction space W cut out by all nonzero describing rows tight at both u and v. "
            "If h=dim W, then the nonzero ambient rows neutral on v-u, restricted to W, have "
            "linear rank exactly h-1. Thus the common kernel of those restricted neutral rows "
            "inside W is precisely the circuit line."
        ),
        "explanation": (
            "Support-minimality of the ambient row circuit implies that the common kernel of "
            "all nonzero neutral describing rows in the ambient space is exactly span(v-u). "
            "The displacement itself lies in the common-direction subspace W. Restricting the "
            "neutral-row evaluation map to W therefore leaves the same one-dimensional kernel. "
            "Rank-nullity on W gives neutral-row rank dim(W)-1."
        ),
        "tags": ["polyhedra", "hirsch-conjecture", "circuits", "common-faces", "rank"],
    },
    {
        "key": "defect",
        "name": "Hirsch.row_circuit_common_face_selected_row_defect_budget",
        "title": "Selected common-face rows obey a circuit rank-defect budget",
        "proof_file": "defect-solution.lean",
        "manifest_file": "defect-manifest.json",
        "adapter_log": "defect-adapter.log",
        "standalone_log": "defect-standalone.log",
        "root_module": "Solutions.Sol_Hirsch_row_circuit_common_face_selected_row_defect_budget",
        "sha256": "f7fe91e5e20341b382fdf809a6b3aa755f60da997b125b5ab03568b0fc15cd35",
        "formal": r"""namespace Hirsch

theorem row_circuit_common_face_selected_row_defect_budget
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (F : Finset (Fin n))
    (hF : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b u v) :
    F.card +
        ((HirschCommonFace.commonFaceDim a b u v - 1) -
          Module.finrank ℝ
            (((HirschCommonFace.rowEvalMap a
              (F ∩ Finset.univ.filter (fun i =>
                a i ≠ 0 ∧ ⟪a i, v - u⟫ = 0))).domRestrict
              (HirschCommonFace.commonDirection a b u v)).range)) +
        d ≤
      n + HirschCommonFace.commonFaceDim a b u v := by sorry

end Hirsch""",
        "natural": (
            "Let W be the common-direction space of a row-circuit displacement v-u based at "
            "a vertex u, with h=dim W. Choose any set F of describing rows whose restrictions "
            "to W are nonzero. Define the selected-row neutral-rank defect as h-1 minus the "
            "rank, on W, of the rows in F that are neutral on v-u. Then |F| plus this defect "
            "plus d is at most n+h. In the intended later application, choosing one effective "
            "row per genuine facet of the common face turns this row-level inequality into the "
            "facet-excess/defect budget; that facet-representative identification is a separate "
            "geometric step and is not claimed here."
        ),
        "explanation": (
            "All effective ambient neutral rows have rank h-1 on the common-direction space. "
            "Deleting k effective rows can lower linear rank by at most k, so the defect of a "
            "selected row set F is bounded by the number of effective rows omitted from F. "
            "Separately, common tight rows and effective rows are disjoint, and rank-nullity for "
            "the common tight equations gives effective_count + d <= n+h. Combining the two "
            "counts yields |F| + defect + d <= n+h."
        ),
        "tags": ["polyhedra", "hirsch-conjecture", "circuits", "common-faces", "rank-defect"],
    },
]


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


def validate_artifact(root: Path) -> dict[str, str]:
    source_commit = locate(root, "source-commit.txt").read_text(encoding="utf-8").strip()
    if source_commit != SOURCE_COMMIT:
        raise RuntimeError(f"source commit mismatch: {source_commit!r}")
    core_log = locate(root, "core.log").read_text(encoding="utf-8")
    audit_axioms(core_log, label="core.log")
    results: dict[str, str] = {}
    for spec in SPECS:
        proof = locate(root, spec["proof_file"]).read_text(encoding="utf-8")
        manifest = json.loads(locate(root, spec["manifest_file"]).read_text(encoding="utf-8"))
        adapter_log = locate(root, spec["adapter_log"]).read_text(encoding="utf-8")
        standalone_log = locate(root, spec["standalone_log"]).read_text(encoding="utf-8")
        digest = sha256(proof)
        if digest != spec["sha256"]:
            raise RuntimeError(f"{spec['key']}: proof hash mismatch {digest}")
        if manifest.get("output_sha256") != spec["sha256"]:
            raise RuntimeError(f"{spec['key']}: manifest output hash mismatch")
        if manifest.get("root_module") != spec["root_module"]:
            raise RuntimeError(f"{spec['key']}: manifest root-module mismatch")
        if manifest.get("public_imports") != PUBLIC_IMPORTS:
            raise RuntimeError(f"{spec['key']}: public import set mismatch")
        if FORBIDDEN.search(proof):
            raise RuntimeError(f"{spec['key']}: standalone proof contains forbidden token/declaration")
        if len(re.findall(r"(?m)^\s*theorem\s+solution\b", proof)) != 1:
            raise RuntimeError(f"{spec['key']}: standalone proof must contain exactly one theorem solution")
        audit_axioms(adapter_log, label=spec["adapter_log"])
        audit_axioms(standalone_log, label=spec["standalone_log"])
        if "'solution' depends on axioms:" not in standalone_log and "'solution' does not depend on any axioms" not in standalone_log:
            raise RuntimeError(f"{spec['key']}: standalone solution axiom receipt missing")
        results[spec["key"]] = proof
    return results


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


def register_or_reuse(api: API, spec: dict, out: Path) -> str:
    rows = theorem_rows(api, spec["name"])
    if rows:
        if len(rows) != 1:
            raise RuntimeError(f"{spec['name']}: name collision with {len(rows)} live rows")
        theorem = api.request("/theorems/" + rows[0]["theorem_id"])
        if norm(theorem.get("formal_statement")) != norm(spec["formal"]):
            raise RuntimeError(f"{spec['name']}: existing theorem has different formal statement")
        save(out, spec["key"] + "-reused-theorem.json", theorem)
        return theorem["theorem_id"]

    queued = api.request(
        "/submit-problem",
        {
            "env": PIN,
            "private": False,
            "problems": [{
                "theorem_name": spec["name"],
                "theorem_title": spec["title"],
                "formal_statement": spec["formal"],
                "natural_language_statement": spec["natural"],
                "preamble": PREAMBLE,
                "source": (
                    "Kernel- and standalone-verified proof from jjoshua2/prove2me-work "
                    f"commit {SOURCE_COMMIT}, Actions run {SOURCE_RUN}. This is project-derived "
                    "structural formalization; no novelty claim is made."
                ),
                "tags": spec["tags"],
            }],
        },
        "POST",
    )
    save(out, spec["key"] + "-problem-queued.json", queued)
    if queued.get("errors") or len(queued.get("jobs", [])) != 1:
        raise RuntimeError(f"{spec['key']}: problem publication did not queue exactly one job")
    job = poll_publish(api, queued["jobs"][0]["job_id"])
    save(out, spec["key"] + "-problem-job.json", job)
    if job.get("status") != "PUBLISHED" or not job.get("theorem_id"):
        raise RuntimeError(f"{spec['key']}: problem publication failed: {job.get('status')}")
    return job["theorem_id"]


def verify_one(api: API, spec: dict, theorem_id: str, proof: str, out: Path) -> dict:
    theorem = api.request("/theorems/" + theorem_id)
    save(out, spec["key"] + "-theorem-before-verify.json", theorem)
    if norm(theorem.get("formal_statement")) != norm(spec["formal"]):
        raise RuntimeError(f"{spec['key']}: server formal statement mismatch before verify")
    if theorem.get("status") == "Proved":
        return {"theorem_id": theorem_id, "status": "Proved", "verification": "SKIPPED_ALREADY_PROVED"}
    if theorem.get("status") != "Open":
        raise RuntimeError(f"{spec['key']}: unexpected theorem status {theorem.get('status')}")
    queued = api.verify(theorem_id, proof, spec["explanation"])
    save(out, spec["key"] + "-proof-queued.json", queued)
    sid = queued.get("submission_id")
    if not sid:
        raise RuntimeError(f"{spec['key']}: verification did not return submission_id")
    verdict = poll_verify(api, sid)
    save(out, spec["key"] + "-proof-verdict.json", verdict)
    final = api.request("/theorems/" + theorem_id)
    save(out, spec["key"] + "-theorem-final.json", final)
    if verdict.get("status") != "ACCEPTED" or final.get("status") != "Proved":
        raise RuntimeError(
            f"{spec['key']}: proof not accepted: verdict={verdict.get('status')} final={final.get('status')}"
        )
    return {
        "theorem_id": theorem_id,
        "submission_id": sid,
        "verdict": verdict.get("status"),
        "status": final.get("status"),
    }


def post_or_reuse_mission_comment(api: API, results: dict[str, dict], out: Path):
    existing = api.request(f"/missions/{MISSION_ID}/comments?limit=100&offset=0")
    save(out, "mission-comments-before.json", existing)
    prior = [c for c in existing.get("comments", []) if COMMENT_MARKER in (c.get("body_md") or "")]
    if prior:
        if len(prior) != 1:
            raise RuntimeError("multiple existing publication comments with marker")
        return prior[0]["id"]

    neutral = results["neutral"]
    defect = results["defect"]
    body = f"""<!-- {COMMENT_MARKER} -->
## Formal circuit rank-defect update

Two additional circuit-localization results are now kernel-checked and Prove2Me-verified:

1. [common-face neutral rank](p2m:theorem/{neutral['theorem_id']}): for a row-circuit displacement `v-u` based at a vertex, the ambient rows neutral on that direction have rank exactly `h-1` after restriction to the `h`-dimensional common-direction space.
2. [selected-row defect budget](p2m:theorem/{defect['theorem_id']}): for any selected set `F` of rows that remain nontrivial on the common face, `|F| + delta_F + d <= n+h`, where `delta_F` is the missing neutral rank relative to `h-1`.

The second theorem is the verified **row-presentation** core of the ordinary `(f-h)+delta <= n-d` defect accounting. What is still not formalized here is the geometric identification of `F` with one representative per genuine facet of the intrinsic common face. It also does not provide an edge route. Therefore the formal Open frontier remains [polynomial edge refinement of circuit walks](p2m:theorem/{FRONTIER_ID}); no new Open child or cyclic decomposition was created.

Verification provenance: GitHub commit `{SOURCE_COMMIT}`, Actions run `{SOURCE_RUN}`. Both standalone proofs independently compiled against only the public common-face/circuit definition modules and Mathlib, with only `propext`, `Classical.choice`, and `Quot.sound` reported.
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
    comments = api.request(f"/missions/{MISSION_ID}/comments?limit=100&offset=0")
    save(out, "mission-comments-readback.json", comments)
    matches = [c for c in comments.get("comments", []) if c.get("id") == cid]
    if len(matches) != 1:
        raise RuntimeError("mission comment not found on readback")
    refs = {(r.get("type"), r.get("id")) for r in matches[0].get("references", [])}
    expected = {
        ("theorem", neutral["theorem_id"]),
        ("theorem", defect["theorem_id"]),
        ("theorem", FRONTIER_ID),
    }
    if not expected.issubset(refs):
        raise RuntimeError(f"mission comment reference readback mismatch: {refs}")
    return cid


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--artifact-root", type=Path, required=True)
    p.add_argument("--out", type=Path, default=Path("prove2me_circuit_neutral_rank_defect_receipts"))
    args = p.parse_args()
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")

    proofs = validate_artifact(args.artifact_root)
    out = args.out
    summary = {
        "started_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "platform_expected": VERSION,
        "env": PIN,
        "source_commit": SOURCE_COMMIT,
        "source_run": SOURCE_RUN,
        "artifact_validation": "PASSED",
        "proof_sha256": {spec["key"]: spec["sha256"] for spec in SPECS},
    }
    save(out, "validation.json", summary)

    api = API(key)
    api.refresh()
    summary["platform_version"] = api.version
    ensure_public_dependencies(api, out)
    ensure_frontier_open(api, out, "before")

    results: dict[str, dict] = {}
    for spec in SPECS:
        tid = register_or_reuse(api, spec, out)
        results[spec["key"]] = verify_one(api, spec, tid, proofs[spec["key"]], out)

    ensure_frontier_open(api, out, "after")
    cid = post_or_reuse_mission_comment(api, results, out)
    summary.update(
        results=results,
        frontier_id=FRONTIER_ID,
        frontier_status="Open",
        mission_comment_id=cid,
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
            Path("prove2me_circuit_neutral_rank_defect_receipts"),
            "failure.json",
            {"error_type": type(exc).__name__, "error": str(exc)[:3000]},
        )
        raise
