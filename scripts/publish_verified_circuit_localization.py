#!/usr/bin/env python3
"""Publish two independently compiled structural circuit-localization theorems.

This publisher is intentionally fail-closed. It accepts only the artifact from
GitHub Actions run 34495410594 at source commit
9f964b8617fbbcae3cf652c130cbdbacd32b0dea, validates both standalone proof
hashes and axiom receipts, checks the public definition dependencies, then
collision-safely registers and verifies the exact public statements on
Prove2Me 0.9.9. It never modifies the Open Polynomial-Hirsch frontier theorem.
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
SOURCE_COMMIT = "9f964b8617fbbcae3cf652c130cbdbacd32b0dea"
SOURCE_RUN = "34495410594"
MISSION_ID = "6078cb2d-3594-44b1-a01a-fd452ddae274"
FRONTIER_ID = "099c6686-560c-48fc-b2c2-18b6a620a06e"

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
open Set Hirsch
"""

SPECS = [
    {
        "key": "localization",
        "name": "Hirsch.row_circuit_common_face_dimension_bound",
        "title": "Row-circuit endpoints lie in a small common face",
        "proof_file": "localization-solution.lean",
        "manifest_file": "localization-manifest.json",
        "log_file": "localization-standalone.log",
        "root_module": "Solutions.Sol_Hirsch_row_circuit_common_face_localization",
        "sha256": "6d3b6b7aecd9c483d30acdff94ff304afad8a8c45f6948b6c12aba1efc1ec009",
        "formal": r"""namespace Hirsch

theorem row_circuit_common_face_dimension_bound
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    2 * HirschCommonFace.commonFaceDim a b u v + d ≤ n + 1 := by sorry

end Hirsch""",
        "natural": (
            "Let u and v be vertices of an n-row H-polytope in ambient dimension d. "
            "If the displacement v-u is a support-minimal row circuit, then the face "
            "cut out by all nonzero describing rows tight at both endpoints has dimension h "
            "satisfying 2h+d <= n+1 (equivalently 2h <= n-d+1). No simplicity, "
            "irredundancy, strict-feasibility, or maximal-step assumption is required."
        ),
        "explanation": (
            "Partition the describing rows into source-only tight rows, target-only tight rows, "
            "and rows neutral on the circuit direction. Vertex extremality bounds the common-face "
            "dimension by each one-sided tight family. Support-minimality forces the neutral "
            "row family to have rank, hence cardinality, at least d-1. The three row families "
            "are disjoint, and summing their cardinalities gives the claimed inequality."
        ),
        "tags": ["polyhedra", "hirsch-conjecture", "circuits", "common-faces", "dimension"],
    },
    {
        "key": "balanced",
        "name": "Hirsch.balanced_row_circuit_vertices_share_tight_row",
        "title": "Balanced row-circuit vertices must share a tight row",
        "proof_file": "balanced-solution.lean",
        "manifest_file": "balanced-manifest.json",
        "log_file": "balanced-standalone.log",
        "root_module": "Solutions.Sol_Hirsch_balanced_row_circuit_vertices_share_tight_row",
        "sha256": "e9b2a0be5fde78404b9b3456a8936d1ff3fea93be27c4cff0d318d02e27fe4ce",
        "formal": r"""namespace Hirsch

theorem balanced_row_circuit_vertices_share_tight_row
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbal : n = 2 * d) (hd : 2 ≤ d)
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by sorry

end Hirsch""",
        "natural": (
            "In an exactly balanced n=2d H-presentation with d at least two, two vertices "
            "whose displacement is a support-minimal row circuit must share a nonzero "
            "describing row that is tight at both endpoints. Thus an estranged balanced "
            "vertex pair cannot be a single row-circuit step."
        ),
        "explanation": (
            "Assume no nonzero row is tight at both endpoints. Each extreme endpoint has at "
            "least d nonzero tight rows, and those source- and target-tight families are "
            "disjoint. A row circuit supplies at least d-1 rows neutral on its displacement; "
            "under the no-shared-row assumption that neutral family is disjoint from both "
            "endpoint-tight families. Their total cardinality therefore exceeds 2d when d>=2, "
            "contradicting n=2d."
        ),
        "tags": ["polyhedra", "hirsch-conjecture", "circuits", "balanced-polytopes", "obstruction"],
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
    source_log = locate(root, "source.log").read_text(encoding="utf-8")
    audit_axioms(source_log, label="source.log")
    results: dict[str, str] = {}
    for spec in SPECS:
        proof = locate(root, spec["proof_file"]).read_text(encoding="utf-8")
        manifest = json.loads(locate(root, spec["manifest_file"]).read_text(encoding="utf-8"))
        log = locate(root, spec["log_file"]).read_text(encoding="utf-8")
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
            raise RuntimeError(f"{spec['key']}: standalone proof contains forbidden declaration/token")
        if len(re.findall(r"(?m)^\s*theorem\s+solution\b", proof)) != 1:
            raise RuntimeError(f"{spec['key']}: standalone proof must contain exactly one theorem solution")
        audit_axioms(log, label=spec["log_file"])
        if "'solution' depends on axioms:" not in log and "'solution' does not depend on any axioms" not in log:
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
                    f"commit {SOURCE_COMMIT}, Actions run {SOURCE_RUN}. Related circuit-diameter "
                    "literature is background only; no novelty claim is made."
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


def post_mission_comment(api: API, results: dict[str, dict], out: Path):
    loc = results["localization"]
    bal = results["balanced"]
    body = f"""## Formal circuit-localization update

Two results from the recent circuit-localization research are now kernel-checked and Prove2Me-verified:

1. [row-circuit common-face dimension bound](p2m:theorem/{loc['theorem_id']}): for vertex endpoints with row-circuit displacement, `2*dim(F(u,v)) + d <= n+1`.
2. [balanced row-circuit vertices share a tight row](p2m:theorem/{bal['theorem_id']}): when `n=2d` and `d>=2`, a vertex-to-vertex row-circuit pair must share a nonzero tight row, so a balanced estranged pair cannot be one circuit step.

These are structural localization/obstruction lemmas, **not** an edge-refinement theorem. Restricting to the common face can still destroy circuit status after removing intrinsically redundant restricted rows, so the formal Open frontier remains [polynomial edge refinement of circuit walks](p2m:theorem/{FRONTIER_ID}). No new child or cyclic decomposition was created.

Verification provenance: GitHub commit `{SOURCE_COMMIT}`, Actions run `{SOURCE_RUN}`; both standalone proofs independently compiled with only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
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
    comments = api.request(f"/missions/{MISSION_ID}/comments?limit=20&offset=0")
    save(out, "mission-comments-readback.json", comments)
    matches = [c for c in comments.get("comments", []) if c.get("id") == cid]
    if len(matches) != 1:
        raise RuntimeError("mission comment not found on readback")
    refs = {(r.get("type"), r.get("id")) for r in matches[0].get("references", [])}
    expected = {
        ("theorem", loc["theorem_id"]),
        ("theorem", bal["theorem_id"]),
        ("theorem", FRONTIER_ID),
    }
    if not expected.issubset(refs):
        raise RuntimeError(f"mission comment reference readback mismatch: {refs}")
    return cid


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--artifact-root", type=Path, required=True)
    p.add_argument("--out", type=Path, default=Path("prove2me_circuit_localization_receipts"))
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
    cid = post_mission_comment(api, results, out)
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
            Path("prove2me_circuit_localization_receipts"),
            "failure.json",
            {"error_type": type(exc).__name__, "error": str(exc)[:3000]},
        )
        raise
