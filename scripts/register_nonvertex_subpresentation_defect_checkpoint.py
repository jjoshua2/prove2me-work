#!/usr/bin/env python3
"""Register the kernel-verified nonvertex common-carrier defect theorem on Prove2Me.

This publisher intentionally performs theorem registration + mission linkage only.
The repository proof is kernel-verified, but its current source imports unpublished
`Solutions/*` helpers that are not valid Prove2Me server imports.  Do not pretend
that local kernel verification is an ACCEPTED platform solution.
"""
from __future__ import annotations

import datetime
import json
import os
import re
import time
import urllib.parse
import urllib.request
from pathlib import Path

BASE = "https://prove2.me/api/v1"
VERSION = "0.10.1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
MISSION_NAME = "The Polynomial Hirsch Conjecture"
MISSION_ID = "6078cb2d-3594-44b1-a01a-fd452ddae274"
FRONTIER = "099c6686-560c-48fc-b2c2-18b6a620a06e"
THEOREM_NAME = "Hirsch.row_circuit_common_face_subpresentation_excess_defect_checkpoint"
SOURCE_COMMIT = "52b4ebdf3e1f76bd297c765a15b2d22dfc1650a9"
MERGE_COMMIT = "e6473584218dff70a0022a2f3133f1503fe53e15"
VERIFY_RUN = "34633224935"
VERIFY_JOB = "103374853296"
OUT = Path("nonvertex_subpresentation_defect_publication_receipts")

PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model
open scoped BigOperators RealInnerProductSpace
open Set Module Hirsch"""

FORMAL = """namespace Hirsch

theorem row_circuit_common_face_subpresentation_excess_defect_checkpoint
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (M : ℕ)
    (hsub : HirschCommonFace.CommonFaceHasSubpresentationAtMost a b x y M) :
    ∃ m : ℕ, m ≤ M ∧ ∃ e : Fin m ↪ Fin n,
      Hpoly
          (fun j => HirschCommonFace.commonFaceA a b x y (e j))
          (fun j => HirschCommonFace.commonFaceB a b x y (e j)) =
        Hpoly
          (HirschCommonFace.commonFaceA a b x y)
          (HirschCommonFace.commonFaceB a b x y) ∧
      let F : Finset (Fin n) :=
        (Finset.univ.map e) ∩ HirschCommonFace.commonFaceEffectiveRows a b x y
      HirschCommonFace.commonFaceDim a b x y ≤ F.card ∧
      F.card ≤ M ∧
      (F.card - HirschCommonFace.commonFaceDim a b x y) +
          ((HirschCommonFace.commonFaceDim a b x y - 1) -
            Module.finrank ℝ
              (((HirschCommonFace.rowEvalMap a
                (F ∩ Finset.univ.filter (fun i =>
                  a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0))).domRestrict
                (HirschCommonFace.commonDirection a b x y)).range)) ≤
        n - d := by sorry

end Hirsch"""

NATURAL = """Let P be a bounded n-row H-polyhedron in R^d. Fix any vertex z of P and any feasible checkpoint x. Suppose y-x is a row-circuit direction. If the canonical common carrier of x and y has an equivalent coordinate H-presentation using at most M original rows, then one can choose such a subpresentation whose effective selected-row set F has size between the carrier dimension h and M, while the presentation excess |F|-h plus the loss of selected neutral-row rank is at most the ambient row excess n-d. The checkpoint x need not be a vertex; the fixed vertex z is only a global rank reference and can be reused across every step of a circuit walk."""

SOURCE = (
    "Kernel-verified in jjoshua2/prove2me-work at source commit " + SOURCE_COMMIT
    + ", merged as " + MERGE_COMMIT
    + "; Lean 4.30.0 / Mathlib " + PIN
    + "; GitHub Actions run " + VERIFY_RUN + ", job " + VERIFY_JOB
    + ". Local proof currently imports unpublished repository helper modules, so theorem registration is separated from platform proof submission."
)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError("authenticated redirects disabled")


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.version = None
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode(),
            headers={"Content-Type": "application/json", "Accept": "application/json"},
            method="POST",
        )
        with self.opener.open(req, timeout=45) as response:
            data = json.load(response)
        self.token = data["access_token"]
        self.version = data.get("version")
        if self.version != VERSION:
            raise RuntimeError(f"platform version {self.version!r} differs from reviewed {VERSION!r}")

    def request(self, path: str, data=None, method: str = "GET"):
        if not path.startswith("/") or path.startswith("//") or "://" in path:
            raise ValueError("API-relative path required")
        if not self.token:
            self.refresh()
        body = None if data is None else json.dumps(data).encode()
        req = urllib.request.Request(
            BASE + path,
            data=body,
            headers={
                "Authorization": "Bearer " + self.token,
                "Content-Type": "application/json",
                "Accept": "application/json",
            },
            method=method,
        )
        with self.opener.open(req, timeout=120) as response:
            return json.load(response)


def save(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def norm(text: str | None) -> str:
    return re.sub(r"\s+", "", text or "")


def theorem_summary(t: dict) -> dict:
    return {k: t.get(k) for k in ("theorem_id", "theorem_name", "status", "mathlib_rev")}


def poll(api: API, path: str, terminal: set[str], receipt: Path, timeout: int):
    deadline = time.monotonic() + timeout
    while True:
        data = api.request(path)
        save(receipt, data)
        if data.get("status") in terminal:
            return data
        if time.monotonic() > deadline:
            raise TimeoutError(f"platform job still pending: {path}")
        time.sleep(5)


def existing_theorem(api: API):
    q = urllib.parse.urlencode({"env": PIN, "theorem_name": THEOREM_NAME, "limit": 50, "offset": 0})
    rows = api.request("/theorems?" + q).get("theorems", [])
    matches = [r for r in rows if r.get("theorem_name") == THEOREM_NAME]
    if len(matches) > 1:
        raise RuntimeError("ambiguous theorem-name collision")
    return api.request("/theorems/" + matches[0]["theorem_id"]) if matches else None


def register(api: API) -> tuple[dict, str]:
    theorem = existing_theorem(api)
    registration = "REUSED" if theorem else "PUBLISHED"
    if theorem is None:
        payload = {
            "env": PIN,
            "private": False,
            "problems": [{
                "theorem_name": THEOREM_NAME,
                "theorem_title": "Nonvertex circuit checkpoints obey the same common-carrier excess/defect budget",
                "formal_statement": FORMAL,
                "preamble": PREAMBLE,
                "natural_language_statement": NATURAL,
                "source": SOURCE,
                "tags": ["polyhedra", "circuit-walks", "formalization"],
            }],
        }
        save(OUT / "registration-request.json", payload)
        queued = api.request("/submit-problem", payload, "POST")
        save(OUT / "registration-queued.json", queued)
        if queued.get("errors") or len(queued.get("jobs", [])) != 1:
            raise RuntimeError("registration did not queue exactly one theorem")
        verdict = poll(api, "/publish-jobs/" + queued["jobs"][0]["job_id"],
                       {"PUBLISHED", "FAILED", "ERROR"},
                       OUT / "registration-verdict.json", 900)
        if verdict.get("status") != "PUBLISHED":
            raise RuntimeError("theorem registration failed")
        theorem = api.request("/theorems/" + verdict["theorem_id"])
    if theorem.get("mathlib_rev") != PIN:
        raise RuntimeError("live theorem Mathlib revision mismatch")
    if norm(theorem.get("formal_statement")) != norm(FORMAL):
        raise RuntimeError("live theorem formal statement mismatch")
    save(OUT / "theorem.json", theorem)
    return theorem, registration


def mission_comment(api: API, theorem: dict) -> dict:
    if theorem.get("status") not in {"Open", "Proved"}:
        raise RuntimeError("unexpected theorem status")
    offset = 0
    while True:
        page = api.request(f"/missions/{MISSION_ID}/comments?limit=100&offset={offset}")
        comments = page.get("comments", [])
        for comment in comments:
            if any(r.get("type") == "theorem" and r.get("id") == theorem["theorem_id"]
                   for r in comment.get("references", [])):
                save(OUT / "mission-comment.json", comment)
                return comment
        offset += len(comments)
        if not comments or len(comments) < 100:
            break
    body = (
        f"Registered [nonvertex common-carrier excess/defect theorem](p2m:theorem/{theorem['theorem_id']}): "
        "a bounded-parent row-circuit step starting at a merely feasible checkpoint obeys the same selected-row "
        "presentation-excess plus neutral-rank-defect budget <= n-d as the earlier vertex-source theorem, using "
        "one fixed parent vertex as a reusable rank reference. The exact statement has a repository Lean proof "
        f"that compiled and passed axiom audit in Actions run {VERIFY_RUN}; the platform theorem remains Open "
        "until that proof is repackaged without unpublished repository Solution imports. This closes checkpoint "
        "vertexhood as a mathematical localization gap; the remaining Polynomial Hirsch issue is amortizing "
        "high carrier excess along the ordered circuit construction."
    )
    comment = api.request(f"/missions/{MISSION_ID}/comments",
                          {"body_md": body, "tags": ["reference", "strategy"]}, "POST")
    save(OUT / "mission-comment.json", comment)
    refs = {(r.get("type"), r.get("id")) for r in comment.get("references", [])}
    if ("theorem", theorem["theorem_id"]) not in refs:
        raise RuntimeError("mission theorem reference did not resolve")
    return comment


def main() -> None:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY repository credential is absent")
    api = API(key)
    envs = api.request("/environments")
    save(OUT / "environments.json", envs)
    if not any(e.get("mathlib_rev") == PIN for e in envs.get("environments", [])):
        raise RuntimeError("pinned Mathlib environment unavailable")
    mission = api.request("/missions/" + MISSION_ID)
    save(OUT / "mission.json", mission)
    if mission.get("name") != MISSION_NAME:
        raise RuntimeError("mission identity mismatch")
    before = api.request("/theorems/" + FRONTIER)
    save(OUT / "frontier-before.json", theorem_summary(before))
    if before.get("status") != "Open":
        raise RuntimeError("edge-refinement frontier is not Open")
    theorem, registration = register(api)
    comment = mission_comment(api, theorem)
    after = api.request("/theorems/" + FRONTIER)
    save(OUT / "frontier-after.json", theorem_summary(after))
    if after.get("theorem_id") != before.get("theorem_id") or after.get("status") != "Open":
        raise RuntimeError("edge-refinement frontier changed unexpectedly")
    receipt = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform_version": api.version,
        "mathlib_rev": PIN,
        "registration": registration,
        "theorem": theorem_summary(theorem),
        "local_kernel_source_commit": SOURCE_COMMIT,
        "local_kernel_verify_run": VERIFY_RUN,
        "local_kernel_verify_job": VERIFY_JOB,
        "platform_proof_submitted": False,
        "platform_status_expected": "Open unless an equivalent proof already existed",
        "mission_id": mission["id"],
        "mission_comment_id": comment["id"],
        "frontier_before": theorem_summary(before),
        "frontier_after": theorem_summary(after),
        "frontier_graph_modified": False,
        "new_conjectural_children": 0,
    }
    save(OUT / "receipt.json", receipt)
    print(json.dumps(receipt, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
