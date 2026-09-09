#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE_SCRIPT = ROOT / "_publisher_source/scripts/publish_public_geodesic_face_cover.py"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PREAMBLE = """import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
"""

PUBLICATIONS = [
    {
        "label": "vertex_selection",
        "wrapper": "Solutions/Sol_Hirsch_face_preserving_vertex_selection.lean",
        "packet": "public_checkpoint_vertex_selection_packet",
        "out": "checkpoint_vertex_selection_publish_receipts",
        "name": "Hirsch.face_preserving_vertex_selection",
        "short_name": "face_preserving_vertex_selection",
        "title": "Simultaneous face-preserving rounding to parent vertices",
        "natural": (
            "Let P be a compact Euclidean polytope and let F_i be any family of closed extreme "
            "subsets of P. There is one selection r sending every feasible point of P to a parent "
            "vertex, fixing every existing parent vertex, such that membership in every supplied "
            "face is preserved simultaneously: x in F_i implies r(x) in F_i. The family of faces "
            "need not be finite; no continuity or adjacency preservation is asserted."
        ),
        "explanation": (
            "For a feasible point x, intersect P with every closed extreme face F_i that contains x. "
            "This intersection is nonempty (it contains x), closed, compact, and extreme in P. "
            "Krein-Milman supplies an extreme point of the intersection, which is also an extreme "
            "point of P. Choose such a point for nonvertices and leave existing parent vertices fixed. "
            "The resulting choice preserves all supplied face memberships simultaneously."
        ),
        "tags": ["polyhedra", "hirsch-conjecture", "extreme-faces", "path-repair"],
    },
    {
        "label": "feasible_start_containment",
        "wrapper": "Solutions/Sol_Hirsch_feasible_start_containment_route_bound.lean",
        "packet": "public_checkpoint_feasible_start_containment_packet",
        "out": "checkpoint_feasible_start_publish_receipts",
        "name": "Hirsch.face_interval_cover_route_bound_of_feasible_start_containment",
        "short_name": "face_interval_cover_route_bound_of_feasible_start_containment",
        "title": "Start-containment routing with nonvertex marked checkpoints",
        "natural": (
            "For a finite interval cover by closed extreme faces of a compact parent, the marked "
            "interval endpoints need not themselves be vertices. If the two global endpoints are "
            "parent vertices, every interval endpoint lies in its supporting face, every old step is "
            "covered, and every later interval start occurring while an earlier interval is active "
            "lies in the earlier face, then the endpoints are joined by a parent edge/stay walk whose "
            "length is at most the sum of the intrinsic face-diameter budgets."
        ),
        "explanation": (
            "Use the simultaneous face-preserving vertex selector to round every marked checkpoint "
            "to a parent vertex while preserving every closed-face incidence and fixing the two "
            "global endpoint vertices. The start-containment hypotheses therefore remain true after "
            "rounding. Apply the already verified start-containment interval-routing theorem to the "
            "rounded checkpoints; its route has total budget equal to the sum of the face budgets."
        ),
        "tags": ["polyhedra", "graph-diameter", "hirsch-conjecture", "path-repair", "intervals"],
    },
]


def load_base(tag: str):
    spec = importlib.util.spec_from_file_location(f"basepub_{tag}", BASE_SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def signature(wrapper: Path) -> str:
    text = wrapper.read_text(encoding="utf-8")
    return "theorem solution" + text.split("theorem solution", 1)[1].split(" := by", 1)[0]


def publish(item: dict) -> dict:
    pub = load_base(item["label"])
    pub.ROOT = ROOT
    pub.OUT = ROOT / item["out"]
    pub.NAME = item["name"]
    pub.PREAMBLE = PREAMBLE
    sig = signature(ROOT / item["wrapper"])
    pub.FORMAL = (
        "namespace Hirsch\n\n"
        + sig.replace("theorem solution", f"theorem {item['short_name']}", 1)
        + " := by sorry\n\nend Hirsch"
    )
    orig_request = pub.API.request

    def request(self, path, data=None, method="GET", content_type="application/json"):
        if path == "/submit-problem" and data:
            p = data["problems"][0]
            p["theorem_title"] = item["title"]
            p["natural_language_statement"] = item["natural"]
            p["source"] = "Verified Lean theorem from jjoshua2/prove2me-work PR #50."
            p["tags"] = item["tags"]
        return orig_request(self, path, data, method, content_type)

    pub.API.request = request
    orig_verify = pub.API.verify

    def verify(self, tid, proof, explanation):
        return orig_verify(self, tid, proof, item["explanation"])

    pub.API.verify = verify
    shared = ROOT / "public_geodesic_face_cover_packet"
    shared.mkdir(exist_ok=True)
    (shared / "solution.lean").write_text(
        (ROOT / item["packet"] / "solution.lean").read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    rc = pub.main()
    if rc != 0:
        raise RuntimeError(f"publisher returned {rc} for {item['name']}")
    status = json.loads((pub.OUT / "status.json").read_text(encoding="utf-8"))
    if status.get("status") != "Proved":
        raise RuntimeError(f"publication did not end Proved: {status}")
    return status


def update_mission_discussion(results: list[dict]) -> dict:
    # Reuse the publisher's redacted authenticated API client. This creates one
    # research-status comment; it does not create any Open theorem children.
    pub = load_base("mission_comment")
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = pub.API(key)
    missions = api.request("/missions?limit=100&offset=0").get("missions", [])
    matches = [m for m in missions if m.get("name") == "The Polynomial Hirsch Conjecture"]
    if len(matches) != 1:
        raise RuntimeError(f"expected one Polynomial Hirsch mission, got {len(matches)}")
    mission_id = matches[0]["id"]
    selector_id = results[0]["theorem_id"]
    routing_id = results[1]["theorem_id"]
    body = f"""PR #50 geometric continuation is verified and two completed results are now public:

- [simultaneous face-preserving vertex selection](p2m:theorem/{selector_id}): any feasible checkpoint in a compact parent can be rounded to a parent vertex while preserving **all** memberships in an arbitrary family of closed extreme faces; existing vertices can be fixed.
- [start-containment routing with nonvertex marked checkpoints](p2m:theorem/{routing_id}): PR #49's interval-routing bound still holds when marked intermediate checkpoints are nonvertices; only the two global endpoints must initially be vertices.

The same PR also kernel-verifies nine radial-clipping algebra lemmas and gives an exact fixed-parent construction for simultaneous monotone clipping. With a strictly feasible common centre, radial projection of an outer edge walk into the final polytope decomposes into final cut-face pieces and clipped old-edge pieces; the ordinary mathematical argument gives repair cost `L + sum_i B_i`. Exact tests cover 48 multi-cut instances / 694 affine cells and a genuine moving-facet intersection-loss example.

**Formal boundary:** the full simultaneous-clipping `L + sum B_i` theorem is not yet one end-to-end Lean declaration, so it has **not** been registered as Proved. The remaining formal assembly is finite breakpoint-to-face-cover extraction plus the clipped-old-edge diameter-one step. The deeper research gaps remain (1) obtaining the required outer-edge/clipping model from the desired global circuit/projective construction and (2) polynomial control of total final-face cost `sum_i B_i`. `Hirsch.polynomial_edge_refinement_of_circuit_walks` remains Open. No new Open children were created."""
    comment = api.request(
        f"/missions/{mission_id}/comments",
        {"body_md": body, "tags": ["strategy", "reference", "attempt"]},
        "POST",
    )
    out = ROOT / "checkpoint_mission_update_receipts"
    out.mkdir(exist_ok=True)
    (out / "mission-comment.json").write_text(json.dumps(comment, indent=2) + "\n", encoding="utf-8")
    return comment


def main() -> None:
    results = [publish(item) for item in PUBLICATIONS]
    comment = update_mission_discussion(results)
    summary = {"publications": results, "mission_comment_id": comment.get("id")}
    out = ROOT / "checkpoint_publication_summary.json"
    out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
