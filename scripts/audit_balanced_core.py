#!/usr/bin/env python3
"""Read-only audit of the live balanced Polynomial Hirsch core and its frontier."""
from __future__ import annotations

import json
import os
from pathlib import Path
import urllib.parse

from submit_child_b_balanced_sketch import API, PIN, safe

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "balanced_core_evidence"
BALANCED_ID = "cdb2b059-17b6-4c73-8740-caca090314d7"
NAMES = [
    "Hirsch.balanced_polynomial_bound",
    "Hirsch.balanced_hpoly_transfer",
    "Hirsch.polynomial_target_face_access",
    "Hirsch.diameter_bound_of_target_face_access",
    "Hirsch.polynomial_access_to_given_supporting_face",
    "Hirsch.polynomial_edge_refinement_of_circuit_walks",
    "Hirsch.polynomial_hirsch_conjecture",
]


def write(name: str, value) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def rows(api: API, theorem_name: str):
    q = urllib.parse.urlencode({
        "env": PIN,
        "theorem_name": theorem_name,
        "limit": 20,
        "offset": 0,
    })
    data = api.request("/theorems?" + q)
    return [x for x in data.get("theorems", []) if x.get("theorem_name") == theorem_name]


def compact(item):
    if not isinstance(item, dict):
        return item
    return {k: item.get(k) for k in (
        "theorem_id", "theorem_name", "theorem_title", "status", "mathlib_rev",
        "created_at", "deprecated_at", "deprecated_by",
    )}


def main() -> int:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)

    balanced = api.request("/theorems/" + BALANCED_ID)
    decompositions = safe(api, "/theorems/" + BALANCED_ID + "/decompositions")
    open_leaves = safe(api, "/theorems/" + BALANCED_ID + "/open-leaves")
    graph = safe(api, "/theorems/" + BALANCED_ID + "/graph")
    submissions = safe(api, "/theorems/" + BALANCED_ID + "/submissions")

    write("balanced.json", balanced)
    write("decompositions.json", decompositions)
    write("open-leaves.json", open_leaves)
    write("graph.json", graph)
    write("submissions.json", submissions)

    named = {}
    for name in NAMES:
        matches = rows(api, name)
        named[name] = [compact(x) for x in matches]
    write("named-theorems.json", named)

    summary = {
        "platform_version": api.version,
        "balanced": compact(balanced),
        "decomposition_count": len(decompositions.get("decompositions", [])) if isinstance(decompositions, dict) else None,
        "open_leaf_count": open_leaves.get("total") if isinstance(open_leaves, dict) else None,
        "open_leaves": [compact(x) for x in open_leaves.get("open_leaves", [])] if isinstance(open_leaves, dict) else open_leaves,
        "named": named,
    }
    write("summary.json", summary)
    print(json.dumps(summary, indent=2))
    return 0 if balanced.get("theorem_name") == "Hirsch.balanced_polynomial_bound" and balanced.get("status") == "Open" else 2


if __name__ == "__main__":
    raise SystemExit(main())
