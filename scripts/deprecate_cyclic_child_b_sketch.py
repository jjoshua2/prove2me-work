#!/usr/bin/env python3
"""Retire the cyclic Child-B -> balanced-core sketch after graph audit."""
from __future__ import annotations

import json
import os
from pathlib import Path

from submit_child_b_balanced_sketch import API, safe

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "cyclic_sketch_retirement_evidence"
SUBMISSION_ID = "128604d3-6125-4f1e-8cad-3e64a908d346"
TARGET_ID = "099c6686-560c-48fc-b2c2-18b6a620a06e"
BALANCED_ID = "cdb2b059-17b6-4c73-8740-caca090314d7"


def write(name: str, value) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def find_decomp(decomps):
    if not isinstance(decomps, dict):
        return None
    for item in decomps.get("decompositions", []):
        if item.get("submission_id") == SUBMISSION_ID:
            return item
    return None


def main() -> int:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)

    before = api.request("/theorems/" + TARGET_ID + "/decompositions")
    cycle = find_decomp(before)
    write("before-decompositions.json", before)
    if cycle is None:
        raise RuntimeError("cyclic submission decomposition not found")
    child_ids = {c.get("theorem_id") for c in cycle.get("children", []) if isinstance(c, dict)}
    if BALANCED_ID not in child_ids:
        raise RuntimeError("submission no longer points to balanced core; refusing to mutate")

    # Reversible retirement of exactly this sketch submission.
    patched = api.request(
        "/submissions/" + SUBMISSION_ID,
        {"deprecated": True},
        method="PATCH",
    )
    write("patch-response.json", patched)

    after = api.request("/theorems/" + TARGET_ID + "/decompositions")
    graph = api.request("/theorems/" + BALANCED_ID + "/graph")
    write("after-decompositions.json", after)
    write("balanced-graph-after.json", graph)

    retired = find_decomp(after)
    if retired is None or not retired.get("deprecated_at"):
        raise RuntimeError("submission was not marked deprecated in decomposition readback")

    edges = graph.get("edges", []) if isinstance(graph, dict) else []
    sketch_node = "sketch-" + SUBMISSION_ID
    active_edges = [e for e in edges if e.get("source") == sketch_node or e.get("target") == sketch_node]
    result = {
        "submission_id": SUBMISSION_ID,
        "deprecated_at": retired.get("deprecated_at"),
        "deprecated_by": retired.get("deprecated_by"),
        "balanced_graph_has_hidden_deprecated_sketches": graph.get("has_hidden_deprecated_sketches") if isinstance(graph, dict) else None,
        "visible_edges_touching_retired_sketch": active_edges,
        "platform_version": api.version,
    }
    write("result.json", result)
    print(json.dumps(result, indent=2))
    return 0 if not active_edges else 2


if __name__ == "__main__":
    raise SystemExit(main())
