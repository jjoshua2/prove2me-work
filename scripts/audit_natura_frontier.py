#!/usr/bin/env python3
"""Read-only Prove2Me audit of the just-proved Child A and remaining circuit frontier."""
from __future__ import annotations

import json
import os
from pathlib import Path
import urllib.parse

from submit_natura_child_a_standalone import API, TARGET_ID, TARGET_NAME, PIN

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "child_a_direct_evidence"
CHILD_B_ID = "33fc334e-e05b-4090-ac49-f83fd94d9305"


def write(name: str, value) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def safe(api: API, path: str):
    try:
        return api.request(path)
    except Exception as exc:
        return {"error_type": type(exc).__name__, "error": str(exc)[:500], "path": path}


def main() -> int:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)

    child_a = api.request("/theorems/" + TARGET_ID)
    accepted_a = safe(
        api,
        "/theorems/" + TARGET_ID + "/submissions?" +
        urllib.parse.urlencode({"status": "ACCEPTED", "first": "true"}),
    )
    child_b = api.request("/theorems/" + CHILD_B_ID)
    b_decompositions = safe(api, "/theorems/" + CHILD_B_ID + "/decompositions")
    b_open_leaves = safe(api, "/theorems/" + CHILD_B_ID + "/open-leaves")
    b_graph = safe(api, "/theorems/" + CHILD_B_ID + "/graph")

    q = urllib.parse.urlencode({"env": PIN, "q": "Hirsch", "limit": 200, "offset": 0})
    related = safe(api, "/theorems?" + q)

    write("child-a-full.json", child_a)
    write("child-a-accepted-submission.json", accepted_a)
    write("child-b-full.json", child_b)
    write("child-b-decompositions.json", b_decompositions)
    write("child-b-open-leaves.json", b_open_leaves)
    write("child-b-graph.json", b_graph)
    write("hirsch-related.json", related)

    summary = {
        "platform_version": api.version,
        "child_a": {
            "theorem_id": child_a.get("theorem_id"),
            "theorem_name": child_a.get("theorem_name"),
            "status": child_a.get("status"),
            "mathlib_rev": child_a.get("mathlib_rev"),
        },
        "child_b": {
            "theorem_id": child_b.get("theorem_id"),
            "theorem_name": child_b.get("theorem_name"),
            "status": child_b.get("status"),
            "mathlib_rev": child_b.get("mathlib_rev"),
        },
        "accepted_a_shape": list(accepted_a.keys()) if isinstance(accepted_a, dict) else type(accepted_a).__name__,
        "open_leaves_b_shape": list(b_open_leaves.keys()) if isinstance(b_open_leaves, dict) else type(b_open_leaves).__name__,
    }
    write("frontier-summary.json", summary)
    print(json.dumps(summary, indent=2))
    if child_a.get("theorem_name") != TARGET_NAME or child_a.get("status") != "Proved":
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
