#!/usr/bin/env python3
from __future__ import annotations
import json, os, urllib.parse
from submit_child_b_balanced_sketch import API, PIN

NAME = "Hirsch.dimension_three_bound"

def main() -> int:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)
    q = urllib.parse.urlencode({"env": PIN, "theorem_name": NAME, "limit": 20, "offset": 0})
    data = api.request("/theorems?" + q)
    rows = [x for x in data.get("theorems", []) if x.get("theorem_name") == NAME]
    compact = [{k: r.get(k) for k in ("theorem_id", "theorem_name", "theorem_title", "status", "mathlib_rev")} for r in rows]
    print(json.dumps({"platform_version": api.version, "matches": compact}, indent=2))
    return 0 if any(r.get("status") == "Proved" and r.get("mathlib_rev") == PIN for r in rows) else 2

if __name__ == "__main__":
    raise SystemExit(main())
