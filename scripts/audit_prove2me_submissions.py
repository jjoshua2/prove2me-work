#!/usr/bin/env python3
"""Audit publishable results from prove2me-work PRs against live Prove2Me.

Read-only. Never prints the API key or bearer token.
"""
from __future__ import annotations

import json
import os
import sys
import time
import urllib.parse
import urllib.request
from dataclasses import dataclass
from typing import Any

BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PARENT_ID = "33fc334e-e05b-4090-ac49-f83fd94d9305"


@dataclass(frozen=True)
class Candidate:
    pr: int
    name: str
    kind: str
    expected: str
    note: str = ""


CANDIDATES = [
    Candidate(2, "Hirsch.target_face_access_of_local_neutral_rank", "theorem", "Proved"),
    Candidate(3, "Hirsch.given_supporting_face_access_of_boundary_residual_rank", "theorem", "Proved"),
    Candidate(3, "Hirsch.vertex_exposing_redundant_row_extension", "theorem", "Proved"),
    Candidate(4, "Hirsch.given_supporting_face_access_of_boundary_product_factors", "theorem", "Proved"),
    Candidate(5, "Hirsch.cut_face_access_of_outer_diameter", "theorem", "Proved"),
    Candidate(6, "Hirsch.clipped_diameter_le_outer_add_cut_face", "theorem", "Proved"),
    Candidate(7, "Hirsch.cut_face_access_of_unbounded_outer_diameter", "theorem", "Proved"),
    Candidate(7, "Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one", "theorem", "Proved"),
    Candidate(8, "Hirsch.box_slice_diameter_le_dimension", "theorem", "Proved"),
    Candidate(9, "Hirsch_circuit_model", "definition", "Definition"),
    Candidate(9, "Hirsch.cubic_circuit_walk_bound", "theorem", "Open", "intended sketch child"),
    Candidate(9, "Hirsch.polynomial_edge_refinement_of_circuit_walks", "theorem", "Open", "intended sketch child"),
]

# PR #1 was superseded by the completed Santos chain. These are checked as
# coverage, not counted as missing PR publications.
CHAIN = [
    "Hirsch.five_spindle_length_six",
    "Hirsch.spindle_normalize",
    "Hirsch.spindle_one_step_axis",
    "Hirsch.spindle_one_step_from_apex_facet",
    "Hirsch.spindle_one_step",
    "Hirsch.strong_dstep_spindle",
    "Hirsch.santos_counterexample",
]

# This proof was completed in PR #9 but was not part of its publication packet.
AUXILIARY = ["HirschCircuit.exists_irredundant_strict_model"]


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""

    def json(self, method: str, path: str, payload: dict[str, Any] | None = None) -> dict[str, Any]:
        if not path.startswith("/"):
            raise ValueError(path)
        data = None if payload is None else json.dumps(payload).encode()
        headers = {"Accept": "application/json", "User-Agent": "prove2me-submission-audit/1"}
        if payload is not None:
            headers["Content-Type"] = "application/json"
        if self.token:
            headers["Authorization"] = "Bearer " + self.token
        req = urllib.request.Request(BASE + path, data=data, headers=headers, method=method)
        with urllib.request.urlopen(req, timeout=45) as r:
            out = json.load(r)
        if not isinstance(out, dict):
            raise RuntimeError("unexpected response shape for " + path)
        return out

    def refresh(self) -> None:
        out = self.json("POST", "/agent/refresh", {"api_key": self.key})
        token = out.get("access_token")
        if not isinstance(token, str) or not token:
            raise RuntimeError("refresh returned no token")
        self.token = token
        print("AUTH ok version=" + str(out.get("version", "unknown")))


def all_publish_jobs(api: API) -> list[dict[str, Any]]:
    jobs: list[dict[str, Any]] = []
    offset = 0
    while True:
        page = api.json("GET", "/publish-jobs?" + urllib.parse.urlencode({"limit": 100, "offset": offset}))
        rows = page.get("jobs", page.get("publish_jobs", []))
        if not isinstance(rows, list):
            break
        jobs.extend(x for x in rows if isinstance(x, dict))
        if len(rows) < 100:
            break
        offset += len(rows)
        if offset > 5000:
            break
    return jobs


def find_exact(api: API, name: str) -> list[dict[str, Any]]:
    query = urllib.parse.urlencode({"env": PIN, "theorem_name": name, "limit": 200, "offset": 0})
    out = api.json("GET", "/theorems?" + query)
    rows = out.get("theorems", [])
    if not isinstance(rows, list):
        return []
    return [r for r in rows if isinstance(r, dict) and r.get("theorem_name") == name and r.get("mathlib_rev") == PIN]


def theorem_submissions(api: API, theorem_id: str) -> list[dict[str, Any]]:
    try:
        out = api.json("GET", f"/theorems/{theorem_id}/submissions?limit=100")
    except Exception as exc:
        return [{"audit_error": type(exc).__name__}]
    rows = out.get("submissions", [])
    return [r for r in rows if isinstance(r, dict)] if isinstance(rows, list) else []


def job_attempts(jobs: list[dict[str, Any]], name: str) -> list[dict[str, Any]]:
    found = []
    for j in jobs:
        if j.get("theorem_name") == name or j.get("definition_name") == name or j.get("name") == name:
            found.append({
                "id": j.get("id") or j.get("job_id"),
                "kind": j.get("kind"),
                "status": j.get("status"),
                "error_message": j.get("error_message", ""),
                "theorem_id": j.get("theorem_id"),
            })
    return found


def summarize_candidate(api: API, jobs: list[dict[str, Any]], c: Candidate) -> dict[str, Any]:
    rows = find_exact(api, c.name)
    result: dict[str, Any] = {
        "pr": c.pr,
        "name": c.name,
        "kind": c.kind,
        "expected": c.expected,
        "note": c.note,
        "found": bool(rows),
        "publish_attempts": job_attempts(jobs, c.name),
    }
    if len(rows) == 1:
        row = rows[0]
        tid = row.get("theorem_id") or row.get("id")
        result.update({
            "theorem_id": tid,
            "status": row.get("status"),
            "title": row.get("theorem_title"),
        })
        if c.kind == "theorem" and isinstance(tid, str):
            subs = theorem_submissions(api, tid)
            result["submissions"] = [
                {
                    "id": s.get("id") or s.get("submission_id"),
                    "status": s.get("status"),
                    "created_at": s.get("created_at"),
                }
                for s in subs
            ]
    elif len(rows) > 1:
        result["duplicate_matches"] = [r.get("theorem_id") or r.get("id") for r in rows]
    return result


def main() -> int:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        print("ERROR no PROVE2ME_API_KEY", file=sys.stderr)
        return 2
    api = API(key)
    api.refresh()
    jobs = all_publish_jobs(api)
    print(f"PUBLISH_JOBS fetched={len(jobs)}")

    candidates = [summarize_candidate(api, jobs, c) for c in CANDIDATES]

    parent = api.json("GET", f"/theorems/{PARENT_ID}")
    decomps = api.json("GET", f"/theorems/{PARENT_ID}/decompositions")
    parent_subs = theorem_submissions(api, PARENT_ID)
    decomp_rows = decomps.get("decompositions", [])
    child_sets = []
    if isinstance(decomp_rows, list):
        for d in decomp_rows:
            if not isinstance(d, dict):
                continue
            children = d.get("children", [])
            names = []
            if isinstance(children, list):
                for ch in children:
                    if isinstance(ch, dict):
                        names.append(ch.get("theorem_name") or ch.get("definition_name"))
            child_sets.append({"submission_id": d.get("submission_id"), "children": names})

    wanted_children = {
        "Hirsch.cubic_circuit_walk_bound",
        "Hirsch.polynomial_edge_refinement_of_circuit_walks",
        "Hirsch_circuit_model",
    }
    pr9_sketch_found = any(wanted_children.issubset(set(x["children"])) for x in child_sets)

    chain = []
    for name in CHAIN:
        rows = find_exact(api, name)
        chain.append({"name": name, "found": bool(rows), "status": rows[0].get("status") if len(rows) == 1 else None})

    auxiliary = []
    for name in AUXILIARY:
        rows = find_exact(api, name)
        auxiliary.append({"name": name, "found": bool(rows), "status": rows[0].get("status") if len(rows) == 1 else None})

    report = {
        "env": PIN,
        "generated_at": int(time.time()),
        "candidates": candidates,
        "pr9_parent": {
            "theorem_id": PARENT_ID,
            "name": parent.get("theorem_name"),
            "status": parent.get("status"),
            "matching_sketch_found": pr9_sketch_found,
            "decompositions": child_sets,
            "submissions": [
                {"id": s.get("id") or s.get("submission_id"), "status": s.get("status"), "created_at": s.get("created_at")}
                for s in parent_subs
            ],
        },
        "pr1_santos_chain": chain,
        "pr9_auxiliary_not_in_packet": auxiliary,
    }

    missing = []
    for c, r in zip(CANDIDATES, candidates):
        if not r["found"]:
            missing.append({"pr": c.pr, "name": c.name, "reason": "not published"})
        elif r.get("status") != c.expected:
            missing.append({"pr": c.pr, "name": c.name, "reason": f"status={r.get('status')} expected={c.expected}"})
    if not pr9_sketch_found:
        missing.append({"pr": 9, "name": "parent sketch for Hirsch.polynomial_access_to_given_supporting_face", "reason": "matching decomposition not found"})

    report["missing_or_incomplete"] = missing
    print("\n=== AUDIT JSON ===")
    print(json.dumps(report, indent=2, sort_keys=True))
    print("\n=== MISSING / INCOMPLETE ===")
    if missing:
        for x in missing:
            print(f"PR #{x['pr']}: {x['name']} -- {x['reason']}")
    else:
        print("none")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
