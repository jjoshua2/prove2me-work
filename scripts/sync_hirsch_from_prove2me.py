#!/usr/bin/env python3
"""Read live Polynomial Hirsch mission state from Prove2Me without mutating it.

Uses only repository secret PROVE2ME_API_KEY. Redirects are disabled. The output
contains no credentials and is intended to be inspected before any write-back.
"""
from __future__ import annotations

import datetime
import json
import os
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

BASE = "https://prove2.me/api/v1"
EXPECTED_VERSION = "0.10.1"
MISSION_NAME = "The Polynomial Hirsch Conjecture"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
OUT = Path("prove2me_hirsch_sync_readback")

KNOWN = {
    "frontier": "73beca40-31bc-42d5-8350-5ec9ac28bd3e",
    "parent_edge_refinement": "099c6686-560c-48fc-b2c2-18b6a620a06e",
    "normalized_two_moment_slice_diameter_two": "e93edd7b-4659-4df5-9eab-fbcce4352c78",
    "irredundant_row_count": "8538150b-8afe-47ad-94b0-d72189b80264",
    "maximal_step_common_face_bound": "bfea4b5b-106a-4e52-8297-b8138ca0a294",
    "row_circuit_step_swap_iff_tight_blockers": "bd9710b8-067a-4ce6-8ab9-1f6f763133b7",
    "cubic_circuit_walk_bound": "9b9a6f06-d05d-41ba-980f-04b905e67562",
}


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
        if self.version != EXPECTED_VERSION:
            raise RuntimeError(
                f"platform version {self.version!r} differs from reviewed {EXPECTED_VERSION!r}"
            )

    def request(self, path: str):
        if not path.startswith("/") or path.startswith("//") or "://" in path:
            raise ValueError("API-relative path required")
        if not self.token:
            self.refresh()
        req = urllib.request.Request(
            BASE + path,
            headers={"Authorization": "Bearer " + self.token, "Accept": "application/json"},
            method="GET",
        )
        with self.opener.open(req, timeout=120) as response:
            return json.load(response)

    def try_request(self, path: str):
        try:
            return {"ok": True, "data": self.request(path)}
        except urllib.error.HTTPError as e:
            body = e.read(4096).decode("utf-8", "replace")
            return {"ok": False, "status": e.code, "body": body}


def save(name: str, data) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / name).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def find_mission(api: API) -> dict:
    offset = 0
    matches = []
    while True:
        page = api.request("/missions?" + urllib.parse.urlencode({"limit": 100, "offset": offset}))
        rows = page.get("missions", [])
        matches.extend(x for x in rows if x.get("name") == MISSION_NAME)
        offset += len(rows)
        if not rows or offset >= int(page.get("total", offset)):
            break
    if len(matches) != 1:
        raise RuntimeError(f"expected one exact mission {MISSION_NAME!r}, found {len(matches)}")
    return matches[0]


def paged_comments(api: API, mission_id: str) -> list[dict]:
    out = []
    offset = 0
    while True:
        page = api.request(
            f"/missions/{mission_id}/comments?" + urllib.parse.urlencode({"limit": 100, "offset": offset})
        )
        rows = page.get("comments", [])
        out.extend(rows)
        offset += len(rows)
        total = int(page.get("total", offset))
        if not rows or offset >= total:
            break
    return out


def theorem_summary(t: dict) -> dict:
    return {
        k: t.get(k)
        for k in (
            "theorem_id", "theorem_name", "theorem_title", "status", "mathlib_rev",
            "created_at", "updated_at", "parent_id", "proof_sketch_id"
        )
    }


def main() -> None:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY repository credential is absent")
    api = API(key)

    envs = api.request("/environments")
    save("environments.json", envs)
    if not any(e.get("mathlib_rev") == PIN for e in envs.get("environments", [])):
        raise RuntimeError("pinned Mathlib environment is no longer available")

    mission = find_mission(api)
    mission_id = mission["id"]
    save("mission-list-entry.json", mission)

    # Read the canonical mission payload and collaboration thread.
    mission_detail = api.try_request(f"/missions/{mission_id}")
    comments = paged_comments(api, mission_id)
    save("mission-detail.json", mission_detail)
    save("comments.json", comments)

    # Probe read-only mission subresources used by current/newer platform versions.
    probes = {}
    for suffix in ("milestones", "theorems", "frontier", "graph"):
        probes[suffix] = api.try_request(f"/missions/{mission_id}/{suffix}")
    save("mission-subresource-probes.json", probes)

    theorem_states = {}
    for label, theorem_id in KNOWN.items():
        result = api.try_request("/theorems/" + theorem_id)
        if result.get("ok"):
            theorem_states[label] = theorem_summary(result["data"])
        else:
            theorem_states[label] = result
    save("known-theorems.json", theorem_states)

    summary = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform_version": api.version,
        "mathlib_rev": PIN,
        "mission": {
            "id": mission_id,
            "name": mission.get("name"),
            "status": mission.get("status"),
            "captain": mission.get("captain"),
        },
        "comment_count": len(comments),
        "latest_comments": [
            {
                "id": c.get("id"),
                "created_at": c.get("created_at"),
                "author": c.get("author") or c.get("user"),
                "body_md": c.get("body_md"),
                "references": c.get("references", []),
                "tags": c.get("tags", []),
            }
            for c in comments[-12:]
        ],
        "known_theorems": theorem_states,
        "available_subresources": [k for k, v in probes.items() if v.get("ok")],
    }
    save("summary.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
