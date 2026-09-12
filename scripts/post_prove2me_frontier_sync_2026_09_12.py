#!/usr/bin/env python3
"""Post one authenticated Polynomial-Hirsch frontier sync comment to Prove2Me.

This client is intentionally narrow.  It reads the repository API key only from
the environment, refreshes a short-lived bearer token, verifies the known
public anchors and open frontier, posts/reuses one idempotently-marked mission
comment, and stores redacted JSON receipts.  It never prints credentials.
"""
from __future__ import annotations

import datetime
import json
import os
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

BASE = "https://prove2.me/api/v1"
VERSION = "0.10.3"
MISSION_ID = "6078cb2d-3594-44b1-a01a-fd452ddae274"
FRONTIER = "73beca40-31bc-42d5-8350-5ec9ac28bd3e"
TARGET_TIGHT = "aa3abbb2-203b-41ab-86b6-f45ab734c57a"
SLACK_ROWS = "804b7a8e-0572-4407-a014-2d9f4aaa6f87"
MARKER = "<!-- prove2me-work-frontier-sync-2026-09-12-pr186 -->"
OUT = Path("prove2me_frontier_sync_receipts")


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args: Any, **kwargs: Any):
        raise RuntimeError("authenticated redirects disabled")


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.version: str | None = None
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode("utf-8"),
            headers={"Content-Type": "application/json", "Accept": "application/json"},
            method="POST",
        )
        with self.opener.open(req, timeout=45) as response:
            data = json.load(response)
        token = data.get("access_token")
        if not isinstance(token, str) or not token:
            raise RuntimeError("refresh returned no access token")
        self.token = token
        self.version = data.get("version") if isinstance(data.get("version"), str) else None
        if self.version != VERSION:
            raise RuntimeError(
                f"platform version {self.version!r} differs from reviewed {VERSION!r}"
            )

    def request(self, path: str, data: Any = None, method: str = "GET") -> dict[str, Any]:
        if not path.startswith("/") or path.startswith("//") or "://" in path:
            raise ValueError("API-relative path required")
        if not self.token:
            self.refresh()
        body = None if data is None else json.dumps(data).encode("utf-8")
        req = urllib.request.Request(
            BASE + path,
            data=body,
            headers={
                "Authorization": "Bearer " + self.token,
                "Content-Type": "application/json",
                "Accept": "application/json",
                "User-Agent": "prove2me-work-frontier-sync/1",
            },
            method=method,
        )
        try:
            with self.opener.open(req, timeout=120) as response:
                value = json.load(response)
        except urllib.error.HTTPError as exc:
            # Do not echo response bodies from authenticated endpoints.
            raise RuntimeError(f"HTTP {exc.code} from {path}") from exc
        if not isinstance(value, dict):
            raise RuntimeError(f"unexpected JSON shape from {path}")
        return value


def save(name: str, value: Any) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def theorem_summary(t: dict[str, Any]) -> dict[str, Any]:
    return {k: t.get(k) for k in ("theorem_id", "theorem_name", "status", "mathlib_rev")}


def body(frontier: dict[str, Any]) -> str:
    return f"""{MARKER}
Frontier sync after the 2026-09-12 target-cone / portal-pair work.

Public anchors remain [the target-tight singleton-vertex outer](p2m:theorem/{TARGET_TIGHT}) and [the sharp vertex slack-row bound](p2m:theorem/{SLACK_ROWS}).  The GitHub kernel-verified chain has now advanced past support counting:

- simultaneous target-cone reinsertion exposes the **actual used cut legs**, including each parent-extreme entry/exit pair, and charges `D + sum B(row, entry, exit)` rather than every available cut face;
- target-rooted repair localizes all nontrivial cut-face cost to the endpoint-lift spoke;
- fixed-row radial active cells are convex, so along a segment one row cannot leave the radial upper envelope and later re-enter;
- new verified PR #186 proves a genuine recursive resource inequality: if `J` is a set of ambient rows strictly slack at **every point** of an actual portal-pair common carrier, then `(M_min - h) + |J| <= n - d`.  Thus strict unused rows directly reduce that carrier's minimum presentation excess.

The next concrete target is to choose a shortest/chordless path in the full mixed repair-region graph and formalize that nonneighboring used cut faces are disjoint.  Their rows are then strict throughout each current cut-leg carrier, so the new PR #186 theorem converts long used support into smaller local recursive excess.  In the maximum-support case this should force every local cut-leg carrier into the already-Proved/verified excess-at-most-three routing regime.

This is **not** a Polynomial Hirsch proof.  [The d>=4 circuit-to-edge refinement frontier](p2m:theorem/{FRONTIER}) is still recorded `{frontier.get('status')}`.  The remaining issue is to close the few-used-cuts / high-local-excess cases with a globally amortized ordinary-edge budget rather than multiplying recursive costs.
"""


def main() -> None:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key or not key.startswith("p2m_"):
        raise RuntimeError("PROVE2ME_API_KEY repository credential is absent or malformed")

    api = API(key)
    frontier_before = api.request("/theorems/" + FRONTIER)
    target_tight = api.request("/theorems/" + TARGET_TIGHT)
    slack_rows = api.request("/theorems/" + SLACK_ROWS)
    save("frontier-before.json", theorem_summary(frontier_before))
    save("target-tight.json", theorem_summary(target_tight))
    save("slack-rows.json", theorem_summary(slack_rows))

    if frontier_before.get("status") != "Open":
        raise RuntimeError("edge-refinement frontier is no longer Open; manual re-audit required")
    if target_tight.get("status") != "Proved" or slack_rows.get("status") != "Proved":
        raise RuntimeError("one of the public target-anchored anchors is no longer Proved")

    existing = api.request(f"/missions/{MISSION_ID}/comments?limit=100&offset=0")
    comment = None
    for row in existing.get("comments", []):
        if isinstance(row, dict) and MARKER in str(row.get("body_md", "")):
            comment = row
            break

    if comment is None:
        comment = api.request(
            f"/missions/{MISSION_ID}/comments",
            {"body_md": body(frontier_before), "tags": ["strategy", "reference"]},
            "POST",
        )
    save("mission-comment.json", comment)

    refs = {(r.get("type"), r.get("id")) for r in comment.get("references", [])}
    required = {
        ("theorem", TARGET_TIGHT),
        ("theorem", SLACK_ROWS),
        ("theorem", FRONTIER),
    }
    if not required.issubset(refs):
        raise RuntimeError("mission comment did not resolve every required theorem reference")

    frontier_after = api.request("/theorems/" + FRONTIER)
    save("frontier-after.json", theorem_summary(frontier_after))
    if frontier_after.get("status") != "Open":
        raise RuntimeError("frontier changed unexpectedly during discussion sync")

    receipt = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform_version": api.version,
        "mission_id": MISSION_ID,
        "mission_comment_id": comment.get("id"),
        "frontier_before": theorem_summary(frontier_before),
        "frontier_after": theorem_summary(frontier_after),
        "public_anchors": [theorem_summary(target_tight), theorem_summary(slack_rows)],
        "github_verified_through_pr": 186,
        "github_verification_run": 34697559250,
        "frontier_graph_modified": False,
        "new_conjectural_children": 0,
    }
    save("receipt.json", receipt)
    print(
        json.dumps(
            {
                "platform_version": api.version,
                "mission_comment_id": comment.get("id"),
                "frontier_status": frontier_after.get("status"),
                "public_anchor_statuses": [target_tight.get("status"), slack_rows.get("status")],
            },
            sort_keys=True,
        ),
        flush=True,
    )


if __name__ == "__main__":
    main()
