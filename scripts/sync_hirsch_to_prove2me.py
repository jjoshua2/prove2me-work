#!/usr/bin/env python3
"""Idempotently reconcile GitHub Polynomial Hirsch status to the Prove2Me board."""
from __future__ import annotations

import datetime
import json
import os
import urllib.parse
import urllib.request
from pathlib import Path

BASE = "https://prove2.me/api/v1"
VERSION = "0.10.1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
MISSION_NAME = "The Polynomial Hirsch Conjecture"
MISSION_ID = "6078cb2d-3594-44b1-a01a-fd452ddae274"
MARKER = "<!-- jjosh-hirsch-sync-2026-09-11-1520z -->"
OUT = Path("prove2me_hirsch_sync_writeback")

IDS = {
    "root": "58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac",
    "edge_parent": "099c6686-560c-48fc-b2c2-18b6a620a06e",
    "edge_d4": "73beca40-31bc-42d5-8350-5ec9ac28bd3e",
    "row_count": "8538150b-8afe-47ad-94b0-d72189b80264",
    "two_moment": "e93edd7b-4659-4df5-9eab-fbcce4352c78",
    "affine_transport": "c4b0c852-981b-4bd7-8578-07e72315c3c9",
    "subbalanced": "0e4f233c-418a-4884-bbfb-dbfc7f76bc76",
    "ridge_access": "5f309362-bbda-4dea-806f-20b4e2712a2d",
    "common_face_ge6": "87a8b4f4-8b58-4340-8cb9-5fd1b548d01e",
}
EXPECTED = {
    "root": "Open", "edge_parent": "Open", "edge_d4": "Open",
    "row_count": "Proved", "two_moment": "Proved", "affine_transport": "Proved",
    "subbalanced": "Proved", "ridge_access": "Open", "common_face_ge6": "Open",
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
        with self.opener.open(req, timeout=45) as r:
            data = json.load(r)
        self.token = data["access_token"]
        self.version = data.get("version")
        if self.version != VERSION:
            raise RuntimeError(f"platform version changed: {self.version!r}")

    def request(self, path: str, data=None, method: str = "GET"):
        if not path.startswith("/") or path.startswith("//") or "://" in path:
            raise ValueError("API-relative path required")
        if not self.token:
            self.refresh()
        req = urllib.request.Request(
            BASE + path,
            data=None if data is None else json.dumps(data).encode(),
            headers={
                "Authorization": "Bearer " + self.token,
                "Accept": "application/json",
                "Content-Type": "application/json",
            },
            method=method,
        )
        with self.opener.open(req, timeout=120) as r:
            return json.load(r)


def save(name: str, data) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / name).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def find_mission(api: API) -> dict:
    offset = 0
    matches = []
    while True:
        page = api.request("/missions?" + urllib.parse.urlencode({"limit": 100, "offset": offset}))
        rows = page.get("missions", [])
        matches.extend(m for m in rows if m.get("id") == MISSION_ID or m.get("name") == MISSION_NAME)
        offset += len(rows)
        if not rows or offset >= int(page.get("total", offset)):
            break
    exact = [m for m in matches if m.get("id") == MISSION_ID and m.get("name") == MISSION_NAME]
    if len(exact) != 1:
        raise RuntimeError(f"exact mission lookup failed: {len(exact)} matches")
    return exact[0]


def get_comments(api: API) -> list[dict]:
    out, offset = [], 0
    while True:
        page = api.request(
            f"/missions/{MISSION_ID}/comments?" + urllib.parse.urlencode({"limit": 100, "offset": offset})
        )
        rows = page.get("comments", [])
        out.extend(rows)
        offset += len(rows)
        if not rows or offset >= int(page.get("total", offset)):
            return out


def get_states(api: API) -> dict:
    states = {}
    for label, tid in IDS.items():
        t = api.request("/theorems/" + tid)
        state = {k: t.get(k) for k in ("theorem_id", "theorem_name", "status", "mathlib_rev")}
        states[label] = state
        if t.get("mathlib_rev") != PIN:
            raise RuntimeError(f"{label}: unexpected Mathlib revision")
        if t.get("status") != EXPECTED[label]:
            raise RuntimeError(f"{label}: expected {EXPECTED[label]}, got {t.get('status')}")
    return states


def p2m(label: str, key: str) -> str:
    return f"[{label}](p2m:theorem/{IDS[key]})"


def body() -> str:
    return f"""## GitHub ↔ Prove2Me synchronization — 2026-09-11

Pulled the live Prove2Me 0.10.1 mission state and reconciled it with `jjoshua2/prove2me-work`. All **six curated milestones are Proved** (Klee/Klee–Walkup d≤3, Larman, Naddef 0/1, Kalai–Kleitman, Todd, Santos). The root {p2m('Polynomial Hirsch conjecture', 'root')} remains **Open**.

### Public results now synchronized with the repository
- {p2m('irredundant row-count invariance', 'row_count')}: strictly feasible irredundant H-presentations are cardinal-minimal among equivalent finite presentations.
- {p2m('normalized two-moment slice diameter ≤ 2', 'two_moment')}: normalized nonnegative two-moment simplex slices have padded graph diameter at most two, including repeated/degenerate cases.
- {p2m('injective affine diameter transport', 'affine_transport')}: injective affine embeddings preserve and reflect the exact vertex-edge diameter across different ambient dimensions. Its audited source and publication receipt are now merged into GitHub `main`.

### Progress pulled back from the live board
The newly Proved {p2m('sub-balanced section inheritance theorem', 'subbalanced')} says that for `n < 2d`, shared tight rows reduce diameter to equality sections; this is complementary to the low-excess/slack-slice route and should be reused.

The ridge-visible-access attack is also useful negative/positive guidance. {p2m('Polynomial access to a ridge-visible vertex', 'ridge_access')} remains **Open**; current experiments rule out an O(1) bound, and the naive recurrence through full facet diameter becomes dimension-multiplicative.

### Current work — not yet a proof
The next formal bridge is **positive-weight / codimension-two slack normalization**: map a bounded low-row-count H-presentation exactly onto the normalized two-moment slice, then invoke affine transport. Target interface:

`M_min ≤ h + 2  ⇒  intrinsic common-face diameter ≤ 2`.

The ordinary proof plan constructs a strictly positive annihilating row weight from boundedness, separates the zero-mass/singleton case, and uses a second annihilator when row excess is at most two. **This normalization is not yet kernel-verified or submitted**, and we are not claiming arbitrary circuit carriers are automatically two-moment slices.

### Still open
- {p2m('common-face diameter in dimension ≥ 6', 'common_face_ge6')};
- {p2m('d≥4 circuit-to-edge refinement', 'edge_d4')} and its {p2m('parent edge-refinement theorem', 'edge_parent')};
- uniform ridge-visible access and the root Polynomial Hirsch conjecture.

No new conjectural child is created here. The global proof would still need to control **total** edge-routing cost over an entire circuit walk, not just one low-excess carrier.

{MARKER}"""


def main() -> None:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY is absent")
    api = API(key)
    envs = api.request("/environments")
    if not any(e.get("mathlib_rev") == PIN for e in envs.get("environments", [])):
        raise RuntimeError("pinned Mathlib environment unavailable")
    save("mission.json", find_mission(api))

    before = get_states(api)
    save("theorems-before.json", before)

    milestone_data = api.request(f"/missions/{MISSION_ID}/milestones")
    milestones = milestone_data if isinstance(milestone_data, list) else milestone_data.get("milestones", [])
    if len(milestones) != 6 or any((m.get("theorem") or {}).get("status") != "Proved" for m in milestones):
        raise RuntimeError("curated milestone state is no longer six Proved milestones")
    save("milestones.json", milestones)

    comments = get_comments(api)
    existing = next((c for c in comments if MARKER in (c.get("body_md") or "")), None)
    if existing is None:
        request = {"body_md": body(), "tags": ["reference", "strategy"]}
        save("comment-request.json", request)
        comment = api.request(f"/missions/{MISSION_ID}/comments", request, "POST")
        action = "POSTED"
    else:
        comment, action = existing, "REUSED_EXISTING"
    save("comment.json", comment)

    matches = [c for c in get_comments(api) if MARKER in (c.get("body_md") or "")]
    if len(matches) != 1:
        raise RuntimeError(f"sync marker count is {len(matches)}, expected one")

    after = get_states(api)
    if before != after:
        raise RuntimeError("theorem states changed during status-only sync")
    save("theorems-after.json", after)

    receipt = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform_version": api.version,
        "mathlib_rev": PIN,
        "mission_id": MISSION_ID,
        "mission_name": MISSION_NAME,
        "milestone_count": 6,
        "milestones_all_proved": True,
        "comment_action": action,
        "comment_id": comment.get("id"),
        "marker": MARKER,
        "theorem_states": after,
        "graph_mutation": False,
        "theorem_or_proof_submission": False,
    }
    save("receipt.json", receipt)
    print(json.dumps(receipt, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
