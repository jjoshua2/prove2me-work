# Pull-request backlog reconciliation — 2026-09-10

This note records a repository-hygiene pass for the Polynomial Hirsch workspace. It is process documentation, not mathematical evidence and not a Prove2Me theorem verdict.

## Problem

The repository had accumulated **40 open pull requests**. The open queue had become a mixture of active work, historical source branches, publication-only follow-ups, verification checkpoints, and superseded research experiments. That made it difficult to identify the actual formal frontier from GitHub's PR list.

Open PRs should represent active work; Git branches, commits, closed PRs, research notes, and verification receipts are sufficient to preserve history.

## Actions taken

### Historical/superseded PRs closed

The following 37 historical or superseded PRs were closed without deleting their branches or commits:

- #2–#11;
- #27–#31;
- #33–#54.

These included already-published theorem work, publication-only follow-ups, conditional/diagnostic research, and branches superseded by later canonical developments. Closing them changes no theorem status and preserves their Git history.

A temporary comparison PR #65 was opened accidentally while measuring obsolete ancestry and was immediately closed. Its 353 commits / 237 changed files illustrated why old stacked branches should not be merged wholesale merely to preserve useful verified files.

### PR #61 salvaged before closure

Historical PR #61 contained four useful Lean modules that had passed targeted compilation and 17 transitive axiom audits at source commit

`681314640b6f84792d8ae011c3534a6e8c456930`

in Actions run

`34532572816`.

Its branch ancestry was obsolete, so it was **not** merged directly. Instead, the four exact verified Lean blobs, two durable research/verification notes, and the exact regression script were transplanted onto current `main` in clean PR #66. PR #66 contained one commit and seven changed files and was merged as

`5a731041dc8c785e362209cead85051f6fa44557`.

PR #61 was then commented as superseded by #66 and closed. This is the preferred pattern for valuable verified work stranded on old stacked ancestry.

## PRs intentionally left open at this checkpoint

### #62 — active publication gate

`Publish four audited face-cover results to Prove2Me`

This PR is temporary publication infrastructure. Its standalone Lean statements/proofs and axiom audits passed, authenticated preflight passed, and its Prove2Me server verification step was still running at the time of this note. It must remain open until the actual server verdict is known and the resulting theorem/submission IDs and receipt are reconciled into durable repository state. It should then be closed rather than used as an archive.

### #64 — genuine active research draft

`Draft: reconcile nonvertex circuit localization and carrier-routing verification`

This is intentionally draft. It contains new nonvertex checkpoint localization, conditional carrier-routing work, and exact regressions whose combined Lean/publication gate has not yet completed. Its PR body states the blocker and next verification action. It remains an actual active work item.

## Result

After the historical cleanup and #61 → #66 integration, the intended steady-state open queue is **two PRs**: one live publication gate (#62) and one genuine active research draft (#64). #62 should disappear from the open queue as soon as its publication outcome is durably recorded.

## Rule going forward

`AGENTS.md` now specifies that open PRs are an active queue, not archival storage. Every PR should be merged, closed as superseded/historical, or explicitly kept draft with a blocker and next action. Verified work on obsolete ancestry should be clean-transplanted onto current `main`; publication-only PRs should be closed after their verdict and receipt are preserved.
