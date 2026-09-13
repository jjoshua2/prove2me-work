# Isolated GitHub-connector module verification smoke test

The user requested an actual test of merged PR #212's module-only comment flow.
This disposable, documentation-only PR is separate from #210 and #208 and
contains no proof packet, new Lean code, workflow, pin, or publication change.

Base: `5f50509fe93e4cd9d5f0f3a8cf8469dc1449368f` (main after #212).
Target: `Solutions.PolynomialSeparatedRows`.
Target source blob: `1f023489ae9edadc18d6b6cf3a88d003ebdfff46`, unchanged from main.

Post one new top-level comment:

```text
/prove2me verify --targets Solutions.PolynomialSeparatedRows
```

Expected result: the owner-authored connector comment resolves this PR's exact
head SHA, builds the existing module without selecting any packet, freezes a
module-only artifact, skips publication, and returns the verification comment.
This is a workflow smoke test of an existing merged module, not an interactive
hosted proof-repair loop. No Prove2Me submission is requested.

The authoritative result will be recorded in the PR conversation with the
Actions run URL, pinned SHA, job outcomes, and returned bot comment. Do not
claim success until those outputs are observed. Close this disposable PR after
the test; preserve its conversation and branch as the audit trail rather than
merging test-only documentation into main.
