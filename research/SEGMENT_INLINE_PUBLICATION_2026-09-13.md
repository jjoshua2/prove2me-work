# Inline segment packets — authenticated Prove2Me receipts

Date: 2026-09-13. Distinct from the two frozen WA targets that used custom preamble declarations.

The platform-safe restatements use only Mathlib symbols in the registered type. They were accepted from PR #210 head `9b077abd1c537a7388acbaefd0f771ad63261b5c` in [Actions run 34776662935](https://github.com/jjoshua2/prove2me-work/actions/runs/34776662935). This PR preserves the same packet sources on a small branch.

| Theorem | ID | Submission | Verdict | Live status |
|---|---|---|---|---|
| `Hirsch.segment_summand_equality_of_finite_farkas_weights` | [7ad7d8d9](https://prove2.me/theorems/7ad7d8d9-d9e9-424b-b0bb-09c0c52c0f13) | `9d3523aa-69d4-49e2-afcd-ecdcbb12ebd9` | ACCEPTED | Proved |
| `Hirsch.sharp_fiber_caps_every_segment_summand` | [5e34643a](https://prove2.me/theorems/5e34643a-d18e-43d1-9450-24f857d966db) | `c865e829-a932-4887-b23e-873f5e2ba5e2` | ACCEPTED | Proved |

Do not resubmit `Hirsch.segment_summand_equality_of_farkas_certificates` or `Hirsch.any_segment_summand_le_sharp_width`. Those WA registrations are immutable.

A concurrent `/prove2me publish` on this PR failed while registering `sharp_fiber_caps` because the same names were already in flight. That is not a Lean failure of these packets.
