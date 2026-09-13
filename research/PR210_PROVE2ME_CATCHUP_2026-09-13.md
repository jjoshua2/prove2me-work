# PR #210 Prove2Me catch-up — 2026-09-13

This receipt separates repository/Lean verification from authenticated Prove2Me verdicts.

## Authenticated ACCEPTED results

Actions run `34774357689` compiled and axiom-audited the frozen packets at head
`baf56bcda56073be43cb25db3669cb29726f404d`, then the trusted main-branch
publisher used `PROVE2ME_API_KEY` and received authenticated platform verdicts:

- `Hirsch.direction_local_budget_iff_group_budgets`
  - theorem `f18c9025-ee8a-4a89-97d9-ac3bd239dbb6`
  - submission `fe85263b-0909-405a-a389-3ca664f8a170`
  - verdict **ACCEPTED**
- `Hirsch.nonnegative_packing_region_downward_closed`
  - theorem `ba1e8a52-7453-4bc2-b1ea-b022512a8977`
  - submission `3afbc375-ab82-4bcc-aaee-cb0100fad1a3`
  - verdict **ACCEPTED**
- `Hirsch.weighted_transition_lower_bound`
  - theorem `7e735eb5-bb09-4f10-9a2b-780f1407dd92`
  - submission `6db63032-0da1-4db1-8418-0ad1b25d1c55`
  - verdict **ACCEPTED**

The authenticated publication log is preserved in GitHub Actions run
`34774357689`; artifact `prove2me-publication-receipts` was uploaded by that run.

## Authenticated WA results — do NOT count as proved

Two early packets compiled locally but registered custom helper definitions in
`problem.json` preambles while also redeclaring those helpers in `solution.lean`.
Prove2Me's exact target comparator rejected them. These immutable theorem targets
must not be retried unchanged:

- `Hirsch.segment_summand_equality_of_farkas_certificates`
  - theorem `2eaa5e9c-b6c5-45e3-b4fd-f08e023133bf`
  - submission `755cb0b3-7bbd-41f5-a3a1-a583e2ae3a03`
  - verdict **WA**
- `Hirsch.any_segment_summand_le_sharp_width`
  - theorem `9f931e6d-3190-4c5d-ac47-36d4ad613fca`
  - submission `d4e108fb-17f2-4e5a-819e-3976c813c992`
  - verdict **WA**

Fresh public-symbol-only replacements are staged under
`research/publication_packets/pr210_catchup/segment_farkas_inline/` and
`research/publication_packets/pr210_catchup/segment_sharp_inline/`.

## Module-only verification improvements

Main now supports comments of the form

```text
/prove2me verify --targets=Solutions.A,Solutions.B
```

The named modules are built at the PR head SHA without a publication packet and
without the Prove2Me secret. This caught and enabled repairs to stale Lean 4.30
API usages in:

- `Solutions.PolynomialSegmentFiberEquality`
- `Solutions.PolynomialSegmentFarkasMaximality`
- `Solutions.PolynomialFiniteSummandObstructions`
- `Solutions.PolynomialJointExtractionGeometry`
- `Solutions.PolynomialMinkowskiExposedEdges`

`Solutions.PolynomialAntipodalSegmentCoverage` already built with only standard
logical axioms. A platform-safe standalone packet for its geometric switch lemma
is staged at `pr210_catchup/segment_switch_edge_line/`.

The segment modules were verified together successfully after repairing two old
`mul_le_mul_* .mp` usages. The larger finite-summand/Minkowski chain is being
rerun after source repairs; no platform verdict should be inferred until its
current Actions verification finishes.

## Workflow safeguards

- Verification checks the exact PR head and does not receive `PROVE2ME_API_KEY`.
- Publication consumes only the immutable verified artifact using trusted code
  checked out from `main`.
- Module-only verification artifacts cannot be published.
- Publishing still requires explicit `problem.json` + `solution.lean` packets.
- PR #215 added a guard against the custom-preamble packet pattern responsible
  for the two WAs above.

Only authenticated Prove2Me responses listed under **ACCEPTED** are platform
proof verdicts. Lean compilation and axiom audits are prerequisites, not verdicts.
