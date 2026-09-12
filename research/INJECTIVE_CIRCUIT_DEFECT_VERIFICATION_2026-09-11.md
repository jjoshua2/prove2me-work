# Hosted verification: injective circuit defect accounting

Date: 2026-09-11 (America/New_York)

## Frozen proof source

- branch: `formal/injective-circuit-defect`
- proof source commit: `982fc860f539cf46d6a2fd8121d81b11a47f1943`
- workflow run: `34666807890`
- job: `103480243486`
- Lean: `4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

Artifact:

- id: `10289323110`
- name: `injective-circuit-defect-verification`
- digest: `sha256:220e678a923d6c94d85df318f1cb355c8c339d61a5ab095898a48af709cd7d4a`

## Result

All three new modules built successfully:

- `Solutions.PolynomialCircuitInjectiveNeutralRank`
- `Solutions.PolynomialCircuitInjectiveDeletionSavings`
- `Solutions.PolynomialOneRowDeletionCircuitDefect`

The focused axiom audit checked 13 public declarations and found only the accepted logical axioms `propext`, `Classical.choice`, and `Quot.sound`.

The audit script reported:

`Axiom audit passed: 13 required declarations; 13 reports checked; only standard logical axioms.`

## Mathematical result

Row-map injectivity, rather than boundedness, is the actual linear-algebra hypothesis behind the exact circuit neutral-kernel and neutral-rank theorems. Under injectivity:

- the neutral kernel of a row circuit is exactly its one-dimensional circuit line;
- neutral rank is exactly ambient/subspace dimension minus one;
- the common-direction rank is exactly `commonFaceDim - 1`;
- the selected-row neutral defect is bounded by discarded neutral rows;
- the full five-term excess/defect/savings identity and its saturation criterion remain valid.

Because a one-row deletion outer of a bounded nonempty parent has an injective row map, all of these statements apply directly to the potentially unbounded deletion presentation from PR #151. In particular, the deletion outer keeps the exact neutral-rank and resource accounting needed by the carrier program.

Combined with PR #151, the deletion outer now has both an explicit cubic row-circuit route and the bounded-parent rank/defect bookkeeping. The remaining old-outer obstruction is therefore dynamic circuit-to-edge routing, not circuit-walk existence or loss of rank/excess control under deletion.

No Prove2Me publication or mutation was performed by this verification run.
