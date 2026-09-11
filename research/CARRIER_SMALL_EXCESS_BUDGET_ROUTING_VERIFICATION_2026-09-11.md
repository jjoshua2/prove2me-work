# Variable small-carrier-excess routing verification — 2026-09-11

Frozen source commit: `7432a15c4fc271ce184de058bdab5fbb9e431cd8`.
Verification run: `34630585106`; job `103366140769`.
Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The targeted build completed successfully. The audit checked 126 transitive
reports and required these three declarations; each has only `propext`,
`Classical.choice`, and `Quot.sound`:

1. `HirschCircuitLocalization.feasible_sequence_edge_route_three_mul_of_carrier_subpresentation_at_most`;
2. `HirschCircuitLocalization.commonFace_diamLE_of_subpresentation_excess_le_three`;
3. `HirschCircuitLocalization.feasible_sequence_edge_route_of_carrier_excess_budgets_le_three`.

No `sorryAx` or other axiom occurs in their transitive closures.

## Mathematical content

The main intrinsic theorem keeps the exact carrier cost. If a bounded common
carrier of dimension `h` admits an equivalent coordinate H-presentation using
at most `h+r` rows, with `r <= 3`, then its intrinsic graph diameter is at most
`r`.

The sequence theorem applies this independently at every old step. For a
feasible checkpoint sequence `w 0,...,w L` with parent-vertex endpoints, choose
budgets `R : Fin L -> Nat` satisfying `R i <= 3` and explicit equivalent
subpresentations with at most `h_i + R i` rows for each consecutive common
carrier. Then the parent graph has an ordinary edge/stay route of exact budget

```text
sum i, R i.
```

The ambient parent may have arbitrary row excess and the interior checkpoints
may be nonvertices. Thus the checked reduction preserves the actual additive
small-carrier-excess cost instead of rounding every step up to three.

## Evidence boundary

The source keeps the already-Proved small-excess H-polyhedron theorem as the
explicit logical premise `SmallExcessHpolyBound`, so this local audit does not
import a theorem stub. The theorem does not establish that arbitrary circuit
walks admit `R_i <= 3`; it converts such carrier presentation certificates into
ordinary edge-routing cost. Bounding or amortizing the carrier excesses in the
general d>=4 frontier remains Open.
