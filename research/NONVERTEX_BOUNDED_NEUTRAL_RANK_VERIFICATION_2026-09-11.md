# Bounded nonvertex circuit neutral-rank verification — 2026-09-11

## Kernel evidence

Frozen source commit: `1922d706523c5253bbe32079e6e6ab71444b3538`.
GitHub Actions run: `34630740596`; job: `103366669600`.
Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The gate ran

```text
lake build Solutions.PolynomialCircuitBoundedNeutralRank
```

and completed all 8,488 jobs successfully. The axiom checker inspected 20 transitive `#print axioms` reports; the four required declarations use only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.

Checked declarations:

1. `HirschCircuitLocalization.rows_ge_dimension_of_bounded`;
2. `HirschCircuitLocalization.rowCircuit_neutral_kernel_eq_span_of_bounded`;
3. `HirschCircuitLocalization.rowCircuit_neutral_rank_eq_dim_sub_one_of_bounded`;
4. `HirschCircuitLocalization.rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded`.

## Mathematical content

The earlier row-circuit neutral-rank chain assumed the source point was a parent vertex. This verification shows that assumption is not needed when the parent H-polyhedron is bounded and the source checkpoint is feasible.

The key replacement is `HirschCircuit.rowMap_injective_of_bounded`: in a nonempty bounded H-polyhedron, no nonzero ambient direction can be annihilated by every row. Therefore a nonzero row-circuit direction has at least one nonzero row evaluation, and the support-minimality argument again forces the common kernel of all neutral rows to be exactly the circuit line.

Consequently, for a feasible source `u` in a bounded parent and an ambient row circuit `v-u`, the neutral rows restricted to the common-direction space have rank exactly

```text
commonFaceDim(a,b,u,v) - 1.
```

No source-vertex or target-vertex hypothesis is needed for this rank statement.

## Frontier consequence

This removes the first substantive use of source vertexhood in the current minimum-subpresentation excess/defect theorem. The remaining vertex-dependent ingredient is the lower bound saying an equivalent effective common-face subpresentation contains at least `h` nonzero rows. Since the common-face coordinate H-polyhedron is itself bounded for a bounded parent, the same bounded row-map injectivity argument should also replace vertex extremality there. If that propagation succeeds, the exact minimum-subpresentation excess/defect inequality extends to nonvertex circuit checkpoints without the self-face correction terms previously expected in the research handoff.
