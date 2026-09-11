# Exact minimum-carrier-excess routing verification — 2026-09-11

Frozen source commit: `a1717403cd65a365079aa9c32baa2340c439157a`.
Verification run: `34633804214`; job `103376743065`.
Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The targeted build `Solutions.PolynomialMinCarrierExcessRouting` completed successfully. The audit checked 150 printed transitive reports and required these four declarations; each has only `propext`, `Classical.choice`, and `Quot.sound`:

1. `HirschCircuitLocalization.commonFace_has_subpresentation_faceDim_add_minExcess`;
2. `HirschCircuitLocalization.commonFace_diamLE_minPresentationExcess_of_le_three`;
3. `HirschCircuitLocalization.feasible_sequence_edge_route_sum_minPresentationExcess_of_each_le_three`;
4. `HirschCircuitLocalization.rowCircuitWalk_edge_route_sum_minPresentationExcess_of_each_le_three`.

No `sorryAx` or other axiom occurs in their transitive closures.

## Mathematical content

Define the intrinsic minimum carrier presentation excess

```text
e(u,v) = commonFaceMinSubpresentationCount a b u v
         - commonFaceDim a b u v.
```

For a bounded parent and feasible source checkpoint, the minimum presentation witness itself supplies an equivalent common-face coordinate presentation with exactly the budget `h+e`. Therefore, whenever `e<=3`, the already verified small-carrier routing theorem gives intrinsic carrier graph diameter at most exactly `e`.

For a feasible checkpoint sequence `w 0,...,w L` with parent-vertex endpoints, if every step satisfies `e_i<=3`, the parent graph has an ordinary edge/stay route of exact budget

```text
sum i : Fin L, e_i.
```

No rounding to `3L` is required. The RowCircuitWalk specialization simply unpacks circuit-walk feasibility; intermediate circuit checkpoints may be nonvertices.

## Scope

The local file keeps the public small-excess H-polyhedron theorem as the explicit premise `SmallExcessHpolyBound`, so this kernel audit imports no local theorem stub. The theorem does not establish `e_i<=3` for arbitrary circuit steps. Combined with the reference-free circuit defect theorem, it cleanly separates easy steps (`e_i<=3`, exact graph cost `e_i`) from the still-open large-excess carrier regime.
