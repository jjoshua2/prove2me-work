# Circuit localization formal verification — 2026-09-10

Two structural row-circuit results are kernel-checked in Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f` on branch
`formal/circuit-localization`.

Verified source commit: `9f964b8617fbbcae3cf652c130cbdbacd32b0dea`.
GitHub Actions run: `34495410594`.
Artifact: `10159657523`, `circuit-localization-one-shot`.

The gate compiled the complete source modules and public adapters, rejected
`sorryAx`, and axiom-audited all required declarations with only `propext`,
`Classical.choice`, and `Quot.sound`. It then deterministically flattened each
public adapter into a standalone `solution.lean`, independently compiled each
standalone file, and repeated the axiom audit.

Standalone hashes:

- row-circuit common-face localization:
  `6d3b6b7aecd9c483d30acdff94ff304afad8a8c45f6948b6c12aba1efc1ec009`
- balanced shared-tight-row obstruction:
  `e9b2a0be5fde78404b9b3456a8936d1ff3fea93be27c4cff0d318d02e27fe4ce`

## Result 1

For extreme vertices `u,v` of an `n`-row H-polytope in ambient dimension `d`,
if `v-u` is a support-minimal row circuit, then

`2 * dim F(u,v) + d <= n + 1`,

where `F(u,v)` is the face cut out by all nonzero describing rows tight at both
endpoints. Equivalently `2 * dim F(u,v) <= n-d+1`.

No simplicity, irredundancy, strict-feasibility, or maximal-step assumption is
used.

## Result 2

If additionally `n=2d` and `d>=2`, then a vertex-to-vertex row-circuit pair
must share a nonzero describing row tight at both endpoints. Thus an exactly
balanced estranged vertex pair cannot be one row-circuit step.

The proof is a direct row count: each endpoint has at least `d` nonzero tight
rows, a row circuit supplies at least `d-1` neutral rows, and under the
no-shared-row assumption those three row families are pairwise disjoint.

## Research boundary

These results localize a single vertex-to-vertex circuit displacement. They do
not prove that the circuit remains a circuit in the irredundant intrinsic
presentation of the common face, and they do not provide a polynomial edge
route. The formal Open frontier therefore remains
`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`).
