# Circuit-step publication receipt — 2026-09-10

This receipt records the final kernel and Prove2Me verification of the maximal-step carrier bound and exact tight-blocker swap characterization.

## Frozen Lean evidence

- Lean: `v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- frozen publication source commit: `2ef303016d5edbed0bb339fc7341b4f019ada400`
- publication-quality source/adapter/standalone gate: Actions run `34553646058`
- gate artifact: `10181764818`
- gate artifact digest: `sha256:02d02d55a7d79ced5cee262b92937e44872f7a4258d12260f0f7cb0f0fdfa3a6`
- carrier standalone SHA-256: `ad1bcdc39d8a8f3dd0993b1af9262647ba27f87b3abf5f9a17b9345993b6cd12`
- swap standalone SHA-256: `49103bd1d83928d2c28b903ed79ec2b098ca9fd55eaf5af491bd128071de2e5e`

The core characterization, both public adapters, and both independently flattened standalone `solution` files compiled. Their audited transitive axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Prove2Me 0.10.0 publication

The first authenticated publication attempt correctly failed closed when the platform reported version `0.10.0` instead of the previously reviewed `0.9.9`. The same frozen Lean bytes were then rerun against an explicit 0.10.0 contract check.

Successful publication run: `34555207789`, job `103126314228`.
Receipt artifact: `10182563828`, digest `sha256:00ba594d446bc8aea02ffcc7c54e8e6773f3a1b545802a405ba7a4d6b55d46a6`.

### `Hirsch.maximal_row_circuit_step_common_face_bound`

- theorem ID: `bfea4b5b-106a-4e52-8297-b8138ca0a294`
- submission ID: `6fa5d295-7b3e-4463-a823-b9933a67ed70`
- verdict: **ACCEPTED**
- live status: **Proved**
- submitted solution SHA-256: `ad1bcdc39d8a8f3dd0993b1af9262647ba27f87b3abf5f9a17b9345993b6cd12`

For a maximal row-circuit step `x → y` in an `n`-row presentation in dimension `d`, assuming the same H-polyhedron has a reference extreme vertex `z`,

```text
commonFaceDim(x,y) + d ≤ n + commonFaceDim(x,x).
```

No endpoint-vertex hypothesis is imposed on `x` or `y`. Internally maximality supplies a destination-tight row increasing along the step and hence a strict drop from the step carrier to the destination self-carrier.

### `Hirsch.row_circuit_step_swap_iff_tight_blockers`

- theorem ID: `bd9710b8-067a-4ce6-8ab9-1f6f763133b7`
- submission ID: `641acc00-19d4-41ba-93b3-8893e7e94c0b`
- verdict: **ACCEPTED**
- live status: **Proved**
- submitted solution SHA-256: `49103bd1d83928d2c28b903ed79ec2b098ca9fd55eaf5af491bd128071de2e5e`

Given two maximal row-circuit steps `x → y → z`, write `w = x + (z-y)`. The swapped steps `x → w → z` are both maximal row-circuit steps exactly when `w` is feasible and each swapped displacement has a destination-tight nonzero row with strictly positive derivative. The two original row supports need not be disjoint.

## Frontier readback

Before and after publication, Prove2Me 0.10.0 returned

- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
- theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`
- status **Open**
- same pinned Mathlib revision.

The publisher recorded `frontier_graph_modified: false` and `new_conjectural_children: 0`. These two structural results therefore do not claim Polynomial Hirsch or close the edge-refinement bottleneck.
