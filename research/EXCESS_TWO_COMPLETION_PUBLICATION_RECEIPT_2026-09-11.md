# Full excess-two diameter publication receipt — 2026-09-11

Mission: **The Polynomial Hirsch Conjecture**  
Platform: Prove2Me **0.10.1**  
Lean: **4.30.0**  
Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

## Public theorem

`Hirsch.normalized_two_moment_slice_diameter_two`

- theorem ID: `e93edd7b-4659-4df5-9eab-fbcce4352c78`
- submission ID: `ea2f94b1-abcf-49bd-8c0e-82423da3839e`
- verification verdict: **ACCEPTED**
- live theorem status: **Proved**
- registration result: **PUBLISHED**

The formal statement is intentionally self-contained. For arbitrary
`t : Fin n → ℝ` and `mu : ℝ`, the nonnegative simplex slice

```text
{ s : EuclideanSpace ℝ (Fin n) |
    (∀ i, 0 ≤ s_i) ∧ Σ s_i = 1 ∧ Σ t_i s_i = mu }
```

has `Hirsch.DiamLE ... 2`.

There is no moment-genericity assumption: repeated moments, empty slices,
singleton slices, and lower-dimensional cases are included.

## Frozen source and independent kernel gate

Frozen proof source commit:

`e9b89ee3f02fbaed5c379e35ef1c824ab3b85186`

Source/standalone verification:

- GitHub Actions run: `34605987684`
- verification artifact: `10266226410`
- artifact digest:
  `sha256:20c5d707bdfeda5a19f3088e94608e0542b31680143f4788cb7b825efe92c37a`
- generated standalone SHA-256:
  `45e96aecc53c63bfd394ebc11a2ee196b958534cd93fe1f648c281dad8072317`

The source gate compiled and axiom-audited the complete new chain:

- `HirschExcessTwo.singletonPoint_mem_extremePoints`
- `HirschExcessTwo.extreme_eq_of_support_contained`
- `HirschExcessTwo.feasible_support_has_singleton_or_pair`
- `HirschExcessTwo.momentSlice_extremePoints_iff`
- `HirschExcessTwo.supportFace_pair_eq_segment_singletons`
- `HirschExcessTwo.singletonPoint_adj_singletonPoint`
- `HirschExcessTwo.supportFace_triple_eq_segment_singleton_pair`
- `HirschExcessTwo.singletonPoint_adj_pairPoint`
- `HirschExcessTwo.momentSlice_two_step_route_preserving_zeros`
- `HirschExcessTwo.supportFace_two_step_route`
- `HirschExcessTwo.momentSlice_diamLE_two`
- `HirschExcessTwo.supportFace_diamLE_two`

It then flattened the fixed dependency chain to a standalone `solution.lean`,
compiled that file independently, and axiom-audited `solution`. Every report
contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Authenticated publication gate

The first authenticated attempt, run `34606609780`, failed closed immediately
when token refresh reported that the live platform had upgraded from reviewed
0.10.0 to **0.10.1**. The exact proof packet had already passed SHA, Lean, and
axiom checks, but no theorem registration or proof submission occurred in that
failed attempt.

The compatibility rerun changed only the explicitly reviewed platform-version
guard. It preserved every frozen `Solutions/`, `Definitions/`, Lean-pin, and
standalone-proof byte.

Successful publication transaction:

- GitHub Actions run: `34606984246`
- publication branch head: `1692538ba9f7661ca079a86f2963fb48ac2270d1`
- receipt artifact: `10266714009`
- artifact digest:
  `sha256:b787863f78425a4136b2f060bf296fec79b4b04adedbe9918f165cac05452afd`

Before the repository secret was exposed, the successful run:

1. verified no proof/definition/Lean-pin bytes differed from frozen source;
2. regenerated the standalone file;
3. required exact SHA-256 equality;
4. recompiled it under the pinned environment; and
5. reran the clean axiom audit.

The authenticated client then collision-checked theorem name and exact formal
type, registered the theorem, submitted the exact audited standalone proof,
and required both server verdict **ACCEPTED** and live theorem status **Proved**.

## Mission linkage and frontier preservation

Polynomial Hirsch mission ID:

`6078cb2d-3594-44b1-a01a-fd452ddae274`

Mission discussion reference:

`fb10586a-11b4-40fa-944c-673c7a28f5ea`

The comment links both the public theorem and accepted solution and explicitly
records the remaining scope boundary: the normalized rank-two slice theorem
does not imply that every arbitrary circuit carrier is such a slice.

The authenticated transaction checked the actual formal frontier before and
after publication:

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

- theorem ID: `73beca40-31bc-42d5-8350-5ec9ac28bd3e`
- before: **Open**
- after: **Open**
- graph modified: **false**
- new conjectural children: **0**

Therefore this publication closes the normalized excess-two base geometry, but
**does not solve Polynomial Hirsch** and does not itself supply the required
global circuit-to-edge accounting.

## Stronger internal result and next bridge

The repository proof is stronger than the public top-level diameter statement:
`momentSlice_two_step_route_preserving_zeros` chooses the intermediate vertex
without introducing a coordinate zero at both endpoints, and
`supportFace_diamLE_two` proves every coordinate support face has intrinsic
graph diameter at most two using edges of that face.

The highest-value next formal bridge is diagonal slack normalization and affine
transport for bounded strictly feasible `d`-dimensional H-presentations with at
most `d+2` irredundant rows. Combined with the representation-independent row
count result from PR83, the useful common-face interface is expected to be:

```text
coordinate dimension h and minimal irredundant strict row count M_min ≤ h + 2
  ==> intrinsic graph diameter ≤ 2.
```

That bridge remains separate work and is not claimed by this receipt.
