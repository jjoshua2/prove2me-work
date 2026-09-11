# Low-excess section descent publication receipt — 2026-09-11

Mission: **The Polynomial Hirsch Conjecture**  
Platform: Prove2Me **0.10.1**  
Lean: **4.30.0**  
Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

## Public theorem

`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`

- theorem ID: `12426807-9602-4014-bd5e-c69fb43f4cb6`
- accepted submission ID: `59736803-0e9d-40bb-875d-7ca66b9ccd45`
- verification verdict: **ACCEPTED**
- live theorem status: **Proved**
- registration result: **REUSED**
- solution SHA-256: `58ceb59004e1f9046ccaaf8b55ae39e7e8646135c5c521b8e74b495e7c238568`

The theorem states that every bounded `n`-row H-polyhedron in ambient dimension
`d` with `n <= d+3` has padded vertex-edge diameter at most `n-d`. Empty and
lower-dimensional feasible sets, redundant inequalities, and zero normals are
included. No strict-feasibility or irredundancy hypothesis is required.

In particular:

```text
n <= d+2  ==>  DiamLE P 2.
```

This removes positive slack-weight existence as a prerequisite for the
**diameter-only** row-excess-two base case. The explicit normal-relation theorem
remains useful for exact slack coordinates and intrinsic selected-row support
faces.

## Kernel / standalone evidence

Frozen source commit: `2774702c54078cb8efae7bed185ed1b4b93bce5b`.

- source module blob: `794126103cc9d9f60a95eb262d96d282f3e9ad4f`
- vertex-span dependency blob: `673e5a68f154b66556d01dd81977107329a3415e`
- first complete source/driver gate: Actions run `34619780682`, job
  `103330569162`
- final publication/recovery run: `34620239467`
- final artifact: `10271654810`, digest
  `sha256:8ab4205200f170189f6da2189195b37274c5c3f5bec1b5b350b2f62e01dea71d`
- audited driver SHA-256:
  `d58e8dcb92d9ee1d21f330a64432c6b0d7b880ba6c44c803dd39bf33bc0deb1a`

The driver compiled with the low-dimensional Hirsch and facet-reduction results
as explicit logical premises rather than local theorem stubs. The unconditional
public solution then supplied exactly these two already-Proved dependencies via
tracked platform imports:

- `Hirsch.dimension_three_bound`, theorem
  `cf588038-4ee8-4c90-b034-348c28d0da21`;
- `Hirsch.facet_reduction`, theorem
  `11b3500a-b9f8-4b44-94aa-d71354441ddb`.

The platform rechecked their names, exact formal types, Proved statuses, and
Mathlib pin before accepting the composition.

## Proof structure

At every vertex the nonzero tight row normals span the ambient direction space,
so there are at least `d` distinct tight nonzero rows. If `d>3` and `n<=d+3`,
then `n<2d`; hence two endpoint vertices share a nonzero tight row. Restrict to
that equality section and use the established facet reduction. Both row count
and ambient dimension drop by one, so the excess is unchanged:

```text
(n-1) - (d-1) = n-d.
```

Both endpoints already lie in the section, so no access step or multiplicative
routing cost is introduced. Strong induction terminates at the already-Proved
`d<=3` theorem.

## Mission/frontier integrity

Mission comment: `24672cde-eaba-4630-8fa5-025950227067`.

The authenticated transaction checked
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`) before and after publication. Its
status remained **Open**, the frontier graph was not modified, and no new
conjectural children were created.

This theorem is a small-excess base result, not a solution of Polynomial Hirsch.
The next mission-facing adapter is the common-face statement
`M_min <= commonFaceDim + 2 -> intrinsic common-face diameter <= 2`.
