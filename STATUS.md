# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-11 18:04 UTC. Repo: `jjoshua2/prove2me-work`.
Platform: Prove2Me 0.10.1. Lean: v4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

Best continuation files:

- `research/SMARTER_AGENT_HANDOFF_2026-09-11.md` — broad frontier map;
- `research/NONVERTEX_MIN_SUBPRESENTATION_EXCESS_PLAN_2026-09-11.md` — exact
  next proof plan after the newest nonvertex result.

## Public Prove2Me state

**Polynomial Hirsch is not solved.** Latest authenticated synchronization plus
the later accepted carrier publication give:

- `Hirsch.polynomial_hirsch_conjecture`
  (`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`): Open;
- `Hirsch.polynomial_edge_refinement_of_circuit_walks`
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`): Open;
- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`): Open;
- `Hirsch.common_face_diameter_of_dim_ge_six`
  (`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`): Open;
- `Hirsch.polynomial_access_to_ridge_visible_vertex`
  (`5f309362-bbda-4dea-806f-20b4e2712a2d`): Open.

All six curated historical mission milestones are Proved.

Important public low-excess results:

1. `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
   (`12426807-9602-4014-bd5e-c69fb43f4cb6`, accepted proof
   `59736803-0e9d-40bb-875d-7ca66b9ccd45`): every bounded n-row H-polyhedron
   with `n<=d+3` has `DiamLE P (n-d)`.
2. `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`
   (`ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted proof
   `b9d5af5b-51d3-48dd-b008-a365a18b053e`): in a bounded parent with
   `n<=d+2`, any common carrier based at a feasible checkpoint has intrinsic
   diameter <=2; the second checkpoint may be arbitrary.

The accepted carrier publication re-read the d>=4 frontier Open and made no
conjectural graph mutation. Receipt:
`research/EXCESS_TWO_COMMON_CARRIER_PUBLICATION_RECEIPT_2026-09-11.md`.

## GitHub: low-excess graph-routing plumbing is now complete through excess 3

### Intrinsic excess <=2

PR #105 is merged. Frozen source
`dc6fea94d21e8cb62db0a1cd066b21696a88f4b9`, run `34629982502`, job
`103364150810`; 123 transitive axiom reports, only `propext`,
`Classical.choice`, `Quot.sound`.

For an arbitrary bounded parent, if each selected consecutive carrier satisfies

```text
M_i := commonFaceMinSubpresentationCount(...) <= h_i + 2,
h_i := commonFaceDim(...),
```

then any feasible length-L checkpoint sequence with parent-vertex endpoints has
a parent edge/stay route of length `2*L`; intermediate checkpoints may be
nonvertices.

### Intrinsic excess <=3

`Solutions/PolynomialCarrierExcessThreeRouting.lean` is merged. Frozen source
`6552ca5edf585354b043e53d2e15218f59b9d688`, run `34630058450`, job
`103364397358`; 123 reports and only standard logical axioms.

It proves an arbitrary-parent carrier with `M_i<=h_i+3` has intrinsic diameter
<=3 and a feasible length-L sequence all of whose carriers satisfy that bound
routes in `3L` parent edge/stay steps.

### Variable exact small-excess budgets

This has now been strengthened and merged at main commit
`7066f047feb8929433861cd905e2eebfcf40d15a`:
`Solutions/PolynomialCarrierSmallExcessBudgetRouting.lean` gives exact additive
accounting. If step i has an equivalent common-carrier coordinate presentation
with row excess `R_i<=3`, its intrinsic graph cost is at most `R_i`, and the
whole feasible sequence routes in budget

```text
sum_i R_i.
```

The ambient parent may have arbitrary row excess and intermediate checkpoints
need not be vertices. Do not spend a stronger agent on another low-excess
routing wrapper.

## Fresh structural result: source vertexhood is no longer needed for circuit neutral rank

PR #108 is merged at commit `678b470e5dbc57e16295fca24b2b49dc6df86598`.
Frozen source `1922d706523c5253bbe32079e6e6ab71444b3538` passed run
`34630740596`, job `103366669600`; all 8,488 build jobs succeeded and the axiom
audit checked 20 reports with only the standard logical axioms.

For a bounded parent, feasible source `u`, and ambient row circuit `v-u`:

```text
neutral-row kernel = span(v-u)
neutral-row rank = d-1
neutral-row rank on commonDirection = commonFaceDim(a,b,u,v)-1.
```

No source-vertex or target-vertex hypothesis is required. Receipt:
`research/NONVERTEX_BOUNDED_NEUTRAL_RANK_VERIFICATION_2026-09-11.md`.

## Immediate next theorem: try the exact nonvertex minimum-presentation budget, with no correction terms

The current
`rowCircuit_commonFace_minSubpresentation_excess_defect` assumes the source is
a parent vertex and proves

```text
(M_min - h) + selectedNeutralDefect <= n-d.
```

A dependency audit after PR #108 suggests this exact statement may extend to a
merely feasible source in a bounded parent **without** source/target self-face
corrections.

Why this now looks plausible:

- the old vertex-dependent neutral-rank and `d<=n` steps have exact
  bounded/feasible replacements from PR #108;
- deleting zero-normal rows from a minimum subpresentation needs only zero
  feasibility, and zero common-face coordinates correspond to the feasible
  source `u`;
- the remaining lower bound `h<=M_min` can likely be obtained by applying
  `rows_ge_dimension_of_bounded` directly to the bounded, nonempty equivalent
  coordinate subpresentation, instead of proving zero is an extreme point.

The exact theorem shape and a step-by-step Lean decomposition are recorded in
`research/NONVERTEX_MIN_SUBPRESENTATION_EXCESS_PLAN_2026-09-11.md`.
Try this stronger theorem before weakening to a nullity-corrected variant.

## After that: true high-excess amortization bottleneck

For a circuit-walk carrier let

```text
h_i = commonFaceDim(...)
M_i = commonFaceMinSubpresentationCount(...)
e_i = M_i-h_i.
```

The routing portal handles every `e_i<=3` carrier at exact cost `e_i` (or any
certified row excess `R_i<=3`). Even a successful exact nonvertex resource bound

```text
e_i + defect_i <= n-d
```

will not alone solve Polynomial Hirsch, because `n-d` can be large and the
optimal-defect-completion diagnostics show scalar excess+defect can trade while
protected graph distances survive.

The global research problem is therefore to amortize **`e_i>3`** carriers using
an ordered/persistent resource: blocker/rank progress, persistent carrier/face
intervals, distinct-carrier charging, rank-sensitive low-excess children, or a
phase-reset invariant. The existing `17*n^3` circuit-walk construction already
supplies the polynomial circuit walk; do not rebuild that side.

## Anti-duplication / evidence discipline

At this snapshot PR #109 is packaging/public-composition work around the
small-carrier-excess theorem, not the structural frontier above. Search current
main/open PRs before starting new work.

Keep exact finite evidence, Lean kernel/axiom evidence, and Prove2Me
ACCEPTED/live-Proved status distinct. Avoid cyclic theorem-graph decompositions
and duplicate registrations/submissions. Credentials stay outside Git in
`PROVE2ME_API_KEY`.
