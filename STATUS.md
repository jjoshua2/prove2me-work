# Current Polynomial Hirsch frontier

Synchronized 2026-09-12 with GitHub, authenticated Prove2me 0.10.3, the 48 mission discussion posts preceding this continuation, and recursively expanded theorem dependencies. The original sync post is `70d168d1-f966-4904-86f3-0afd25766a50`; the #200 continuation is `313208d8-567e-42bf-b894-c33726ece3d8`; the accepted fixed-excess and verified #201/#202 update is `a993112b-01dc-4060-8a72-89dc4af633a0`.
Repository: `jjoshua2/prove2me-work`. Integration baseline main: `65dc76dd2a2e9cc01a3e0ae3f64464d4eebfbdd3` (after #200).
Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## What remains open

[Polynomial Hirsch](https://prove2.me/theorems/58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac) remains **Open**. All six curated milestones are **Proved**.

The live `open-leaves` endpoint reports one leaf:

**[Hirsch.common_face_diameter_of_dim_ge_six](https://prove2.me/theorems/87a8b4f4-8b58-4340-8cb9-5fd1b548d01e)**.

It asks for one pair of constants `C,k`, independent of all dimensions, bounding the ordinary-edge diameter of every nonempty common face of dimension at least six by `C*(n+d)^k`. Its open ancestors include the high-carrier and d>=4 circuit-to-edge refinement statements. The research bottleneck is still total ordinary-edge cost. The cubic circuit walk, Santos, and fixed-dimensional Larman specializations are already available.

The default `/graph` response is incomplete at this depth: it returned 22 nodes and omitted this leaf. Recursively querying `/decompositions` reached 51 theorem/definition IDs. Use the recursive audit and `open-leaves`, not a shallow graph image, to assess connectivity.

## Public results and work outside the root graph

The pre-submission Hirsch catalog contained 189 entries. **135 non-deprecated Proved results were outside the root's API-declared dependency closure; 108 were submitted by this account.** This includes classical milestones and other contributors, not just recent discoveries. Discussion links do not create proof dependencies.

The [complete inventory](research/HIRSCH_UNCONNECTED_RESULTS_2026-09-12.md) gives each theorem's ID, submitter, discussion membership and milestone status. The [machine-readable snapshot](research/verification/2026-09-12-sync/catalog-and-dependencies.json) preserves the traversal edges. The new deferred-cost theorem below is recorded separately from that pre-submission count.

Priority results to reuse:

| Ingredient | Public result | Missing connection |
|---|---|---|
| Target-tight outer with unique old vertex | [aa3abbb2](https://prove2.me/theorems/aa3abbb2-203b-41ab-86b6-f45ab734c57a), Proved | Bound the cost of restoring target-slack cuts |
| At most `n-d` target-slack rows | [804b7a8e](https://prove2.me/theorems/804b7a8e-0572-4407-a014-2d9f4aaa6f87), Proved | Count only the cuts actually used |
| Closed extreme faces with no shared parent vertex are disjoint | [28f797e1](https://prove2.me/theorems/28f797e1-c7bd-49fd-b3b5-570c22329bdc), Proved | Apply to nonneighbors on the same chosen shortest path |
| Common-carrier excess at most three gives that exact routing cost | [d42af13a](https://prove2.me/theorems/d42af13a-a00d-4a15-b22f-19abc4f49276), Proved | Establish a small-excess certificate for actual charged pairs |
| Independent low-excess row blocks give diameter `<=n-d` | [27737675](https://prove2.me/theorems/27737675-3725-4a3d-92d7-92a87e91031e), Proved | Supply actual factorization; arbitrary high-excess carriers need not factor |
| Ridge-visible access implies polynomial facet access | [f74dd52f](https://prove2.me/theorems/f74dd52f-586b-4923-b2c1-9b209d8dc3e2), Proved | Uniform ridge-visible access remains unproved |

A result belongs in the root graph when a valid checked reduction actually uses it and exposes any remaining hypothesis. Merely importing it or mentioning it in a discussion would not resolve its applicability to arbitrary carriers.

## Integrated progress through PR #194

- #188 chooses shortest/chordless region paths.
- #189 converts disjoint used cut faces into strict-row carrier savings.
- #190 counts at least `r-3` nonneighbors of each selected label.
- #191 and publication-only #192 establish public closed extreme-face disjointness. Submission `6821be01-40d1-4467-a385-7385c54b9f32` is ACCEPTED; the theorem is Proved. [Publication receipt](research/CLOSED_FACE_DISJOINTNESS_PUBLICATION_2026-09-12.md).
- #193 proves `local minimum-presentation excess + (r-3) <= n-d`. Maximum used support `r=n-d` forces each local carrier's excess to at most three.
- #194 retains the **same shortest mixed clipping path and actual cut portal pairs** in the clipping conclusion. Its exact verified source is integrated without the one-shot workflow. [Verification receipt](research/SIMULTANEOUS_CLIP_SHORTEST_PAIR_LEGS_VERIFICATION_2026-09-12.md).

The earlier chain and frozen receipts through #187 are retained in [the archived handoff](research/FRONTIER_THROUGH_PR187_2026-09-12.md).

## New result: select portal pairs before asking for local costs

Source: [PolynomialDeferredRegionCostsPublic.lean](Solutions/PolynomialDeferredRegionCostsPublic.lean).
Frozen source commit: `6db6759777606ad5c5243b716a4fe1ea59c80c8d`.

`Hirsch.shortest_region_path_with_deferred_pair_costs` first chooses a shortest, chordless region path and a duplicate-free list of portal pairs. **After those choices**, it quantifies over every routing graph and every cost assignment. Routes for only the listed pairs assemble with length at most the sum of their costs.

This fixes an interface obstacle in the next composition. The #194 statement has a universal `hFaces` premise: it asks for routes for every pair on every cut face before returning the chosen support. The new theorem exposes the geometry before local route obligations, so support-derived small-excess certificates can be applied without assuming bounds for unused pairs. The #194 theorem remains valid; the stronger interface is needed for this use.

Both the source and exact standalone `theorem solution` passed Lean and axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`. Prove2me theorem [ba2632b3](https://prove2.me/theorems/ba2632b3-1bec-43f9-8755-960e4b04936c), submission `59a4c70a-7584-4f2e-a429-23598e316dd8`, is **ACCEPTED**, and the live theorem is **Proved**. The [publication packet](research/publication_packets/deferred_region_costs/) preserves the exact statement, proof and receipts.

## Deferred clipping and maximum-support closure (PR #200)

The first two items of the previous handoff are now locally verified in
[integration PR #200](https://github.com/jjoshua2/prove2me-work/pull/200).
[Exact theorem scope and reproduction receipt](research/DEFERRED_CLIPPING_MAXIMAL_SUPPORT_2026-09-12.md). Merged [PR #197](https://github.com/jjoshua2/prove2me-work/pull/197) supplies the padded
route adapter. Merged [PR #198](https://github.com/jjoshua2/prove2me-work/pull/198) supplies the
projected clipping interface. This continuation preserves both interfaces and
adds the full geometric certificate, maximum-support assembly and residual theorem.

- [PolynomialDeferredClipping.lean](Solutions/PolynomialDeferredClipping.lean)
  returns a `DeferredClipCertificate` containing the shortest mixed path and its
  actual parent-vertex portal pairs **without any local route premise**. Its
  callback accepts routes only for the selected cut pairs and charges
  `D + sum(actual cut costs)`.
- [PolynomialMaximalSupportClipping.lean](Solutions/PolynomialMaximalSupportClipping.lean)
  applies #193 to those same selected pairs. With `e=n-d` and `r` used cuts,
  `r=e` forces each carrier's minimum-presentation excess to at most three.
  The small-excess theorem discharges every cut call, proving `D+3e`.
- [PolynomialTargetConeDeferredCosts.lean](Solutions/PolynomialTargetConeDeferredCosts.lean)
  obtains such certificates for every bounded H-polyhedron and vertex pair,
  with `D=1` from the target-tight compact star and `r<=e`. The maximum-support
  regime therefore has an actual ordinary-edge route of length at most `1+3e`.
- [PolynomialLowDimensionalCarrierRouting.lean](Solutions/PolynomialLowDimensionalCarrierRouting.lean)
  uses intrinsic Larman coordinates to discharge dimension-at-most-five
  carriers at cost `4n`. If each selected carrier has either dimension `<=5`
  or excess `<=3`, the route costs at most `1+(4n+3)e`.

The final theorem
`target_slack_quadratic_route_or_few_cut_high_dim_high_excess_carrier`
returns the same certificate and either that quadratic route, or `0<r<e`
with an **actual selected cut pair** whose common carrier has dimension `>=6`
and minimum-presentation excess `>=4`. The latter alternative does not assert
that a short route is impossible. It identifies what the present estimates
have not discharged.

The core adapters keep `SmallExcessHpolyBound` and `LarmanHpolyBound` as explicit
inputs. These match already-Proved platform theorems
[12426807](https://prove2.me/theorems/12426807-9602-4014-bd5e-c69fb43f4cb6) and
[68453b6b](https://prove2.me/theorems/68453b6b-bcef-4672-b877-d04e56527e3f)
at the committed Mathlib pin. This avoids importing local theorem placeholders;
the new core proofs use only standard logical axioms. These new assemblies are
**local Lean results**, not newly accepted platform theorem submissions.

## Exact selected degrees and all fixed support deficits (#201/#202)

The #201 candidate now compiles after two finite-cardinality elaboration fixes.
Its actual selected-pair estimate is `delta_i+r<=e+1+deg_S(i)`, where `e=n-d`.
The new `PolynomialSelectedRunBudgets.lean` proves the selected-run degree
identity and applies it to the SAME certificate, giving

```
sum(actual carrier excesses) + 2c <= r*(g+3),   r+g=e.
```

Here c counts selected-run starts on the chosen chordless path. In the regime
`g+deg_S(i)<=2` for each used cut, the existing small-excess theorem converts
this into an ordinary-edge route of length `D+(r*(g+3)-2c)`.
Empty support is included. [Full proof note](research/EXACT_SELECTED_SUPPORT_2026-09-12.md).

The independent #202 sources compile unchanged from
`4797a18206c63e761628e556d5ca4bd1eef3c169` and are preserved in #201's integrated
proof commit `117709458ec4b071dc846cd8443feea19ca2669b`. For an actual vertex-pair
carrier, they prove `2h<=M`, hence `h<=delta=M-h` and `M<=2delta`.
Consequently a dimension-at-least-six actual carrier has excess at least SIX.
An excess-four or excess-five carrier is not that high-dimensional obstruction.

Applying already-Proved Larman to the minimum intrinsic presentation closes
EVERY selected call at fixed support deficit, without a recursive diameter
premise or a selected-adjacency condition:

```
Route length <= D + 2*(g+3)*2^g*r.
```

Thus deficit one costs at most `D+16r`, and deficit two at most `D+40r`.
For target-rooted certificates D=1. These safe constants are not claimed optimal.
The route theorem uses Larman alone; the piecewise small-excess version also
uses the already-Proved excess-at-most-three input.
[Intrinsic carrier argument and cube stress test](research/SUPPORT_DEFICIT_INTRINSIC_BUDGET_2026-09-12.md).

A separate short classical proof in `PolynomialFixedExcessLarman.lean` uses
shared nonzero tight-row descent plus Larman to give
`DiamLE(P,2*E*2^(E-3))` whenever `n<=d+E`. It includes empty, degenerate,
redundant-row and zero-row descriptions. Its standalone platform packet and
verification receipts are under
[fixed_excess_larman](research/publication_packets/fixed_excess_larman/).
The general constant is exponential in E; this is not a uniform polynomial.

The standalone theorem is now **Proved** on Prove2Me:
[49576ed3](https://prove2.me/theorems/49576ed3-5185-4951-9215-43283ef6169e),
submission `cd24addc-446f-4d16-b814-85315057c98f` **ACCEPTED**.
Its checked dependency edges use Larman and facet reduction, both already Proved.
The new theorem remains outside the root's dependency closure; it is available
for real future reductions. The larger selected-run/clipping assemblies are
locally and GitHub-verified, not newly accepted platform theorem submissions.


## Next research work, in order

1. **Control the sum of costs for coupled carriers when support deficit grows.**
   Fixed-deficit cases and the deficit-one internal-run case are now closed.
   Work on the same selected pairs; avoid introducing whole-face bounds for
   unused pairs. Use the stronger size information `h<=delta` and `M<=2delta`.
2. **Find a joint potential or certified decomposition that handles products.**
   The cube family in #202 rules out forcing logarithmic deficit for every
   shortest certificate: target-slack face labels form a clique, so at most two
   occur on a chordless path and `g>=d-2`, despite actual diameter d. This is a
   mathematical counterexample with finite checks, not a Lean-formalized cube
   theorem. Any proposed potential must pass this stress test. The existing
   product-route theorem is useful only when actual factorization is supplied.
   Endpoint savings still permit an exponential independent-call majorant;
   they are not evidence for an exponential polytope diameter.
3. **Connect a uniform total-cost bound to the root by a checked reduction.**
   The current bound is exponential in growing g. It does not prove the open
   leaf, and discussion links do not create root dependencies. Publish reusable
   established consequences with their real inputs, while keeping any missing
   geometric condition explicit. Do not add a cosmetic or cyclic graph child.

The ridge-visible line is a complementary research direction. Its proved small-row thresholds and known pivot-collision obstruction are recorded in the mission discussion and inventory. Numerical examples support investigation but do not establish a uniform access theorem.

## Verification and continuation

The #201/#202 integration passed
`lake build Solutions.PolynomialSelectedRunBudgets Solutions.PolynomialFixedExcessLarman`.
Its audit checks 30 required declarations and 406 reports across dependencies,
all with standard logical axioms. Both finite checkers passed again; fresh
receipts hash the current source, while original candidate receipts are
preserved as history. See
[verification/2026-09-12-exact-support](research/verification/2026-09-12-exact-support/).
The standalone explicit-premise fixed-excess driver also passes its own audit;
local typechecking of public composition uses exact theorem interface stubs.
The subsequent authenticated server verdict accepts that composition. The single
final [hosted verification run](https://github.com/jjoshua2/prove2me-work/actions/runs/34708143326)
on source `117709458ec4b071dc846cd8443feea19ca2669b` also passed, with the same
30 required declarations and 406 standard-axiom reports.

The earlier #200 continuation passed `lake build Solutions.PolynomialTargetConeDeferredCosts` and the standard-axiom audit for all 15 new/adapter/projection declarations (375 reports checked across dependencies). Exact hashes and logs are under [verification/2026-09-12-deferred-clipping](research/verification/2026-09-12-deferred-clipping/). The previous targeted build also passed for the integrated shortest-clipping module, chordless carrier tradeoff, and minimum-carrier routing. The new standalone theorem has its own clean axiom audit. Full evidence is under [verification/2026-09-12-sync](research/verification/2026-09-12-sync/).

[Integration PR #195](https://github.com/jjoshua2/prove2me-work/pull/195) preserves completed #192 publication receipts and the exact #194 theorem while excluding both temporary workflows. It supersedes both completed PRs; no historical experiment remains part of the active work queue. Do not reopen their old experiments as active work.

Do not equate circuit steps with edges, replace a uniform polynomial by Larman/Kalai–Kleitman, infer low excess or factorization without certificates, or create circular reductions through an open ancestor.
