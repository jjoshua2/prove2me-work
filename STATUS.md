# Current Polynomial Hirsch frontier

Synchronized 2026-09-12 with GitHub, authenticated Prove2me 0.10.3, all 46 existing mission discussion posts, and recursively expanded theorem dependencies. The new progress post is comment `70d168d1-f966-4904-86f3-0afd25766a50`.
Repository: `jjoshua2/prove2me-work`. Baseline main: `59be0de0447b23d257aee2e3f04ac3f4b1872e1f`.
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

## Next research work, in order

1. **Thread deferred local costs through simultaneous clipping and the target-cone specialization.** Return the shortest mixed path and actual parent-vertex portal pairs without `hFaces`; provide a callback accepting routes only for those pairs. Preserve the current old-edge charge `D` and endpoint lift cost. The new generic theorem is the assembly primitive.
2. **Close the maximum-support regime with an end-to-end route theorem.** On that same path let `e=n-d` and `r` be the number of used cuts. When `r=e`, #193 makes every charged carrier's excess `<=3`. Instantiate the public small-excess theorem and sum actual costs. The immediate safe target is `D+3e`; the sharper `D+3e-2` requires a separate exact neighbor-count sum and the zero-support boundary case. Neither total bound is claimed proved here.
3. **Attack few-used-cut, coupled high-excess carriers.** For `r<=3`, the present inequality gives no strict excess decrease. Even `r=4` allows four subcalls of excess `e-1`; iterating the corresponding independent-call majorant can grow exponentially. A global potential/charging argument, stronger separation, or a certified block decomposition is still required for a fixed-degree polynomial. This is a limitation of the current bound, not an exponential lower bound for polytope diameter.

The ridge-visible line is a complementary research direction. Its proved small-row thresholds and known pivot-collision obstruction are recorded in the mission discussion and inventory. Numerical examples support investigation but do not establish a uniform access theorem.

## Verification and continuation

Local targeted build passed for the integrated shortest-clipping module, chordless carrier tradeoff, and minimum-carrier routing. The new standalone theorem has its own clean axiom audit. Full evidence is under [verification/2026-09-12-sync](research/verification/2026-09-12-sync/).

[Integration PR #195](https://github.com/jjoshua2/prove2me-work/pull/195) preserves completed #192 publication receipts and the exact #194 theorem while excluding both temporary workflows. It supersedes both completed PRs; no historical experiment remains part of the active work queue. Do not reopen their old experiments as active work.

Do not equate circuit steps with edges, replace a uniform polynomial by Larman/Kalai–Kleitman, infer low excess or factorization without certificates, or create circular reductions through an open ancestor.
