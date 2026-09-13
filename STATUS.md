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

The companion [PR #199](https://github.com/jjoshua2/prove2me-work/pull/199)
retains the exact abstract cost `D + sum(local minimum-presentation excesses)`
and its `D+3e` bound under maximum support. Its initial hosted compile failed
on an undefined cut-leg type; the corrected `RegionLeg` version passed local
Lean and the standard-axiom audit. [Exact-cost receipt](research/MAXIMAL_CUT_SUPPORT_EXACT_COST_VERIFICATION_2026-09-12.md).
This exact-cost companion is preserved alongside the stronger continuation below.

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


## Projectively hidden products (#203)

PR #203's segment-chart, positive-perspective, and projective row-block modules
now compile. The targeted local build and single final hosted run
[34710879303](https://github.com/jjoshua2/prove2me-work/actions/runs/34710879303)
pass on frozen proof source `6cd06d52fa4bbd832d8eae1eddd85ded9f0bfec9`.
All 15 required declarations and 28 total reports contain only standard
logical axioms. The original rational regression counts pass unchanged.
[Proof and scope](research/PROJECTIVE_HIDDEN_PRODUCTS_2026-09-12.md).

The map `x/(1+c·x)` explicitly preserves segments, extreme subsets, vertices,
and ordinary edges on its positive domain. The inverse and row-slack identities
are proved, not assumed. A new wrapper consumes both nonnegative-row-multiplier
certificates and preserves a known ordinary-edge budget without extra steps.
Together with independent small-excess source blocks, this gives `DiamLE(Q,n-d)`
for the sheared rows `a'_i=a_i+b_i*c`, with no bound on total excess or deficit.

The full finite-certificate criterion is now **Proved** as
[Hirsch.hpoly_diameter_le_excess_of_projectively_hidden_small_row_blocks](https://prove2.me/theorems/b6289eea-78b3-4bcf-a5d7-65fbab46a986).
Submission `84cf11d7-d965-41c3-96b6-d0f108e8ce2e` is **ACCEPTED**.
Authenticated source readback matches the packet byte-for-byte. Mission update
`940e9078-b248-4385-afa7-2f60bab07663` links the theorem, accepted solution,
its actual row-block input, and the still-Open leaf.
Its exact public input is the already-Proved row-block theorem
[27737675](https://prove2.me/theorems/27737675-3725-4a3d-92d7-92a87e91031e).
[Standalone packet and receipts](research/publication_packets/projective_small_blocks/).

The projective cube family has connected affine row normals and still has
shortest-repair deficit at least d-2, despite diameter d. Therefore affine
indecomposability together with large deficit does not identify hard routing.
The generic transport and finite certificate criterion are Lean-verified;
the unbounded family's matroid/deficit/lower-diameter description remains a
mathematical argument with exact finite checks, not separate Lean declarations.

## Recursive chart discovery and additive product trees (#204)

Merged PR #204 supplies the next continuation. Its original two Lean modules compile
unchanged against merged #203. Frozen verified source
`fcbb02425dececaa9a8f7abd90c341ae99dbafac` extracts the geometric `ProductTree`
into a standalone definition. Seven required declarations and 272 transitive
reports pass the local standard-axiom audit. The independent recursive proof
packet and exact public composition also compile locally.

An exact rational discovery procedure now recovers charts from homogeneous
row bipartitions. It derives source balance and both denominator certificates
from a supplied strictly interior point, positive target normal balance and an
exactly searched dual witness. It then recursively splits factors using distinct
charts at different nodes. Products add costs and charts preserve them, giving
`DiamLE(P,n-d)` whenever the resulting finite geometric tree is complete.
For the SAME actual selected clipping pairs, equivalent intrinsic trees using
at most n rows imply a route at cost `D+n*r`. The small-excess input is explicit
in the local Lean induction and is already Proved on the platform.

The triangular interval towers in the proof note are routed recursively even
when no single chart exposes only excess-at-most-three factors. The full
recognition-completeness and infinite-family arguments are mathematical proofs
in that note; they are not all formalized Lean theorems. The JSON verifier
checks rational identities and does not emit Lean proof terms. Fresh tests pass
32 positive certificates, 2,720 ordered graph distances and 15 negative controls.
The cyclic four-/five-dimensional examples have cube graphs but no homogeneous
separator and are correctly left unresolved by this detector.

The geometric definition is published as
[3c29c70d](https://prove2.me/theorems/3c29c70d-337c-4d63-8f52-9c437f52e878).
The [recursive routing theorem](https://prove2.me/theorems/4afd7668-51a9-4a5e-a991-2a02c53b9e1c)
is **Proved**, with **ACCEPTED** submission
`7f2bba60-85ad-42d5-8a1a-eed656add3f5`. The exact accepted source and definition
match the frozen packet. Mission update `34e388c1-afb6-412e-85c0-366096816186`
links the accepted proof and its real small-excess/definition dependencies. Consult
[the packet](research/publication_packets/recursive_projective_products/).
[Proof and precise boundaries](research/RECURSIVE_PROJECTIVE_DISCOVERY_2026-09-12.md).
The final [hosted run 34712133611](https://github.com/jjoshua2/prove2me-work/actions/runs/34712133611)
passes the same seven required declarations and 272 standard-axiom reports.
The root conjecture and high-dimensional common-face leaf remain Open.

A further [paper proof for contractive feedback boxes](research/CONTRACTIVE_FEEDBACK_BOXES_2026-09-12.md)
now routes `0<=x<=b+M*x` in d ordinary edges when M>=0, b,w>0 and M*w<w.
It classifies vertices by their active coordinate choices and toggles one choice
per edge. The cyclic family has no projective product split in d>=3; for d>=4
it lies outside recursive small-excess product trees. This is a mathematical
result with finite regression evidence, **not yet a Lean or accepted platform
theorem**. Twelve rational examples pass 4,080 ordered routes and four invalid
witness controls. Formalizing its vertex/edge classification is the next task.

## Historical research priorities through #204 (see latest integrations below)

1. **Control the sum of costs for coupled carriers when support deficit grows.**
   Fixed-deficit cases and the deficit-one internal-run case are now closed.
   Work on the same selected pairs; avoid introducing whole-face bounds for
   unused pairs. Use the stronger size information `h<=delta` and `M<=2delta`.
2. **Find a joint potential or certified decomposition that handles products.**
   The cube family in #202 rules out forcing logarithmic deficit for every
   shortest certificate: target-slack face labels form a clique, so at most two
   occur on a chordless path and `g>=d-2`, despite actual diameter d. This is a
   mathematical counterexample with finite checks, not a Lean-formalized cube
   theorem. Any proposed potential must pass this stress test. The projective extension also handles factorization hidden by a positive chart;
   the #204 continuation now searches charts and recursively exposes factors.
   Neither affine normal connectivity nor failure of the projective separator
   search is a diameter lower bound. Formalize the contractive-feedback
   active-choice vertex and edge lemmas next, then connect equivalent models
   to the actual selected carriers. Arbitrary carriers need a joint cost
   argument beyond the known product and feedback classes. Search is finite but exponential in
   the worst case; capped failure is not geometric nonexistence.
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

## Coupled positive-feedback boxes (#205)

All three modules are locally compiled and transitively standard-axiom audited;
final hosted run `34723396993` passed on `163caecb77418e3bd998e0b225f8685d45dc7139`.
The direct matrix criterion `C>=0`, `b,w>0`, `Cw<w` gives actual ordinary-edge
diameter at most the dimension. The image adapter routes the same selected
carriers at cost `D+sum(h_i)`. No dimension cap or Larman premise is needed.
[Precise verification and fixture boundary](research/COUPLED_BOXES_DELIVERY_2026-09-12.md).
The four original Python sources were absent; the committed independent verifier
checks the supplied examples and does not claim to rerun their historical suite.

The standalone public theorem is `4096cd8a-6bf6-4788-89be-e67f84f6c92f`.
Submission `05df606c-7c8c-42eb-9e69-794b6be48926` is **ACCEPTED**; the
authenticated theorem status is **Proved**, and accepted-source readback matches
the frozen solution hash. #205 is merged at `e1e8b9edb23b88f10bf3ead6ee3fd704f121efe5`.
PR #206 is the active all-row joint
mass continuation. PR #207 is the distinct portal-debt/near-geodesic draft;
its new Lean sources and the missing geometric adapters remain to be verified.

## Joint all-row carrier mass (#206)

All four new modules compile locally. All twenty required declarations pass
transitive axiom audits; the exact suite reruns 1,099 graphs, 148,126 incidence
audits, 26 geometric instances, 61 actual carriers, and eight negative controls.
The unchanged matrix-independent geometric inequality is
`sum(delta_i)+r*s <= r*(n-d)+3*s`, hence `sum(delta_i)<=3e` at `s=e`.
The supplied target-tight basis and separate strict center give an actual
D=1 certificate with s=e, including nonsimple targets. Intrinsic dimension
and row mass are <=3e and <=6e. An actual carrier dimension cap H gives
`D+6e*2^(H-3)`, or `D+24e` for H<=5, with explicit Larman input.
[Exact scope](research/GEODESIC_ALL_ROW_MASS_2026-09-12.md).

Final hosted run `34723720395` passed at `8e4a666f9bc54c64ff38f93223a965c6181751b6`,
with all twenty required axiom reports. The graph-only joint-budget theorem
[b8f45079](https://prove2.me/theorems/b8f45079-9784-43a0-b659-0914a2038332) is
**Proved**, submission `83ed9045-971b-4ad8-ae0d-3659c625e850` **ACCEPTED**.
The accepted source matches the frozen packet. The actual geometric adapters
have local/hosted verification, not their own platform verdict.
Basis extraction and combining feedback carriers with the mass bound are now
locally verified in #209 below. #207 remains the separate portal-debt and
near-geodesic draft. New #208 develops additive-spill route trees and a detour
mass bridge depending on #206/#207; its Lean verification and complete geometric
existence wrapper are outstanding. Neither conditional recurrence closes Hirsch.

## Automatic target bases and linear mixed carriers (#209)

The three new modules and all eight printed declarations pass local compilation
and transitive standard-axiom audits. Frozen source:
`7ffa3fb3cede303c579164245f01286a49351b15`.
[Proof and exact boundary](research/AUTOMATIC_BASIS_LINEAR_FEEDBACK_2026-09-12.md).

- Every extreme point supplies d distinct original tight rows with injective
  row evaluation, without simplicity, boundedness, or a supplied basis.
- With boundedness and a separate strict interior point, the basis-star
  certificate is now obtained automatically with D=1, s=n-d and total actual
  carrier excess <=3(n-d), before any route/model callback.
- Feedback carriers, optionally mixed with excess<=3 carriers, give 1+3(n-d).
  Feedback carriers mixed with dimension<=5 carriers give 1+24(n-d).
- The same automatic certificate gives the latter route or an actual selected
  carrier of dimension>=6 without a PositiveBoxImage model. This identifies an
  unresolved sufficient-criterion case, not a diameter lower bound.

Final hosted run `34724365226` passed at
`43ab319f30d698105ed878e0ae9b5cc82ef8cedd`, with eight required and 414 total
standard-axiom reports. The standalone classical basis theorem
`e46935cf-6286-4874-a742-01cc62269b2d` has submission
`63c8d2b9-2c24-4c59-9c3a-6769a095f63e` **ACCEPTED**. Authenticated theorem
readback says **Proved**, and its accepted source matches the frozen packet.
All final gates for integration #209 have passed. The basis
publication is not a platform verdict for the larger clipping assemblies.
The active queue after this integration should contain only #207 and #208,
with their distinct blockers and next local compile commands in their bodies.
The root and sole leaf were refreshed by authenticated API and remain Open.

Mission update `0ab0273f-42de-4318-b53d-0bfa4e33160f` links the accepted
#205/#206/#209 public theorems and distinguishes the larger Lean assemblies.
The new results are listed separately from the inventory's historical counts.
No root dependency was added without a checked reduction proving applicability.

## Verified portal debt and near-geodesic windows (#207)

All three modules compile and all 13 required declarations pass local/hosted
standard-axiom audits. Frozen proof `35dc985`; final hosted run `34725296903`
passed at `63725a915769acae1c31c554335ac8b633606d14`. The exact portal-debt,
independent audit, and amplified-family suites were rerun successfully.
The public occurrence-counted budget theorem
[79bdd301](https://prove2.me/theorems/79bdd301-35e1-4cdb-a6ed-eb49b00e5c3c)
is **Proved**, submission `1ede1000-2a0d-4d98-8736-1a828626eb2f` **ACCEPTED**.
The accepted source matches the frozen packet. It allows repeated labels and
bounds resource mass by (q+3)e at full availability. The finite-set and edge-tree
debt invariants are also Lean-verified; the full simple-polytope identification
and infinite geometric family are not silently upgraded to platform theorems.

#209's basis theorem e46935cf-6286-4874-a742-01cc62269b2d was rechecked live and
remains Proved; no duplicate submission was made. #208 is being integrated from
its continued head 9fdbed3e5c8fea05ccb0a14ef5902ac6d05c7f0b, including the cyclic
fixed-slack obstruction and explicit adaptive routes. Its final verification
and publication states are recorded by the next integration. The next geometry
must permit input-dependent portal chains or separately solve easy high-excess
calls; fixed slack is not a viable universal premise in #208's specified family.


## Additive spill, adaptive portals, and submission closure (#208)

The continued #208 source is frozen at `b7a832e9ff98743d53c66d6e471fd0828891d22d`. All six modules compile locally and in final hosted run [34725721217](https://github.com/jjoshua2/prove2me-work/actions/runs/34725721217), at `418e7a4158b54212a43df0bec9b11e40506066da`. Both audits check all 20 required declarations and 291 standard-axiom reports. Both exact regression suites were rerun after the elaboration repairs and pass. Final source hashes match. [Durable verification](research/verification/2026-09-12-additive-spill/).

The public conditional theorem `Hirsch.additive_portal_repair_polynomial_route`, `32dbbfe9-bd4c-4685-8df6-7a4403175ef4`, uses the published finite repair definition `be8f4ff8-23bd-4894-a523-ab6271d326f0`. Submission `2a2dd9bd-9ee5-43fa-bc04-def26a5a2a98` contains the frozen proof. Its authenticated PENDING receipt is preserved in [the packet](research/publication_packets/additive_portal_repair/).

Given a finite repair tree with actual leaf routes, strictly decreasing dimensions, nonincreasing child excess, sibling excess sum at most e+b, and leaf cost at most C*e, the theorem produces an actual route and bound C*e+(1+b*C)*h*(e-b). Geometric existence and interpretation of the numerical tags remain explicit premises.

The complete infinite fixed-slack cyclic obstruction and adaptive block-slide construction are mathematical-note results with exact finite tests; their transport and supporting-kernel cores compile, but not every step of the infinite argument is formalized. The obstruction concerns the specified first-original-edge/available-facet family, not all radial-cap constructions or actual shortest distance. It rules out universal fixed slack within that family; input-dependent long but cheap portal chains remain a legitimate next target.

This section supersedes earlier candidate/draft statements for #207/#208. #207 is merged and its near-geodesic budget is Proved; #209 is merged and its basis-extraction theorem remains Proved without resubmission. The larger geometric adapters have their own local/hosted verification, distinct from these public theorem verdicts. The authenticated root and high-dimensional common-face leaf remain Open. No cosmetic or cyclic dependency was added.

Publication checkpoint: #208 proof submission is PENDING. Keep #208 draft and poll submission `2a2dd9bd-9ee5-43fa-bc04-def26a5a2a98`; do not resubmit. Local and final hosted gates have passed.

Mission synchronization: comment `cc1cb374-56df-4478-8345-ac6810ee08b5` records #207/#209 acceptance and #208 pending proof verification, with eight resolved theorem/definition/solution references and exact readback. #208 is the sole open PR and deliberately remains draft pending that platform verdict. Next action: from the authenticated workspace, run `PYTHONDONTWRITEBYTECODE=1 python3 scripts/publish_self_contained_packet.py --packet research/publication_packets/additive_portal_repair poll-verify`; after ACCEPTED, preserve accepted-source readback, update the existing mission comment, and merge the exact verified PR head. No new submission is needed.
