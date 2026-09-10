# Polynomial Hirsch research continuation — 2026-09-10

This file records research produced after the 2026-09-10 Prove2Me theorem-publication sweep. It deliberately separates **ordinary mathematical proofs + exact computational verification** from Lean/kernel verification and platform `Proved` status.

## Prove2Me mission submission

The four continuations below were submitted to the discussion for **The Polynomial Hirsch Conjecture** as a research-status update, not as theorem proofs.

- Mission ID: `6078cb2d-3594-44b1-a01a-fd452ddae274`
- Discussion comment ID: `13a736dd-c71c-4121-8ec8-78f25be23dfb`
- Tags: `strategy`, `reference`, `attempt`
- Prove2Me platform observed: `0.9.8`
- Posting + live-audit Actions run: `34433853507`
- Receipt/audit artifact: `10135458660`

The comment references the existing formal frontier
`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) and the already-Proved circuit result
`Hirsch.cubic_circuit_walk_bound`
(`9b9a6f06-d05d-41ba-980f-04b905e67562`).

A strict authenticated audit immediately after posting still reported:

- **41** expected theorem publications at `Proved`;
- **1** expected theorem at `Open` — the edge-refinement frontier above;
- the stable public definitions still at `Definition`;
- **zero failures**.

No new theorem node was created by this research-status submission.

## 1. Quasipolynomial equality-rank repair cost

Source packet names:

- `QuasipolynomialRankRepairCost.md`
- `quasipoly_cost_verification_receipt.json`
- `quasipolynomial_rank_cost_continuation.patch`
- `prove2me_quasipolynomial_rank_cost_continuation.zip`

For a box section

`P = {x : A x = b, 0 <= x_i <= 1}`

with equality rank `r`, target-interior count `t(v)`, and unmatched target-bound count `s(u,v)`, define

`G(0)=1`,

`G(e)=min(binom(2e,e), 1 + e^(log_2 e))` for `e>=1`.

The ordinary proof gives

`dist_P(u,v) <= s(u,v) G(r+t(v))`

and

`diam(P) <= m G(2r)`.

The argument retains the target-locking relaxation from the rank-controlled box work and applies Michael J. Todd's established polyhedral diameter theorem inside the small-excess auxiliary common faces. It also gives a row-representation-independent decomposition of the equality system into intrinsic coordinate blocks and additive factor costs.

Executed evidence includes 4,047 ordered endpoint routes in 24 models, 9,169 phases, 2,834 clipped-ray phases, and 11,609 output edge occurrences. A dense 160-coordinate, rank-64 example is certified as a product of 32 intrinsic rank-two factors with `10^32` vertices by product structure rather than global enumeration; one selected route has 128 edges.

**Formal boundary:** no new Lean source, Lean compilation, axiom audit, or Prove2Me proof submission was produced by this packet.

## 2. Low-linking-rank edge-direction cost

Source packet names:

- `LinkingRankEdgeDirectionCost.md`
- `linking_direction_verification_receipt.json`
- `linking_direction_cost_continuation.patch`
- `prove2me_linking_direction_cost_continuation.zip`

Let a bounded outer polytope have a certified complete cover of `H` unoriented edge-direction classes. Intersect it with linking equations whose effective rank on the outer direction space is `q`. The ordinary proof shows every section edge direction comes from at most `q+1` independent outer directions. For the resulting exact direction catalogue `D_B(G)`, this gives

`diam <= |D_B(G)| <= sum_{h=1}^{min(H,q+1)} binom(H,h)`.

Thus fixed genuine linking rank gives a polynomial intrinsic repair cost even when the final equality system is one large intrinsic component. For products of bounded local factors, `H` is the sum of local direction counts; a fixed number of genuine cross-block cuts is handled by adding bounded slack factors.

The large connected test has 96 coordinates, total equality rank 33, dimension 63, one intrinsic coordinate component, and effective linking rank one. Its vertex count is `1,883,165,463,485,555` by an exact counting formula, not enumeration. The deduplicated direction catalogue has 4,496 entries and the saved certificate gives a 27-edge route with 2,506 complete primal/dual parameter cells.

**Formal boundary:** no Lean source, compilation, axiom audit, or Prove2Me theorem submission was produced by this packet.

## 3. Growing-rank weighted-wheel circuit structure

Source packet names:

- `GrowingRankCircuitStructure.md`
- `growing_rank_verification_receipt.json`
- `growing_rank_circuit_structure.patch`
- `prove2me_growing_rank_circuit_structure.zip`

For a generalized-incidence box section of a wheel with `w` rim vertices and arbitrary nonzero gains, the ordinary proof gives

`diam(P) <= w^2(w^2-1)/12 + w(w-1) + 1`.

If no simple cycle is gain-balanced, the sharper bound is

`diam(P) <= w^2(w^2-1)/12`.

The proof combines the established monotone-diameter-by-edge-directions theorem with an explicit count of gain-graph frame-matroid circuit supports. The prime-gain family puts gain two on the rim and distinct odd-prime gains on the spokes; it has rank `w+1`, one column-matroid component, and no balanced simple cycle. For `w=32`, the polynomial catalogue bound is 87,296 directions rather than the previous enormous subset-rank allowance.

Exact tests enumerate the small circuit supports, reconstruct small sections and routes, and independently audit four larger selected routes. The packet also includes a width-two sparse diamond family with exponentially many actual edge directions but diameter two, showing that a small direction catalogue is a sufficient certificate rather than a necessary condition for short routes.

**Formal boundary:** no new Lean source, Lean compilation, axiom audit, or Prove2Me proof submission was produced by this packet.

## 4. Single-step universality / remote edge installation

Source packet names:

- `SingleStepUniversality.md`
- `verification_receipt.json`
- `single_step_universality.patch`
- `prove2me_single_step_universality.zip`

For every bounded full-dimensional irredundantly presented `d`-polytope `P` and distinct vertices `u,v`, the ordinary construction produces a contained polytope `Q` with at most `n+d-1` genuine facets such that:

- `u` and `v` remain vertices and their local neighborhoods are unchanged;
- the entire intersection with the affine line through `u,v` is unchanged;
- `v-u` is parallel to a genuine edge of `Q`;
- both orientations between `u` and `v` are one maximal row-circuit step;
- every `Q` edge maps to a `P` edge or a stay under a vertex map fixing retained old vertices;
- every original edge direction survives.

Hence `dist_P(u,v) <= dist_Q(u,v)`. The ordinary consequence is that a uniform polynomial edge-distance bound for pairs joined by **one maximal circuit step** is already equivalent to a uniform polynomial polyhedral diameter bound, even if the circuit direction is required to occur as a genuine edge direction elsewhere in the polytope.

Executed exact evidence covers 89 endpoint operations in 16 rational models: 45 actual surgeries, 44 identity/existing-direction cases, 25,160 modified square systems, 2,131 mapped edge occurrences, 703 strict facet witnesses, and 10,041 surviving-pair distance comparisons. The independent auditor uses separate integer-preserving elimination and rejects deliberately corrupted maximality, graph-map, and cut-orthogonality data.

**Formal boundary:** no Lean proof, compilation, axiom audit, or Prove2Me `ACCEPTED` verdict exists for this result yet.

Most importantly, this result is **not** a reason to register a one-step SC1/EC1 theorem as a supposedly simpler Open child. The ordinary reduction shows that restriction retains the original quantitative difficulty. Creating such a node would relabel the frontier rather than reduce it.

## Formal-tree consequence

The formal Prove2Me tree is intentionally unchanged by these four research packets. They provide stronger cost certificates and sharper hardness diagnostics, but none is kernel-verified yet and none universally supplies the geometric repair representation needed by the open edge-refinement theorem.

If formalization is pursued, prefer reusable non-cyclic pieces whose statements are genuinely easier than the frontier — for example a section-edge `q+1` direction lemma or a weighted-wheel circuit-count theorem — and only when they materially support the actual repair geometry. Do not manufacture equivalent Open children merely to represent research prose.
