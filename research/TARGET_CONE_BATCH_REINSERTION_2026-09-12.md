# Target-cone batch reinsertion with final parent-face budgets

Date: 2026-09-12. Research PR #168.

Status of this explanatory note: ordinary proof and exact regressions complete;
consult the companion verification receipt for the kernel gate's result.
No Prove2Me submission is made by this branch.

## Statement

Let P = {x : <a_i,x> <= b_i} be a bounded finite H-polyhedron and let v be
one of its vertices. Let J be exactly the rows strictly slack at v. For each
j in J, assume an ordinary parent-edge/stay route of length B_j between any
two parent vertices on the final row face F_j = P intersect {<a_j,x> = b_j}.
These replacement routes may leave F_j; an intrinsic face-diameter hypothesis
is not required.

Then the new interface proves:

- every parent vertex u is reachable from v in at most 1 + sum_{j in J} B_j
  ordinary edges (encoded as a padded edge/stay route);
- the parent has diameter at most 2 + sum_{j in J} B_j.

The second bound is obtained by one simultaneous repair, NOT by concatenating
two rooted bounds and charging the face sum twice.

## Proof architecture

1. Keep exactly the inequalities tight at v. PR #165 proves that their row map
   is injective and their outer Q0 has extreme-point set {v}. Q0 can be unbounded.
2. Use the explicit negative-row-sum functional on the retained rows. Its finite
   cap is bounded by the already-verified injective-cap theorem. Choose the cap
   level strictly above all of P; this preserves every parent point.
3. The existing compact single-cap classification makes each capped vertex
   either the old vertex v or a vertex adjacent to an old vertex. Since the
   only old vertex is v, every other capped vertex is genuinely adjacent to v.
   Hence the capped outer Q has rooted cost 1 and graph diameter at most 2.
   No auxiliary cap-cap chord is treated as a graph edge.
4. Reinsert all J at once. Since the cap contains P, the final clipped set is
   exactly P. Since each J row is strictly slack at v, v is the required common
   strict centre for the radial retraction. Other original vertices may have
   disappeared from Q0; compact endpoint lifting accounts for their creation.
5. The retracted trace is covered by final cut faces, surviving clipped outer
   edges, and endpoint singleton regions. Genuine shared parent-vertex portals
   connect these regions. Erasing repeated region labels charges each face
   once. Its local route may leave the face because the assembly uses the
   ambient parent adjacency relation throughout.
6. A two-edge outer route gives the diameter bound 2 + sum B_j. Choosing v
   itself as one lifted endpoint and a one-edge root route gives 1 + sum B_j.

## Exact scope and what remains

This supplies the simultaneous batch-repair step missing after #165, with
constant outer cost. It does not prove that the remaining face sum is uniformly
polynomial. A replacement budget obtained recursively in one lower dimension
may still generate a rapidly growing recursion tree. Counting each face once
at ONE level is not the same as global amortization across ALL levels.

The original parent is bounded. Only its target-tight outer is allowed to be
unbounded in this theorem. An arbitrary partial batch of target-slack rows need
not leave a target-only outer and is not covered by the star claim.

All final face-route hypotheses remain explicit. Using the unknown parent
diameter itself to choose B_j would be valid but circular for an attempted
polynomial proof. The unresolved task is to produce smaller, independently
justified budgets or a weighted cover whose total cost is globally controlled.

## Reusable declarations

`Solutions/PolynomialSimultaneousClipParentRoutes.lean`:

- HirschRadial.route_clip_of_lifted_endpoints_with_parent_routes
- HirschRadial.diamLE_clip_of_strict_centre_with_parent_routes
- HirschRadial.route_clip_from_root_with_parent_routes

`Solutions/PolynomialTargetConeBatchReinsertion.lean`:

- HirschTargetDeletion.compact_cap_star_of_unique_vertex
- HirschTargetDeletion.diamLE_two_of_vertex_star
- HirschTargetDeletion.exists_compact_star_cap_of_target_tight_selection
- HirschTargetDeletion.target_slack_batch_reinsertion_with_parent_routes

## Reproduction and finite controls

Run:

    python3 scripts/check_target_cone_batch_reinsertion.py
    lake build Solutions.PolynomialTargetConeBatchReinsertion

The deterministic Fraction regression covers 23 fixtures, 99 target vertices,
297 cap constructions, 1,041 capped vertices, 744 apex edges, 285 final-face
budget calculations, and 412 lost-original-vertex occurrences. Fixtures include
nonsimple 3D polytopes, lower-dimensional presentations, a singleton, dimension
zero, redundant/zero rows, translations, and positive row scalings near 10^20.

The exact report digest is
`3106dc044009131b5a0e4ee781e1cbf8288fdab4ff348fcd2d0a27cebcd89fa3`.

Negative controls show that a cap failing to contain P changes the recovered
polytope, and that retaining some target-slack rows can destroy the target-star
property. These are explicit assumption checks, not counterexamples to the
stated theorem. Finite tests supplement rather than replace kernel verification.
