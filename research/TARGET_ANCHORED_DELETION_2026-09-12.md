# Target-anchored batch deletion

Date: 2026-09-12. Continuation of PRs #163 and #164; source in PR #165.

The Lean verification outcome and frozen provenance belong in the companion verification receipt. This note explains the mathematics and its exact scope; finite regression is not a substitute for a Lean kernel result. No Prove2Me acceptance is claimed here.

## Fix a target vertex rather than a current circuit checkpoint

Let P={x : <a_i,x> <= b_i} be a finite H-presentation, and fix v in its extreme-point set. No boundedness, strict feasibility, irredundancy, or full-dimensionality hypothesis is required.

Let J be any finite set of rows strictly slack at v. Delete every row in J. All rows tight at v remain, and those rows span the ambient direction space by `vertex_tight_rows_span_checked`. Consequently:

- the remaining row map is injective, so the relaxed outer is pointed;
- v is still an actual vertex of that outer;
- exactly n-|J| rows remain after canonical finite reindexing;
- reinserting J recovers P exactly.

The preservation of a vertex is stronger than preservation of a feasible point. If v lies strictly between two points feasible for the retained rows, every target-tight row is also tight at both endpoints. Their difference from v is annihilated by all original active rows; the checked vertex-kernel theorem forces equality.

The choice of J may be made all at once. Pointedness does not need to be re-established using a new circuit certificate at each deletion.

## Same-phase exceptional branch disappears

PR #163 proves that an arbitrary maximal circuit step admits either pointed blocker deletion or a row supporting every parent vertex. The actual fixed-phase application is stronger: its final target v is a vertex.

A newly tight blocker in an unchanged phase is target-positive in slack coordinates (`same_phase_zero_blocker_is_trapped_positive`). It is therefore strictly slack at v. Deleting it preserves v and pointedness by the preceding result. The all-vertices-tight alternative is incompatible with v itself.

This uses no source-vertex premise: x and y may both be nonvertices, and P may be unbounded. It also does not assume an ambient injectivity hypothesis separately; the target vertex already forces the original active rows to span.

## Extreme batch: keep exactly the target-tight rows

Let Q retain exactly the rows tight at v. The preceding theorem makes Q pointed and preserves v. If z is any vertex of Q, every Q-row tight at z also has the same right-hand side at v. Thus all rows active at z annihilate z-v; the checked vertex-kernel theorem forces z=v.

Hence `extremePoints Q = {v}` and `DiamLE Q 0`. Geometrically this is the translated target tangent cone. It need not be a singleton feasible set, bounded, or connected by ordinary graph edges to an arbitrary nonvertex source.

This offers a batch-deletion alternative with **zero old-vertex graph cost**. It does not by itself prove a cheap route after all removed cuts are restored.

## Cost and recurrence boundary

The source vertex u may disappear as a vertex under target-slack deletion. For example, the square [0,1]^2 at target (0,0) becomes the nonnegative quadrant after both upper bounds are deleted; only (0,0) remains a vertex. The original opposite corner (1,1) still needs routing after reinsertion.

A dimension count gives the ordinary corollary |J| <= n-d, since the retained row map is injective. This controls distinct removed labels, not the cost of recursively restoring their final faces.

The one-cut wrapper in #164 cannot simply be applied as if an arbitrary simultaneous batch were one cut. Its final-face budget is for one deleted row; multi-cut repair requires the appropriate simultaneous geometric interface and explicit endpoint/face costs. Repeated independent lower-dimensional face budgets can still produce an exponential or Pascal-type recurrence. Nothing here establishes a uniform fixed-degree polynomial bound.

The useful next question is whether the actual phase's target-positive blockers admit a reusable, cost-controlled batch reinsertion cover. Keep the global ordinary-edge refinement theorem open until both that geometry and the accumulated cost are proved.

## Exact finite controls

`scripts/test_target_anchored_deletion.py` uses only Python's standard library and exact Fractions. It checks 212 batch deletions across 30 target vertices in 9 fixtures: a square, triangle, redundant/zero/duplicate-row model, lower-dimensional segment, two pointed unbounded examples, sheared cube, coefficients above 10^40, and dimension zero.

It also checks a nonvertex same-phase square step whose target survives deletion; a one-nonneutral-row quadrant step which necessarily changes phase; and the square/quadrant example disproving automatic survival of other parent vertices.

Expected full JSON SHA-256: `094ebcb1551b051d86d0e29e773e2530934a3766a4e9a9bf1087b802ecad7097`.
Frozen Lean source SHA-256: `1b8e3c801aa4a549728880ce253381aab0317ded1a1ee95c0635c9dea4d62a7e`.
