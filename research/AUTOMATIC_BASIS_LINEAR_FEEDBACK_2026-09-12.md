# Automatic target bases and linear mixed-carrier routing

This continuation starts from merged #205/#206 at
`a00b67b37d31b30f76a4965e3e6947a1e305e80c`. It closes the supplied-basis
formalization gap and combines actual feedback routes with joint carrier mass.
It does not duplicate #207's portal debt or #208's bounded-spill recurrence.
All three new modules compile at the committed Lean/Mathlib pin. All eight
new declarations pass the transitive standard-axiom audit; the complete log
checks 414 reports. [Local evidence](verification/2026-09-12-automatic-basis/local-audit.json).

## 1. The target basis is now obtained from the vertex

Let P be an n-row H-polyhedron in R^d and v one of its extreme points.
The existing finite-perturbation theorem says that a vector annihilating every
row tight at v must be zero. Therefore the orthogonal complement of the span
of those normals is zero, so their span is the entire ambient space.
Select an independent subfamily spanning the same space. A basis of R^d has
exactly d elements, and its original row indices are distinct. Reindexing by
Fin d gives an embedding e0:Fin d -> Fin n with injective row evaluation and
all selected rows tight at v.

`exists_target_tight_basis` proves this without boundedness, strict feasibility,
simplicity, or a supplied basis. This is classical finite linear algebra;
the contribution is completing the missing formal interface, not a claim of
a new basis-existence theorem in mathematics.

For a bounded presentation with a separately supplied point o strictly
satisfying every row, feed this automatically selected basis into #206's
compact-star and deferred clipping construction. It retains exactly d rows
and restores every other original row, including extra rows tight at a
nonsimple target. Thus s=n-d available cuts and D=1, with no local route
premise needed to select the actual portal pairs. On this certificate,

    sum_i delta_i <= 3(n-d),
    sum_i h_i <= 3(n-d),

where delta_i and h_i are the minimum intrinsic presentation excess and
dimension of each actual common carrier. The new wrapper no longer asks the
caller to find a target-tight basis. Strict feasibility is still an explicit
geometric hypothesis. A redundant zero-equality or lower-dimensional ambient
presentation may not have such a point; a further intrinsic-normalization
wrapper is not silently assumed here.

## 2. Spend joint mass on actual feedback routes

#205 proves that a positive-feedback image model of an h-dimensional carrier
gives an ordinary-edge diameter bound h. Its model supplies a monotone linear
operator C, positive b,w with Cw<w, a positive projective chart and an injective
affine embedding onto the actual carrier. It contains no graph or diameter
premise. There is no dimension cap, acyclicity restriction, or product split.

The exact #205 adapter charged D+sum(h_i). It previously padded this by D+d*r.
The new `route_positive_boxes_of_all_row_mass` instead uses #206's aggregate:

    D + r*a + 3s,     s+a=n-d.

At full availability this is D+3(n-d), even with unbounded used-support
deficit g=(n-d)-r and unbounded individual carrier dimension. The parameter a
is the availability defect; it must not be confused with g.

Actual carriers of excess at most three can be mixed into the same repair.
The explicit already-established small-excess input routes them at cost
delta_i, and feedback carriers have h_i<=delta_i. Therefore

    every selected carrier feedback OR delta_i<=3
      => route cost <= 1+3(n-d)

on the automatic basis-star certificate. The existential certificate appears
before the model callback: only its selected pairs are requested, not every
pair on every available facet. `exists_automatic_basis_linear_mixed_route`
keeps both its joint excess bound and this conditional route conclusion.

This is a sufficient criterion. It does not assert that arbitrary selected
carriers are feedback images, or provide a complete recognition algorithm.
The bound also need not beat a direct route already known for a particular
whole polytope: a d-dimensional feedback box already has its d bound from #205.

## 3. A linear route or a more specific actual residual carrier

The second mixture permits all carriers of dimension at most five alongside
arbitrary-dimensional feedback carriers. For a low-dimensional carrier, the
explicit classical Larman input gives M_i*2^max(h_i-3,0). The verified intrinsic
relation M_i<=2delta_i makes this at most 8delta_i when h_i<=5. Feedback
carriers cost h_i<=delta_i<=8delta_i. Summing on the same full-availability
certificate gives

    every selected carrier feedback OR h_i<=5
      => route cost <= 1+24(n-d).

`automatic_basis_linear_route_or_high_dim_nonfeedback_carrier` retains the
automatic certificate and sum(delta_i)<=3(n-d), then returns either that route
or a member of its actual selected-leg list whose common carrier has dimension
at least six and admits no `PositiveBoxImage` model. Its excess is consequently
at least its dimension by the existing intrinsic theorem. The residual is
failure of this sufficient criterion; it is not a graph-distance lower bound
and does not exclude other easy structures such as recursive product models.

## 4. Verification and publication boundaries

Reproduce the new proof checks with:

```sh
lake build Solutions.PolynomialAutomaticTargetBasis \
  Solutions.PolynomialLinearFeedbackMassRouting \
  Solutions.PolynomialFeedbackCarrierResidual
```

The three files have no holes, custom axioms, or imported theorem placeholders.
Small-excess and Larman assumptions remain explicit where used. Pure feedback
mass routing and basis extraction do not use them. No new Python enumeration
is presented as evidence for these quantified theorems: their new evidence is
Lean compilation and transitive axiom checks. The #205 fixture audit and #206
full exact regressions were executed and preserved in their merged PRs.

The public basis packet, when accepted, concerns basis extraction only. The
automatic clipping and mixed-routing results have their own local/hosted
verification; acceptance of a smaller public theorem does not certify all of
these geometric assemblies on Prove2Me. Final hosted and platform receipts
are recorded in STATUS.md and the packet directories when available.

## 5. The remaining target

Polynomial Hirsch remains open. The new conclusions close neither arbitrary
high-dimensional carrier routing nor a polynomial bound on repeated charges
across nested repairs. A factor-three sibling mass sum alone still permits an
exponential independent-call majorant, as #206 records.

#207 studies portal debt and near-geodesic windows; #208 gives a polynomial
recurrence conditional on bounded additive sibling spill at each split. The
substantive geometric question is whether suitable portal choices uniformly
realize such a bounded-spill rule, including the hard finite families in those
PRs. The automatic basis lemma now removes one setup obligation when that
question is studied through full-availability basis-star certificates. It does
not solve the portal-selection rule. Keep strict-center, actual-edge,
dimension-drop and repeated-occurrence conditions explicit in that next work.
