# A compact coefficient model for every bounded polyhedral image

## The completed mathematical target

Let X_t={x>=0: Bx<=t}, for finite real row and image maps B,G. The proposed
public theorem proves a constant C>0 depending only on B,G such that every
x in X_t has y in X_t with

    Gy=Gx, sum(y)<=C*(norm(t)+norm(Gx)).

Every originally zero coordinate of x remains zero at y, and every original
resource row tight at x remains tight at y. Consequently, if norm(Gx)<=M on
X_t, adding ONE row sum(y)<=R for R=C*(norm(t)+M) preserves its ENTIRE image.
The capped coefficient set is compact. Nonemptiness is not required; empty
images are included. B and its right sides may be signed. G need not be
injective, and original coefficient boundedness or coverage is not assumed.

This closes the bounded-image/unbounded-coefficient REPRESENTATION gap in #237.
The new mass row itself has the all-ones coverage certificate, so the existing
covering-allocation and checked-budget theorems may work with this compact
representation. One must actually provide/instantiate the cap and other
certificates; this theorem does not make arbitrary numerical data trustworthy.

The result is classical finite-dimensional polyhedral geometry, not a new
classical theorem or a uniform diameter estimate. The proof below establishes
it directly, without assuming Minkowski-Weyl, a finite vertex/ray decomposition,
a bounded-right-inverse theorem, or the existence of the desired representative.
Mathlib's compact extreme-value theorem is the analytic ingredient.

## 1. Remove positive kernel directions by support descent

For an arbitrary finite linear map A, start with x>=0. If its support contains
a nonzero nonnegative z with Az=0, let

    t=min_{i:z_i>0} x_i/z_i.

Then t>0, x-tz>=0, A(x-tz)=Ax, and at least one positive coordinate vanishes.
No zero coordinate can become nonzero. The source proves the full support
reduction and uses strong induction on support cardinality. It returns a
representative y with the same image and a support S containing NO nonzero
nonnegative kernel vector. This is a conclusion, not an assumed rank oracle.
The proof itself removes nonnegative kernel directions; no circuit catalogue
is enumerated or presumed complete.

## 2. Compact normalized supports give a uniform homogeneous bound

On a fixed such support S, consider

    K_S={u>=0: sum(u)=1, u_i=0 outside S}.

It is compact. If nonempty, the continuous function norm(Au) attains its
minimum, which is strictly positive because S has no positive kernel vector.
Rescaling any nonnegative vector on S therefore bounds its total mass by
C_S*norm(Au). Empty K_S is handled separately and permits only the zero vector.
There are finitely many coordinate supports, so one positive constant dominates
all the valid C_S. Combining with support reduction proves

    for every x>=0, exists y>=0:
      Ay=Ax, support(y) subset support(x), sum(y)<=C_A*norm(Ax).

The proof does NOT claim C_A is bounded by dimension or computable efficiently.
The minimum-norm proof also does not assert a continuous global choice of y.
The finite collection of supports is used for existence, not hidden as a
polynomial-cost enumeration algorithm.

## 3. Slack augmentation makes all resource inequalities exact

For x in X_t, form u=(x,t-Bx)>=0 and the linear map

    A(theta,s)=(Btheta+s, Gtheta).

Its image at u is (t,Gx). Apply the preceding homogeneous representative theorem
to obtain (y,s')>=0 with B y+s'=t and Gy=Gx. Thus ALL original inequalities
survive, and

    sum(y)<=sum(y)+sum(s')<=C_A*norm((t,Gx))
        <=C_A*(norm(t)+norm(Gx)).

Zeros in x and in its original slack vector stay zero, yielding the two
face-preservation conclusions. The construction is not an edge walk: it may
move through a higher-dimensional coefficient face, and its projection need
not represent original graph edges. No original diameter conclusion is drawn.

If the image is bounded by M, one uniform cap R=C_A*(norm(t)+M) works for every
image point. The capped set is an intersection of the closed original
halfspaces with a bounded nonnegative simplex, hence compact. Both inclusions
of the IMAGE equality are proved. The original coefficient set can remain
unbounded; it is not falsely asserted equal to the capped set.

## Exact controls and computational interpretation

B=0,G=0 has unbounded coefficients but singleton image. The added cap can
preserve that image using y=0, with no original coverage certificate.
For B=[I,-I;-I,I], G=[I,-I], t=1, the coefficient set contains arbitrarily
large (z,z) rays but its image is [-1,1]^d. Sign-separated representatives use
at most d total mass. The 32-coordinate test starts at mass128000637/4 and
returns mass37/4, below cap16, with identical image and original tight rows.
No complete coefficient graph, image graph or image vertex set is enumerated.

At the opposite boundary, G=(epsilon), no resource rows, and image point1
force coefficient mass1/epsilon. The test uses epsilon=2^-120. Thus a theorem
claiming a dimension-only numerical mass constant would be false, even in
one dimension. The existence result is not a route to a universal conditioning
bound or a new Polynomial Hirsch estimate.

The exact rational constructor uses signed-kernel pruning to reach independent
columns, a stronger termination condition than the proof's positive-kernel
pruning. It checks a rational left inverse on the final support; its absolute
coefficient sum gives a per-support infinity-norm bound. Small examples audit
all subsets and take the maximum bound, giving independent numerical uniform
constants. Large examples verify only the actual returned trace, left inverse
and original constraints; the generic Lean theorem is not a claim that each
large table was separately kernel-evaluated.

The independent arithmetic auditor calls no rank or elimination routine. It
checks nonnegativity, support containment, exact null directions, the maximal
ratio, strict support descent, original image reconstruction and the left
inverse identities. Tests deliberately disable producer search routines during
auditing. Python/JSON are not Lean-extracted and are not themselves verified
by publication of the generic theorem.

## Executed regression

    python3 scripts/test_bounded_representatives.py

The initial completed regression checks448 linear-fiber cases,684 support
reductions,112 exhaustive small uniform tables and2032 support cells;72 slack-
allocation cases and85 reductions;15 bounded-image/unbounded-coefficient cases;
and12 malformed controls. Every global constant is checked against the actual
rational matrices in those small cases. Exact counts and source SHA-256 hashes
are in research/BOUNDED_REPRESENTATIVE_TESTS.json. No runtime or coefficient-
bit-complexity theorem is claimed.

## Coordination and verification boundary

The live queue already assigned #238 to strict support-witness existence and
#239 to additive simultaneous Minkowski edge lifting. Neither is duplicated,
modified or triggered here. A coordination comment on merged #237 was blocked
before creation and was not retried via another route. This independent source
implements the distinct bounded-image task explicitly named by current STATUS.

The prepared standalone Lean source has five axiom printouts and an import/open-
only public preamble. Local Lean/Lake is absent and public toolchain DNS failed.
Source inspection and Python tests are not compilation. Only the actual pinned
final gate and authenticated publication receipt may establish those statuses.
No new Farkas, coverage-existence or bounded-representative premise is added.
After a successful gate, preserve exact source hashes and receipts, not an
unsupported assertion that the result was accepted. Do not duplicate pending
or accepted submissions or change the workflow/pin/security split.
