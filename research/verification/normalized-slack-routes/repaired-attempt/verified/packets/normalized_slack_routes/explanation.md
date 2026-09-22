# Original-edge routes from normalized slack spectra

## Exact public statement

Let P be both the convex hull of finite real C in ambient dimension d and its
ORIGINAL m inequalities A_i x <= b_i. Let u,v be actual extreme points. For each
original row, supply an affine denominator a_i+D_i x that is strictly positive
at every actual vertex. The denominators may DIFFER by row; a common invertible
projective chart, a product decomposition, or a neighbor graph is not assumed.

On the actual vertices V, define the normalized slack spectrum

    R_i = {(b_i-A_i x)/(a_i+D_i x) : x in V},    w_i=|R_i|-1.

Let G contain original equations tight at both endpoints and T the original
target rows missing at u. The theorem DERIVES S contained in T with
|S|<=min(d,m-d), whose equations together with G have trivial homogeneous kernel.
Its weight is minimum among all determining completions R contained in T of
size at most d. Construct an ORIGINAL-edge route with

    L <= sum_(i in S) w_i <= sum_(i in R) w_i

for each such competitor. For the SAME route, weights at most K on selected
rows imply L<=K*min(d,m-d). This is a selected normalized-spectrum bound, not
shortest-path optimality. No small spectrum or small optimal weight is assumed
in the unconditional weighted assertion, and none is proved universally small.

Every visited point is an actual extreme point of ORIGINAL P. Every consecutive
segment is whole, nondegenerate and IsExtreme in that body. Every target row
already acquired stays tight, including unselected rows. The determining set,
rank certificate, entire acquisition phase and route are derived, not supplied.
Exact finite H/hull equality, actual endpoints and positive affine denominators
remain explicit. Redundant rows/generators, nonsimple/lower-dimensional bodies,
zero dimensions, constant rows and coincident endpoints are included.

The public positivity assumption is on all actual vertices for every row.
The proof only needs those values in its steps. Positivity along every delivered
edge follows separately from affinity and positive endpoints; no pole-crossing
or nonlinear movement is used to manufacture an edge. Denominator discovery,
efficient vertex enumeration, efficient subset minimization, all-facet
nonrevisiting, one global objective and uniform Polynomial Hirsch are NOT claimed.

## 1. Linearization produces a genuine original edge

Fix a target-tight row j and a current actual vertex x with positive slack.
Write n(z)=b_j-A_j z, q(z)=a_j+D_j z and r=n(x)/q(x)>0. Use the LINEAR objective

    f(z)=A_j z+r D_j z.

Since A_j v=b_j,

    f(v)-f(x)=r q(v)>0.

The accepted original-hull improving-edge theorem, inside the current target-lock
face, constructs an actual original neighbor y with f(y)>f(x). Positivity q(y)>0
and n(x)=r q(x) give

    f(y)>f(x)  iff  n(y)<r q(y)  iff  n(y)/q(y)<r.

Thus normalized slack strictly decreases on a GENUINE original edge preserving
all current target locks. The objective is recomputed using the new ratio at the
next step; raw slack need not decrease and no fixed numerical gain is needed.
This is elementary linear-fractional algebra composed with the accepted geometry,
not a new projective-transport or tangent-cone assumption.

## 2. Construct the whole phase by counting distinct ratios

For row j, consider the finite set of values in R_j strictly smaller than the
current value. At every improving step it becomes a strict subset: the new value
belongs to the previous set but not the next one. Strong induction on this
cardinality constructs the whole route until A_j=b_j. Its length is at most
|R_j|-1. This is not an inference from termination alone or from a lower bound
on numerical progress. Very small positive denominators and ratio gaps remain
permitted. A row already tight has a zero-edge acquisition phase.

## 3. Select a determining completion and charge it once

Reuse accepted small_completion: restrict original target-active rows to the
kernel of shared equations, select a spanning independent subfamily of restricted
functionals, and remove already-shared labels. Actual target extremality proves
injectivity and yields a completion with at most d original labels. Thus the
finite family of eligible subsets is nonempty. Minimize its nonnegative integer
normalized-spectrum weight by finite mathematical minimization.

At a current vertex different from v, some selected row is missing; otherwise
its displacement from v vanishes on both G and S and is zero. Apply the entire
normalized phase for a missing selected row. All shared/previous target equations
remain tight, so the due selected set loses that row and never restores a paid
label. Its nonnegative weight pays the phase once; incidental acquisitions are
free. Strong induction constructs and appends all phases, proving the minimum
selected-budget bound. Source-active injectivity gives |T|<=m-d, so the selected
cardinality is at most min(d,m-d). Summing the K bound gives the same-route
corollary.

This uses GLOBAL normalized spectra. It does not silently replace #332's
face-local affine cost or prove that arbitrary normalization always improves
it. Choosing all denominators equal to one recovers global raw slack weights.
A future face-local ratio refinement and automatic good-denominator theorem
would be separate obligations.

## 4. Why raw face-local costs are insufficient: a projective cube

The accompanying research note gives a COMPLETE WRITTEN all-dimensional argument,
not a second Lean instance theorem. For d>=1 let w_j=2^j and use exactly 2d rows

    x_i>=0,       x_i+w.x<=1       (i=0,...,d-1).

Put q(x)=1-w.x. Every feasible point has q>0: 0<=x_i<=q, and q=0 would force x=0
and hence q=1. The transformations y=x/q(x) and x=y/(1+w.y) are mutual inverses
between this P and [0,1]^d. The finite H/hull equality, all actual vertices,
original facet witnesses and whole original edges are derived in the note.
No extra redundant high-weight inequality is added; all 2d rows are genuine
facets. The finite vertices are x^S=1_S/(1+w_S).

Take u=x^[d] and v=0. The target rows are exactly the d lower coordinate rows,
all initially missing, with no shared equations. Any eligible determining flag
in #332 must use all d, so its only choice is their order. If k coordinates
remain after a prefix, the next raw lower row has zero and 2^(k-1) distinct
nonzero values. Binary subset-sum uniqueness proves this count for every order.
Consequently EVERY eligible #332 order has conditional total

    2^(d-1)+...+2+1=2^d-1.

Therefore the proposed route to the general mission by universally bounding
#332's specific optimized raw affine-row charge is FALSE. This does not refute
#332 itself, whose conclusion is conditional and remains accepted. It is not
an original-diameter lower bound or an obstruction to every adaptive invariant.

Divide each slack by q(x). Lower and upper row ratios become y_i and 1-y_i,
respectively, and hence are binary at EVERY actual vertex. The generic normalized
routing theorem gives <=d original edges for ANY pair of vertices in this family.
The independently tested opposite-endpoint route removes one upper bit at a time
and has exactly d original edges. Its raw lower slack can increase elsewhere,
but its target locks and selected ratio progress remain valid.

In d64 there are128 original facets: every raw eligible flag costs2^64-1, while
the normalized budget and explicit route are64. No2^64 vertex list or large graph
is enumerated. The all-dimensional counterexample/application is written proof;
small exhaustive checks and large support certificates are supporting arithmetic.
The construction and fractional transformations are classical in character;
no historical priority, best-known diameter or new cube graph theorem is claimed.

## 5. Relation to prior project work and limits

#203 already addresses positive projective transport, and #256 already studies
normalized slack SHARES, projective invariance, and vanishing angular/radial
contraction at fixed facets. Those results are not resubmitted or superseded.
Here the positive denominator need not be the sum of target slacks (which vanishes
at v), denominators may vary by row, and a finite spectrum bounds the complete
phase without any uniform fraction-of-gap premise. #256's contraction barrier
therefore remains intact. #276's all-affine global-level obstruction and #332's
exact local construction remain distinct. #326 and #282's owned family proofs
and reserved #210 are unchanged.

A universal polynomial original-edge bound still requires a derived universally
useful invariant or normalized cost bound, not supplied small spectra or a
recognition oracle. The projective cube refutes one attempted RAW-cost route to
that goal and demonstrates a positive normalized escape on the same inputs.
It does not prove all carriers admit a small normalized completion.

## Formal source and executed verification boundary

Retain exactly932 lines/38243 bytes of accepted #332 proof bodies and namespace
closures before its FaceLocal namespace. All five dependency manifest hashes
were recomputed from the supplied accepted bundle; its complete source and the
prefix are unchanged. No accepted public target is resubmitted or used to prove
itself. New code supplies fractional linearization, complete ratio phases,
normalized weight selection/accounting and the exact public root. The public
type uses Mathlib only with an imports/open/options preamble; seven final named
transitive reports are requested. Requested reports are not passing verification.

Local lean/lake/elan and checked /opt,/home/oai,/mnt/data installations/caches
were absent; toolchain-host DNS returned no addresses. Source and arithmetic
checks are NOT compilation. One complete carefully prepared pinned final gate
is required. Preserve any failed source/diagnostics rather than repeat speculative
hosted edits. Lean4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f,
strict0.10.8, duplicate guards and verifier/publisher isolation remain unchanged.

The executed23-model rational suite constructs564 routes with700 original-edge
occurrences versus694 total shortest edges. Three nonshortest routes,57 multiedge
phases,24 nonacquiring steps and53 within-phase objective changes are retained.
The consumer independently checks724 determining candidates, complete ratio
spectra, every current linearization, target locks and whole original edge slices.
Row-specific denominators include minima2^-30. Eight malformed controls fail.
Serialized replay disables selection/route/edge production.

The projective-cube suite checks eight dimensions1/2/3/4/8/16/32/64,130 further
original edges and260 genuine-row singleton-support witnesses. At dimensions
1..4 it solves all98 original full-row systems, finds30 actual vertices, and
checks all33 eligible orders; higher cardinalities are proved formulas, not
enumerations. Six malformed family controls fail. A clean FOUR-script replay
reproduces all four full JSON reports/fixtures byte-for-byte. Python/JSON are not
kernel-verified and no all-real result is inferred from finite sampling.
