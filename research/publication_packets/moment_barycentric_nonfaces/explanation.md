# Explicit barycentric nonfaces for the ORIGINAL moment inequalities

## Exact scope

Target: `Hirsch.moment_curve_barycentric_nonfaces`.
For d,m natural, an injective real parameter map a on Fin m, and any selected
set s with d+2 <= |s|, define

    w_i = inverse(product_{j in s minus {i}} (a_i-a_j)).

The theorem proves these weights are nonzero on s and

    sum_{i in s} w_i * a_i^r = 0,       0 <= r <= d.

For the original mean-centered inequalities

    row_i(x) = sum_{j=1}^d (a_i^j - average_l a_l^j) * x_j <= 1,

EVERY feasible x has a selected negative-weight row strictly below 1 and a
selected positive-weight row strictly below 1. Thus neither sign side can be
simultaneously tight. In particular both sign sides are nonempty, by applying
the result to x=0. The public target includes the actual inverse-product formula
and original row formula as local `let` expressions, not opaque definitions.
No affine circuit, rank/spanning certificate, optimizer, exposing hyperplane,
ordered-sign characterization, or infeasibility oracle is an input.

This is the complementary incompatibility mechanism to the accepted #285
small-face witness theorem. It is NOT another submission of that theorem,
#281's accepted stellar count, or #284's protected-state count. It does not
assert or formalize the full odd-subset minimum-nonface classification and its
exponential cardinality, the entire geometric family, or Polynomial Hirsch.
The input m and d may include d=0; |s|>=d+2 guarantees m>=2. The public claim
is about the displayed inequalities and does not need an independent bounded-
polytope, simplicity or irredundancy hypothesis.

## 1. Constructed annihilation, not a supplied relation

For every polynomial p with natDegree(p)+1<|s|, Lagrange interpolation on the
selected distinct nodes gives

    p(T) = sum_{i in s} p(a_i) * L_i(T).

The coefficient of degree |s|-1 on the left is zero. The leading coefficient
of L_i is exactly w_i. Taking that coefficient proves

    sum_{i in s} w_i * p(a_i) = 0.

The Lean helper `weighted_eval_zero` applies the pinned Mathlib interpolation,
basis-degree and leading-coefficient theorems, then finite coefficient linearity.
Its statement contains NO assumed annihilation. Nonzero differences separately
prove w_i is nonzero. Monomials p(T)=T^r supply all requested moment equations.

## 2. Low-degree positivity must occur on both signs

Suppose p is nonzero, degree(p)+1<|s|, and p(a_i)>=0 for every selected i.
At least one evaluation is positive: otherwise |s| distinct roots contradict
the polynomial root-uniqueness theorem. At that index the weighted evaluation
w_i*p(a_i) is nonzero. A finite sum of reals equal to zero with a nonzero term
has both a negative and a positive term. Since the polynomial evaluations are
nonnegative, these two terms exhibit positive evaluations at negative and
positive weights, respectively.

This finite sign argument is fully proved rather than inferred from a sorted
picture of nodes. It applies to arbitrary parameter order and to larger s as
well as the minimally sized d+2 case. The theorem deliberately does not classify
the signs by index parity, which is a separate application step.

## 3. Bind the polynomial to the full ORIGINAL H-description

For an arbitrary vector x construct the actual slack polynomial

    p_x(T) = 1 - sum_{j=1}^d (T^j - average_l a_l^j) * x_j.

Its degree is at most d, and p_x(a_i)=1-row_i(x). Summing the mean-centered rows
over ALL original labels gives zero, hence

    sum_i p_x(a_i) = m > 0.

So this slack polynomial is never the zero polynomial, for any x. If x is
feasible, all selected evaluations are nonnegative. Section 2 supplies the two
strictly positive slacks, proving the public result. This is why the proof
needs no supplied affine-rank or interior-point certificate to exclude an
all-tight sign class: centering certifies nonzero slack, and the many distinct
nodes force a nonzero evaluation.

## 4. Relation to the geometric minimal-nonface application

For the original integer nodes 0,...,4k, choose any (k+1)-subset N of the odd
labels. Add the even separators consisting of min(N)-1 and each n+1 for n in N.
There are 2k+3 selected distinct nodes in alternating even/odd order. An exact
sign calculation makes all N weights negative and all separator weights positive.
Thus the present theorem excludes a common feasible tight point for N.
Accepted #285 constructs feasible exact-tight witnesses for its proper subsets.
The Python regression checks this application, including every small N and
selected larger N. The general sign-by-order lemma, catalogue counting, and
composition as a single geometric Lean theorem are NOT included in this packet.
Those remaining interfaces are not silently assumed formalized.

The incompatibility applies on the ORIGINAL m-row system, not only on a selected
subsystem with a different mean. A selected s may omit many original rows; the
mean in the public statement is still the mean of all m parameters.

## Verification and publication boundary

The standalone source and problem.json are generated from the same public
signature. The preamble is only an import and `open scoped BigOperators`.
The solution requests five transitive axiom printouts. It imports only Mathlib,
never the target. All lower-degree sums, nonzero evaluations, sign witnesses,
and centering are derived in the proof.

The current local runtime has no Lean/Lake and cannot resolve the toolchain
host. Source inspection and exact arithmetic tests are NOT Lean compilation.
This packet is prepared for the user-requested final existing comment gate.
No experimental workflow, toolchain change, new credential, token, permission,
or alteration of the trusted verification/publication secret split is made.
Only the actual pinned compiler/audit run and authenticated platform receipt
may establish compilation or acceptance. On failure preserve diagnostics and
leave the draft status honest; do not weaken this mathematical statement.

The new top-level command on this packet's open same-repository PR is:

    /prove2me publish research/publication_packets/moment_barycentric_nonfaces

Do not post on accepted #285 or duplicate a pending publication command.

## Primary dependencies and attribution

The exact pinned source was inspected at Mathlib commit
c5ea00351c28e24afc9f0f84379aa41082b1188f:
- Mathlib/LinearAlgebra/Lagrange.lean: interpolation identity, coefficient of its
  basis, and polynomial uniqueness from indexed roots.
- Mathlib/Algebra/Polynomial/Coeff.lean: coefficients commute with finite sums.
- Mathlib/Algebra/Polynomial/BigOperators.lean: finite-sum degree bound.

Interpolation, its barycentric weights, and moment-curve geometry are classical.
No historical-priority or new best-known diameter claim is made. The contribution
is the explicit Lean original-H incompatibility interface with no assumed
certificate, followed by real pinned verification/publication when available.
