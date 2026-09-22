# One source-sensitive potential that decreases on every original edge

## Public geometric input and derived state function

Let P be exactly both conv(C), for a finite real set C in ambient dimension d,
and the ORIGINAL m halfspaces A_i x <= b_i. Let u and v be actual extreme
points. No target-exposing objective, denominator, short acquisition phase,
independent basis, graph, path, or small-rank hypothesis is supplied.

The accepted finite-hull exposure lemma derives a linear h with

    h(z-v) > 0 for every z in C different from v.

This numerator remains FIXED throughout the route. Filter C for actual
extremality to derive the complete original vertex set V. At current vertex x,
let F(x) consist of all actual vertices satisfying every original equation tight
at BOTH x and target v. This is the actual common-target lock face, not a planned
prefix that ignores incidental acquisitions.

For an anchored affine denominator q_D(z)=1+D(z-v) positive on F(x), set

    r_D(z)=h(z-v)/q_D(z),
    R(x,D)={r_D(z):z in F(x), r_D(z)<r_D(x)}.

R counts DISTINCT values strictly below the CURRENT value. It does not count
all vertices, all normalized values, numerical gaps, or target rows. The target
has ratio zero; every other actual vertex has positive ratio on this face.

The theorem derives a slope E(x) attaining the minimum of |R(x,D)| over every
positive anchored affine competitor on F(x), and defines rho(x)=|R(x,E(x))|.
It constructs an ORIGINAL ordinary-edge route from u to v such that

    rho(v)=0,
    rho(next)<rho(current) at EVERY edge,
    L<=rho(u)<=|R(u,D)| for every positive initial competitor D.

The finite sets and rho are explicit let-expressions in the public statement.
Every route point is an actual original extreme point. Every successive segment
is whole, nondegenerate and IsExtreme in ORIGINAL P. Every acquired target row
remains tight, including target rows not selected by any predefined order.

This removes phase resets from the potential argument. In particular, the
integer decreases on steps acquiring NO new target row. Strict decrease implies
no repeated visited vertex, although injectivity is not a separate public field.
The theorem does not claim that an arbitrary original edge decreases rho; it
constructs suitable original improving edges.

## 1. Attained source-sensitive minima

The constant denominator one is admissible in every state. Hence the set of
attained natural-number ranks is nonempty. Natural well-ordering selects its
minimum, and classical choice supplies E(x) for all states. Only actual vertices
are used by the route and covered by the relevant public positivity clause.

This is a mathematical existence theorem. It does NOT identify the classical
choice with the separately implemented exact-rational order-cell solver. It is
not a claim of polynomial-time synthesis or of a uniformly small minimum.

Anchoring at v does not restrict positive affine competitors relevant to an
actual face: v belongs to F(x). Dividing an arbitrary positive affine q by q(v)
puts it in anchored form and scales every ratio by the same positive number,
leaving order and rank unchanged. That equivalence is part of this written
interpretation; the explicit public comparison quantifies anchored slopes.

## 2. Produce a ratio-improving ORIGINAL neighbor

At a nontarget actual vertex x, use D=E(x) and let r=r_D(x)>0. Then

    r*(1+D(x-v))=h(x-v).

For the LINEAR objective f=-h+r*D, this identity implies

    f(v)-f(x)=r>0.

The accepted original-edge construction in the current target-lock face gives
an actual original neighbor y with f(y)>f(x), preserving all currently acquired
target rows. Thus y remains in F(x), where q_D is positive. Cross multiplication
by that positive denominator yields r_D(y)<r_D(x).

No fixed objective is asserted across steps. The numerator h is fixed, but the
normalizer and current ratio can change the linearization. No lower bound on a
numerical gain is required. The construction handles redundant generators and
rows, nonsimple or lower-dimensional bodies, and zero-dimensional cases.

## 3. Reoptimization cannot reset the potential

Target-lock preservation gives the exact inclusion F(y) subset F(x). Therefore
the OLD denominator D is still positive on the new face. Every value in R(y,D)
also lies in R(x,D). Moreover r_D(y) belongs to R(x,D) but not R(y,D): it is a
value at the actual neighbor, and the source threshold has strictly decreased.
Consequently

    |R(y,D)| < |R(x,D)|.

The new optimum is no worse than keeping D, so

    rho(y) <= |R(y,D)| < |R(x,D)| = rho(x).

This is the central lower-envelope descent. The number of possible slopes need
not be bounded, and slopes do not need to persist. Original target faces may
shrink or stay the same; the strict decrease does not rely on a face drop.

Strong induction on rho constructs the entire route. Each prepend adds one
edge, and the next rank is strictly smaller, so the total is at most rho(u).
The target rank is zero since there are no negative ratios below its zero
value. Coincident endpoints use the zero-edge route.

## 4. Exact finite search on rational instances

The executable solver is independent supporting code, not Lean-extracted.
On a complete finite face, numerator values are zero exactly at v and positive
elsewhere. Every admissible denominator therefore induces a unique ordered
partition of the positive vertices into equal-ratio groups. Fixing one such
partition produces a LINEAR feasibility problem in D:

    equal ratios i,j:
      D(s_i*(z_j-v)-s_j*(z_i-v)) = s_j-s_i;
    ratio i strictly below ratio j:
      D(s_i*(z_j-v)-s_j*(z_i-v)) < s_j-s_i;
    positivity at each point:
      -D(z_i-v) < 1.

It suffices to compare consecutive groups, and to tie each group to its first
member. All numerator data and inequalities are exact rational numbers.
Enumerate every ordered partition, sorted by the source's group index plus
one (the additional lower value is target zero). The first feasible cell
therefore attains the minimum source rank. For N positive points the number of
cells is the ordered Bell number, using a(0)=1 and

    a(N)=sum_(j=1..N) choose(N,j)*a(N-j).

Every tested infeasible cell has a rational equality annihilator or a strict
Fourier--Motzkin dual certificate. A separate consumer reenumerates the exact
cell prefix, checks all exclusions, positivity, complete equality nullspaces,
and the final denominator. Solver limits raise errors, not false exclusions or
optimality claims. A real positive solution belongs to one of these order cells;
linear infeasibility certificates exclude real as well as rational solutions.
The consumer and parser are not themselves formally verified.

The route producer uses the negative sum of all target-active original normals
as one strictly target-exposing h. The generic internal Lean theorem works for
any such h; the public theorem derives an h via finite-hull separation. The
computational choice is not asserted byte-for-byte equal to classical choice.

## Executed tests and limitations retained

Eight complete small H/hull models include a point in dimension zero, segment,
square, pentagon, hexagon, embedded lower-dimensional pentagon, tetrahedron and
octahedron. The suite checks159 endpoint routes and180 original-edge occurrences.
It audits6346 ordered cells with6220 certified exclusions. Source rank is strictly
smaller than the minimum COMPLETE normalized spectrum minus one in33 states,
for the SAME fixed aggregate numerator on the SAME face. This is NOT a
comparison with #335's different rowwise conditional flag budget.

Six edges acquire no target row but still strictly decrease rho. Nine malformed
controls fail. Stored replay disables both optimization programs, equality and
strict-feasibility solvers, improving-edge production and route construction;
all certificates and original support edges still audit. The full tested route
lengths and ranks happen to equal graph distances in these small cases. No
nonshortest example or strict extra benefit from reoptimizing over the old
post-step rank was observed here. Neither shortestness nor strict extra benefit
is asserted by the theorem.

An additional seven-vertex polygon stress call hit its45-second time cap before
producing a complete report or fixture. It is retained as INCOMPLETE, not counted
among successful models and not treated as an exclusion. No large graph or
ordered-cell complexity result is inferred from these tests. Full successful
report and fixtures accompany the export and regenerate from the five scripts.

## Verification and remaining mission gap

The retained778-line/31854-byte prefix is copied exactly from accepted #335,
ending immediately after Edge and improve_locked. Accepted public roots are
omitted, not republished. The five frozen dependency input hashes were checked.
The new public statement uses Mathlib-only expressions and matches top-level
solution exactly. Seven transitive reports cover exposure, minimizers, rank
comparison, original-edge descent, target zero, full route and public root.

Local Lean/Lake/Elan and checked caches are absent; release/raw-host DNS failed.
Text, hash, patch and rational checks are NOT Lean compilation. The complete
candidate is prepared for one pinned final gate, with actual failure evidence
preserved if it fails. Keep Lean4.30.0, Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f and strict protocol0.10.8 unchanged.

The geometric hypotheses remain exact finite H/hull equality and actual endpoint
extremality. The exposure is fixed during the route, not jointly optimized with
every denominator. A constant denominator already bounds rho by an actual vertex
inventory, which can be exponential in original m. Source-sensitive synthesis
can also be expensive. The theorem provides no uniform polynomial bound on rho,
no efficient H-to-V method and no unrestricted Polynomial Hirsch conclusion.
The positive next obligation is an original-input bound on this decreasing
potential or a different controlled original-edge invariant. No historical
priority or best-known general diameter claim is made.
