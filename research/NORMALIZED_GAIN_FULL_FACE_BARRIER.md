# Normalized derivative is not a polynomial route-length potential

## Result and relation to the existing project

For every dimension d >= 2, the construction below gives a bounded, simple,
full-dimensional polytope P_d with exactly 2d+1 irredundant ORIGINAL facets,
vertices u_d,v_d having NO common facet, and an objective f_d strictly exposing
v_d. At every visited vertex x use the positive tangent height

    h_x(r) = -sum_{j active at x} a_j(r).

The rule that maximizes f_d(r) over the normalized tangent slice h_x(r)=1
and follows that ray to its maximal ORIGINAL feasible endpoint takes exactly

    floor(2^(d+1)/3)+1 edges

from u_d to v_d. Every maximizing direction is unique. Nevertheless there is
an explicitly constructed path with at most d+1 edges between the same points.
Thus restricting to the endpoints' common face does not cure this example:
that common face is P_d itself. This is NOT a diameter lower bound or a
counterexample to Polynomial Hirsch.

The classical base is Klee--Minty's Dantzig lower bound. Primary context:
Fearnley--Savani, *The Complexity of the Simplex Method*, arXiv:1404.0605,
https://arxiv.org/abs/1404.0605; the standard powers-of-two/powers-of-five
presentation also appears in Yang, arXiv:1910.10097, section 4.1,
https://arxiv.org/html/1910.10097. No claim of priority is made for the base
construction, Dantzig rule, or greatest-improvement comparator. The explicit
cap/target perturbation and common-face check below adapt that mechanism to
the concrete route-length question left by the accepted tangent-edge interface.

IMPORTANT IMPLEMENTATION BOUNDARY: #248 proves an edge from valid positive-height,
normalized-slice and maximal-ray witnesses, and its software chooses particular
fibre-dual witnesses via a Bland LP implementation. This experiment certifies
the canonical active-row-height variant, with an explicitly supplied strict
target exposer. It has NOT replayed those precise default discovery choices.
It rules out a polynomial bound derived solely from the broader positive-height
and maximum-normalized-progress invariants, not an untested claim about the
exact default executable's trajectories. #248's edge-validity theorem remains
correct, unchanged, and useful. #244's separately owned Minkowski assembly is
not involved or modified.

## 1. A cube described by the ORIGINAL inequalities

For i=1,...,d let

    U_i(x) = x_i + sum_{j<i} 2^(i-j+1) x_j,
    K_d = {x: x_i>=0, U_i(x)<=5^i}.

Put S_i=sum_{j<=i} 2^(i-j) x_j. Induction gives 0<=S_i<=5^i for every
feasible prefix. Indeed S_i=2S_(i-1)+x_i and the new upper bound gives
S_i<=5^i-2S_(i-1)<=5^i. Therefore the available width for coordinate i is

    W_i=5^i-4S_(i-1)>=5^(i-1)>0

(for i=1 it is exactly 5). No lower/upper pair can be simultaneously tight.
Every choice beta in {0,1}^d gives one vertex recursively:

    x_i(beta)=beta_i*(5^i-sum_{j<i}2^(i-j+1)x_j(beta)).

The selected active matrix T_beta is lower triangular with diagonal +/-1.
A vertex must have d independent tight rows, hence must select one from each
pair. These are all vertices, and changing one bit joins two adjacent vertices.
Every original row is a genuine facet; each simple selected vertex provides
its local (d-1)-dimensional patch. This proves the claimed graph without using
a larger extension or substituting its facet count for the original one.

Let c=(2^(d-1),...,2,1). Writing F_d(beta)=c.x(beta), the last coordinate gives

    F_d(beta,0)=2 F_(d-1)(beta),
    F_d(beta,1)=5^d-2 F_(d-1)(beta).

The first interval is contained in [0,2*5^(d-1)], the second in
[3*5^(d-1),5^d]. Thus all vertex objectives are distinct and ordered by binary
reflected Gray order g(t)=t XOR (t>>1), with coordinate 1 the low bit.
This strict order also proves no cap placed between consecutive values goes
through an old vertex.

## 2. The normalized tangent rule is exactly auditable

For the active matrix T_beta define d_i=-T_beta^(-1)e_i. Any feasible tangent
direction r satisfies T_beta*r<=0 and has the unique representation

    r=sum_i (-T_beta*r)_i d_i.

Consequently h_beta(r)=sum_i(-T_beta*r)_i is positive for every nonzero tangent
direction, and its height-one section is EXACTLY conv(d_1,...,d_d), not merely
contained in a finite hull. Maximizing a linear objective on this slice chooses
a best incident ray. The finite matrix identity T_beta*D=-I certifies this.

A triangular recurrence gives

    c.d_i = 2^(d-i) * (-1)^(beta_i+...+beta_d).

For completeness, let Z_j=sum_{l<=j}2^(j-l)(d_i)_l. Then Z_i=1-2beta_i,
Z_j=2(1-2beta_j)Z_(j-1) for j>i. Thus Z_d is the displayed derivative.
The positive derivative with largest magnitude is the smallest index i for
which p_i=(beta_i+...+beta_d) mod 2 is zero. These p_i are the binary digits
of the inverse Gray index. Toggling beta_i flips p_1,...,p_i: all lower one
bits become zero and p_i becomes one. The index increases by exactly one.
Hence the derivative rule visits successive Gray vertices, not just a
selected collection of exponentially many feasible points.

The independent auditor additionally checks the normalized optimum dual
identity at every executed step. If s_i=f.d_i and s_* is maximal, then

    f = s_* h_beta + sum_i (s_*-s_i) T_(beta,i),  s_*-s_i>=0.

This certifies optimality over the ENTIRE normalized slice. Strict inequalities
for all competing i prove uniqueness. Original-row ratio bounds certify the
maximal finite endpoint, and the remaining d-1 active rows certify an actual
ordinary edge. No circuit step, projected chord, nonmaximal segment or shortcut
through the interior is counted as an edge.

## 3. Add one cap and choose a strict target with no shared facets

Let a=(1,...,1). Its inverse Gray index is

    N_d = sum_{j=0}^{d-1} ((d-j) mod 2) 2^j = floor(2^(d+1)/3).

For d>=2 it is not the last Gray vertex. Let a' be the next Gray bit vector,
and let ell be its one changed coordinate. With zero-based coordinates ell
is d mod 2. Put

    v = (x(a)+x(a'))/2,
    gamma = c.v,
    P_d = K_d intersect {c.x<=gamma}.

The cap lies strictly between consecutive original objective levels. It cuts
no old vertex. The origin and x(a) lie strictly below it. All d lower facets
survive near the origin, and all d upper facets survive near x(a). The cap
is itself a facet since it intersects the interior between below/above-cap
interior points. The new polytope is simple: new vertices cut interiors of
old edges and acquire the cap plus their d-1 independent common old rows.
The tests independently provide a point tight on exactly EACH of the 2d+1
rows, as well as a strict interior point.

The target v lies on the cap and on U_j=5^j for precisely j!=ell. Every
coordinate of v is strictly positive. The origin has precisely its d lower
facets tight. Hence the endpoints share no facet. Since every proper face
lies in a facet, their minimal common face is the full d-dimensional P_d.

Define q=sum_{j!=ell} U_j and choose

    delta=2^(-d-4),   f=c+delta*q.

At v this is a strictly positive combination of all d independent active
facet normals: coefficient 1 on the cap and delta on the other rows. It
therefore uniquely exposes v over the WHOLE original polytope.

For every original vertex and tangent generator, the recurrence above gives
|(d_i)_j| <= 2^(j-i+1) for j>i and |(d_i)_i|=1. If upper row j is active,
U_j(d_i) is zero except possibly j=i; if it is inactive, the same recurrence
bounds its magnitude by 2^(j-i+1). Therefore

    |q(d_i)| <= 1+sum_{j>i}2^(j-i+1) < 2^(d+1).

Changing c to f changes each normalized derivative by less than 1/8. The
unperturbed derivatives are distinct signed powers of two, all nonzero and
separated by at least 1. Thus EVERY derivative sign and ordering is preserved.
There are no ties whose special resolution is responsible for the example.

Until x(a), the cap is inactive and every selected successor has smaller
c-value than gamma. The next chosen ray is the old edge [x(a),x(a')], which
now stops halfway at v. The target objective uniquely attains its maximum
there. Total route length is EXACTLY N_d+1. The input uses O(d)-bit numbers
per coefficient, not an exponential-length row list.

## 4. The diameter is not exponential

Turn on coordinates in the order 1,2,...,d, taking the upper endpoint each
time. This gives d adjacent original vertices from the origin to x(a).
The objective c strictly increases at each step: earlier coordinates stay
fixed, one positive new coordinate is introduced, and later coordinates
are still zero. All these c-values are <=c.x(a)<gamma, so the path survives
the cap. One more original edge reaches v. Thus distance <=d+1 in ALL
dimensions. The exponential route is a BAD CHOICE of valid edges.

A second selector implemented in this PR maximizes the COMPLETED-edge gain
alpha_i*f(d_i), where alpha_i is the maximal original feasible step. It is
classical greatest improvement, not a newly claimed pivot rule. On identical
inputs for d=2,...,12 it returns d steps. Each instance is certified shortest:
the endpoints share none of the d initial facets, and an edge of the simple
polytope can drop at most one of those facets. Thus every route has >=d steps.
This finite result is NOT extrapolated to a proved all-d d-step trajectory
for this selector, nor to a polynomial guarantee on arbitrary polytopes.

Completed-edge gain has a useful invariant absent from normalized derivative.
If an active row is rescaled by s_i>0, d_i is divided by s_i and alpha_i is
multiplied by s_i. The product alpha_i*f(d_i) and the actual endpoint are
unchanged. The comparator uses endpoint-coordinate tie breaking, so its choices
are unchanged under positive row rescaling as well. Its exact small replay
checks this. Affine invariance of that tie break is NOT asserted.

## 5. Exact tests and interfaces

    python3 scripts/test_normalized_gain_barrier.py
    python3 scripts/simple_tangent_policy_audit.py \
      fixtures/capped_klee_minty_5_input.json --policy full_gain --output /tmp/route.json

The test generates fixture inputs itself; run it before the second command.
The two scripts are self-contained except for SymPy used ONLY in independent
small reference graph enumeration. The route producer does not receive an
image/source graph or a neighbor list. It receives an original-H presentation,
a simple source vertex, and a target with its strict finite exposing certificate.
Degenerate/non-simple or unbounded local inputs fail explicitly, not with a
false nonedge or infeasibility conclusion. These are direct original-H routes,
not arbitrary projection lifts. Broader #248 image interfaces remain separate.

Full route audit d=2..12: 5,464 normalized-policy edges and 77 full-gain edges,
165 genuine-facet anchors, all 11 no-common-facet tests, strict target exposure,
unique normalized gains and maximal original ray steps. All 11 full-gain paths
have matching d-edge lower bounds. Three independent all-basis graphs give
36 vertices,62 edges and endpoint distances2,3,4. Twelve malformed/capped controls
are rejected; auditing succeeds with the inverse producer disabled.

At d16/32/64, only four individually selected steps per dimension are checked.
The enormous route counts in those rows are the all-d mathematical formula,
NOT a claim that the paths were executed or their graphs enumerated. Only
small d2..5 complete traces are written as fixtures; other complete route
checks are executed and summarized. The execution JSON is a derived receipt,
not a Lean or platform verdict. Generic Python correctness, full geometry
formalization and the all-d counting proof are not yet Lean-checked.

## Consequence for the research direction

The max-normalized-gain invariants alone cannot supply the missing polynomial
length bound, even after minimal-common-face reduction, exact edge recognition,
strict improvement, unique choices and original-facet accounting. Any successful
proof using this framework must exploit a more restrictive height-selection
property, choose different rays (possibly adaptively), or bound an alternative
family of routes. The completed-edge comparator is a useful tested alternative,
not such a universal proof. Do not spend another formalization cycle trying
to derive a false polynomial bound from the already refuted invariant set.

No accepted theorem or owned core-walk source is modified. This is a research
and benchmark contribution with an explicit all-dimensional mathematical
argument; it is not a new accepted Prove2Me theorem or an alleged solution of
Polynomial Hirsch. The positive d+1 path and shorter certified test paths make
that distinction concrete rather than merely disclaiming it.
