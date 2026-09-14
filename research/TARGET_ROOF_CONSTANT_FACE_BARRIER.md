# Target-facet hiding: an exponential constant-face phase despite adaptive locking

## Result, scope, and provenance

Research continuation from main `8a124f0e9db9d330cc3733b7ca39cf37ec0219ae`.
It preserves #249's selector/auditor and #250's accepted midpoint face-locking
proof. The latter proves that restricted-face edges are original edges and
that acquired target faces are preserved; it does not assert a polynomial
length bound. This example does not contradict that theorem.

For every d >= 2 there is a rational, bounded, full-dimensional original
H-polytope R_d with exactly **3d genuine facets**, a simple source 0, and a
simple target y uniquely exposed by c, such that:

* Canonical normalized-gain selection with adaptive common-face locking takes
  exactly **2^d+d-2 ordinary edges** from 0 to y.
* Its first **2^d-2 edges** have the WHOLE R_d as the minimal common face with
  y at BOTH endpoints. The first target facet is acquired only on step 2^d-1.
* No acquired target face is ever lost. Every selected normalized direction
  is uniquely optimal on the current face's entire normalized tangent slice.
* There is an explicit, strictly c-monotone **d-edge** route between the SAME
  endpoints, verified using the same original inequalities.

Thus this is an exponential **selector trajectory**, NOT an exponential
shortest-path or graph-diameter lower bound and NOT a counterexample to
Polynomial Hirsch. It rules out a polynomial count from canonical normalized
progress plus adaptive target-face preservation alone. It goes beyond an
example with only an initially full common face: here an exponential whole
phase has no target face available to lock.

The exact policy is h_x = -sum of active original row normals, restricted to
face(x,y), and maximization of c on h_x=1 followed to the maximal ORIGINAL
endpoint. It is a valid choice in #248's broad height/edge interface, but is
NOT asserted to coincide with #248's particular LP-generated default height.
That default executable was not replayed in this continuation. No assertion
about its trajectory follows solely from the canonical experiment.

This is written mathematics and exact research software, **not new Lean or
Prove2Me acceptance**. No uncompiled Lean skeleton, workflow, pin, permission,
secret or accepted source is changed. The unchanged auditor is
`scripts/simple_tangent_policy_audit.py`, Git blob
`73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976`.

## 1. A general target-hiding lemma

Let P be a full-dimensional polytope of dimension d>=2 with irredundant
H-description and c having a unique maximizing vertex v. Let W be the finite
set of its other vertices. Choose y in int(P) so close to v that

    c(y) > max_{w in W} c(w).

Choose d dual vectors r_i with sum r_i=0 and spanning a complement of c.
For example, in coordinates with the last component of c nonzero, take
r_i=e_i^* for i<d and r_d=-sum_{i<d}e_i^*. For sufficiently small eta>0, add

    (c+eta*r_i)(x-y) <= 0,  i=1,...,d.                       (1)

All w in W satisfy (1) STRICTLY and v violates them. The d new normals are
independent: their sum is d*c, and subtracting c leaves a spanning complement.
Consequently y is the unique maximizer of c in the new polytope: equality in
the summed inequalities forces equality in each, then x=y.

Every old nonoptimal vertex retains exactly its old active rows, and every
edge between such vertices survives unchanged. None shares a new target
facet. More strongly, (w+y)/2 satisfies EVERY inequality strictly, so the
minimal common convex face of w,y is the entire new polytope. This is an
explicit strict-interior certificate, not an assumed image-face oracle.

All old facets survive: in dimension at least two each facet has a vertex
other than v, and a sufficiently small relative neighborhood there lies
strictly inside the new inequalities. Each new inequality is a genuine facet
near y, where the old rows are strict and the new normals are independent.
Thus the number of original facets rises from m to m+d, not to an exponential
extension size. Boundedness is inherited; an interior point lies between y
and any retained vertex.

This construction leaves the canonical active-row height and c-derivatives
unchanged at every retained old vertex. It can therefore hide target facets
through a long prefix of a derivative-based trajectory. A rule that also
uses the new target coordinates or inactive rows in another way need not be
preserved. For a general P, choosing eta may use finite vertex information;
no efficient universal preprocessing theorem is asserted by this lemma.
The concrete family below has a closed rational formula and needs none of
that enumeration.

## 2. Explicit rational input, including the objective and target

Use zero-based coordinates j=0,...,d-1. Define the classical Klee--Minty cube

    x_j >= 0,
    U_j(x) = x_j + sum_{i<j} 2^(j-i+1) x_i <= 5^(j+1).

Let

    M = 5^d,
    c_j = 2^(d-1-j),
    eta = 1/(64*d*M),
    y_j = eta*2^j  (j<d-1),       y_(d-1) = M-1/4,
    C = c(y),       Y = sum_{j<d-1} y_j.

Add d new inequalities:

    n_j(x) = c(x)+eta*x_j <= C+eta*y_j,        j<d-1,
    n_*(x) = c(x)-eta*sum_{j<d-1}x_j <= C-eta*Y.             (2)

The target has ONLY these d new rows tight. Their average is c, so equal
positive weights 1/d certify its strict global exposure. Their invertibility
follows by summing the row equations, then recovering the first d-1
coordinates, then the last coordinate since c_(d-1)=1.

To check that y is strictly inside the old cube, for j<d-1,

    U_j(y) = eta*2^j*(1+2j) < 1 < 5^(j+1).

For the last row,

    U_(d-1)(y) = M-1/4 + eta*(d-1)*2^d < M.

All its coordinates are positive. Also

    C = M-1/4 + eta*(d-1)*2^(d-1),
    31/128 < M-C < 1/4.

Every old coordinate is in [0,M]. The absolute perturbation
eta*r_j(x-y) in any new row is at most eta*(d-1)*M <= 1/64.
The old second-highest c-value is M-5*2^(d-1). Therefore EVERY old vertex
except v=(0,...,0,M) lies strictly inside every new roof row. At v each new
row is violated. The crude gap bound is ample; no exponential vertex list is
used to select eta.

The 2d original cube rows remain genuine facets, and the d rows in (2) are
genuine facets by Section 1. The code independently constructs a point tight
on EXACTLY each of the 3d rows, plus a strict interior point. Coefficients and
right-hand sides have O(d+log d) bit length. The input does not hide an
exponential direction or facet list.

## 3. Exponential first phase, with all target faces unavailable

Recall the classical normalized-derivative calculation, included here to fix
the precise policy. Every bit vector beta defines a cube vertex recursively:

    x_j(beta)=beta_j*(5^(j+1)-sum_{i<j}2^(j-i+1)x_i(beta)).

The available widths are positive, and these are all the old cube vertices.
Let T_beta be its active matrix and d_i=-T_beta^{-1}e_i. These rays generate
the ENTIRE tangent cone because T_beta is invertible. The canonical height
satisfies h(d_i)=1. A triangular recurrence gives

    c(d_i)=2^(d-1-i)*(-1)^(beta_i+...+beta_(d-1)).

The unique largest positive derivative toggles the next coordinate in binary
reflected Gray order. The old trajectory from 0 visits every old vertex and
ends at v=(0,...,0,M). For Gray index t, the bit vector is t XOR (t>>1).
This is the classical Klee--Minty mechanism; it is not claimed as new here.

All vertices before v survive the roof strictly. Their active matrices,
heights, objective derivatives and edges to the next retained vertex are
unchanged. Hence 2^d-2 complete old edges are traversed before the edge that
formerly ended at v. The latter is shortened by the first new roof row and
is still a maximal original edge in R_d.

At every old phase vertex x, all old inequalities are strict at y and all new
inequalities are strict at x. Thus (x+y)/2 is strictly interior. This proves
that adaptive restriction to face(x,y) is the identity throughout the phase,
not just at its starting pair. There are no newly acquired target faces to
retain and no dimension drops to count during those 2^d-2 edges.

The untrusted triangular-ray producer is separately checked by the unchanged
#249 auditor: T*D=-I, positive normalized gain, the global tangent-optimality
dual identity, every original ratio/blocker, and the actual final coordinates.
No supplied neighbor graph, auxiliary circuit movement, or partial ray step
is counted as an ordinary edge.

## 4. The locked final phase takes exactly d-1 more edges

Put p=d-1, D=M-C, and for 1<=r<=p define

    A_r=sum_{j<r} c_j,
    s_r=(D-r*eta*2^p)/(A_r-eta).

The state z_r has

    (z_r)_j=y_j+s_r for j<r;   (z_r)_j=0 for r<=j<p;
    (z_r)_(d-1)=M-2*sum_{j<p}c_j*(z_r)_j.

It is tight precisely on the first r new positive roof rows, the p-r remaining
old lower rows, and the last old upper row U_(d-1)=M. Thus it is simple.
The first roof hit on the formerly final cube edge is z_1. Every other row
is strict there. Useful estimates are

    Y < s_r < 2^(-d),          0 < (z_r)_j < 2^(1-d) when j<r.

They imply strictness of all earlier old upper rows, positivity of the last
coordinate, strictness of the unacquired positive roof rows, and strictness
of n_* because (r+1)*s_r exceeds the unassigned sum of y_j.

After locking the first r target rows, the permitted unit-height rays release
one remaining lower row j>=r or the last old upper row. Solving the active
linear equations gives their c-derivatives:

    release lower j:       eta*c_j/(A_r-eta),
    release last upper:    eta/(A_r-eta).

When r<p, the uniquely largest is j=r, since c_j are descending powers of two
and every remaining c_j>=2. Its maximal endpoint is z_(r+1): the next new
roof row becomes tight and all other inequalities remain feasible/strict as
just described. At r=p only the last-upper release remains; its maximal
endpoint is y, acquiring n_*.

Therefore the adaptive canonical path has

    (2^d-1) + (d-1) = 2^d+d-2 edges.                        (3)

Every newly acquired target facet remains locked. This proof concerns the
specified canonical normalized policy. It does not identify an arbitrary
LP-produced height witness with that canonical height.

The locked-step verifier checks the full restricted-slice dual identity.
Multipliers of locked rows may have either sign because those rows are now
equalities; every other inequality multiplier must be nonnegative. It also
checks all original-edge and maximal-endpoint equations. Counting rows locked
is not substituted for checking an actual edge of R_d.

## 5. A d-edge route: the same polytope is not far apart

Start by increasing only the last coordinate. Its first blocker is n_*, at

    w_empty=(0,...,0,C-eta*Y).

This is one complete original edge. For I={0,...,r-1}, r=0,...,p, let
H_I=sum_{j not in I, j<p}y_j and define

    (w_I)_j=y_j+H_I/(r+1) for j in I;  0 otherwise,
    (w_I)_(d-1)=C-eta*Y-sum_{j<p}(c_j-eta)*(w_I)_j.

Every such point is on n_*. Its other active rows are the positive roof rows
indexed by I and the old lower rows indexed by its complement. The mixed
active matrix is invertible: the selected-coordinate block is identity plus
an all-ones matrix, and the last coefficient is one.

The other new rows are strict since their deficit is
eta*(H_I/(r+1)+y_j). All old upper rows and the last old lower row are strict.
For example (w_I)_j<=2Y and

    2Y*sum_{j<p}c_j < eta*2^(2d) = (4/5)^d/(64d) < 1/128,

so the last old upper row remains below M by more than 1/4-1/64. The earlier
upper-row bounds are even looser. Consecutive points share d-1 independent
original rows and exchange exactly one active lower row for a roof row.
They are therefore actual maximal original edges, not chords in a section.

Since

    c(w_I)=C-eta*H_I/(r+1),

each addition to I strictly improves c. At I={0,...,p-1}, w_I=y. The complete
route has 1+p=d edges. This is an all-dimensional constructive upper bound
for this ENDPOINT PAIR, not a claim about all pairs of the polytope.

The classical greatest-COMPLETED-edge-gain comparator is also executed on the
same inputs. It uses d edges for every tested d=2,...,12 and loses no target
facet. Those comparator trajectories are finite observations; this packet
does not prove a universal polynomial guarantee for that rule or a new pivot
rule. Independent complete small graphs confirm distances d for d=2,3,4.

## 6. Actually executed evidence

    python3 scripts/test_target_roof_phase_barrier.py
    python3 scripts/target_roof_phase_barrier.py --dimension 5 --output /tmp/roof.json

Stages can be run with --dimension d, --aux, and --assemble. Assembly rejects
stages from different source hashes. The CLI phase output stops at the first
target-face acquisition and is explicitly not labeled a completed route;
the test suite executes and audits the complete adaptive route as well.

All d=2..12 trajectories are FULLY executed. Totals:

- 8,243 canonical locked original edges;
- 8,166 edges with the full current/target common face at both endpoints;
- 8,177 steps before and including first target-facet acquisition;
- 77 explicitly constructed comparison edges and 77 completed-gain edges;
- 231 relative-interior anchors certifying every genuine original facet;
- 17 rejected forged, malformed, or deliberately capped cases.

At d=12 there are 36 genuine original facets, 4,094 constant-full-face edges,
first acquisition on step4,095, and 4,106 total canonical locked edges. The
explicit comparison and completed-gain routes each have12 edges.

Complete independent SymPy enumeration in d=2,3,4 gives respectively
6/14/30 vertices and6/21/60 edges, all simple, with source-target distances
2/3/4. All three route types are checked against these independently recovered
graphs. No larger graph is enumerated.

At d=16,32,64 ONLY FOUR SELECTED phase steps per dimension are executed.
The enormous counts printed there are labeled all-dimensional FORMULAS,
not executed exponential routes. The large comparison route is also labeled
formula-only in those checks. Every selected step has a strict midpoint and
is checked by the old original-row auditor.

The complete stored route auditor works with inverse discovery disabled.
Floats, false inverse columns, omitted active rows, partial steps, false
blockers, missing prefix/tail, wrong target weights/objective, changed inputs,
and falsely strict midpoints are rejected. These are exact arithmetic tests,
not Lean extraction or a platform theorem verdict.

## 7. Conjecture-facing implication

Adaptive target-face locking fixes the earlier capped example but cannot,
by itself, supply the missing polynomial bound WITHIN an unchanged face.
The new roof hides every target face until an exponential old trajectory has
already occurred. This makes the exact remaining obstacle concrete without
weakening the accepted face-discovery or edge-transfer theorems.

A successful positive proof must use something beyond this canonical local
normalized derivative: for example a selector with a separately proved
phase-exit guarantee, additional structural hypotheses on the original
polytope, objective changes, or a controlled family of routes. The completed-
gain comparator is useful evidence, not such a general theorem. Merely
counting face drops or replaying more Klee--Minty examples would not establish
Polynomial Hirsch.

The accepted #244 core/fibre assembly and #250 minimal-face theorem remain
separate live work. No competing formalization or Prove2Me resubmission was
created in this research continuation.

## Primary context

John Fearnley and Rahul Savani, *The Complexity of the Simplex Method*,
arXiv:1404.0605, https://arxiv.org/abs/1404.0605 . The exponential Klee--Minty
behavior of Dantzig's rule is classical, not claimed new here.

Yaguang Yang, *A double-pivot simplex algorithm and its upper bounds of the
iteration numbers*, arXiv:1910.10097, https://arxiv.org/abs/1910.10097 .
The repository's #249 note records the same explicit powers-of-two/five
normalization used here and its independently audited tangent identity.

New content here is the target-hiding roof lemma, the explicit rational
family, the constant-full-face lower trajectory and exact locked tail,
plus the contrasting same-endpoint d-edge route and reproducible audits.
No historical priority claim for all variants of target perturbation is made.
