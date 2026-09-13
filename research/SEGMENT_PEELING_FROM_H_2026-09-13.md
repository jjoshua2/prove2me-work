# Recover a coarse polytope from final inequalities: maximal segment peeling

## 0. The input gap this continuation closes

Base: PR #210 at `3d6c15df0c1abb539c912bb7de7393b115b81344`.
Earlier wall-refinement work routes in a supplied Minkowski representation
R=P+sum[0,g_j]. It needs a parent P, a short parent route, and the added summands.
This continuation does not ask for those objects. It starts with the FINAL
rational H-system R={x:Ax<=b}, two endpoint vertices, and a finite list of
CANDIDATE DIRECTIONS. It discovers maximal removable lengths, proves the whole
Minkowski equality, recognizes an affine positive-feedback core when available,
and then invokes the previous route lifter unchanged. The final output edges
are independently checked against the original final H-inequalities.

The main recognition theorem works for ANY nonempty compact H-polytope and a
specified direction. It is not restricted to a small rank, a network matrix,
wide cones, or a known summand representation. Candidate-direction discovery
and recognizing/routing an arbitrary residual core remain unsolved here.

There are three substantive statements:

1. The maximal removable segment parameter in a direction is the minimum full
   parallel-fiber length. It is computed using at most m_+*m_- linear programs.
   Nonnegative original-row combinations certify the GLOBAL equality, while a
   feasible shortest-fiber witness proves maximality.
2. Adding a transverse segment does not change this capacity. Consequently
   maximal extractions along fixed pairwise nonparallel directions commute;
   no search over extraction order is necessary.
3. Sequential redundancy certificates and an exact affine feedback-box test can
   expose a hidden short-route core. The previous L+(L+1)q lift then becomes an
   ORIGINAL-H route constructor without a supplied parent or parent route.

Minkowski summands, erosion, positive row implications, and polyhedral LP duality
are classical. Shephard's normal-fan/edge characterization of summands is recalled,
for example, in Jochemko--Ravichandran (2022), Theorem 2.2. Deza--Pournin (2019)
study Minkowski diameter and decomposability. No claim of priority for every
version of the elementary fiber or summand identities is made. The contribution
here is their exact H-only certificate form, maximality/order arguments, and
end-to-end integration with actual original-edge routing.

The two new Lean files are UNCOMPILED candidates. The full proofs below are
mathematical arguments; the exact executable tests are separate evidence. No
hosted gate, platform submission, or general Polynomial Hirsch conclusion is
claimed. Earlier code, workflows, pins, and publication packets are unchanged.

## 1. Erosion is easy; equality is the real obligation

Fix a nonzero direction g and a nonnegative parameter t. Write alpha_i=A_i g.
The endpoint erosion is exactly

    E_t = R minus_Minkowski [0,tg]
        = {p: A_i p <= b_i-t*max(alpha_i,0) for every i}.      (1)

Here erosion means p+[0,tg] is contained in R. Convexity makes it enough to
check both endpoints. Thus E_t+[0,tg] is ALWAYS contained in R.

Nonempty E_t is not a sufficient summand test. In the triangle
x>=0,y>=0,x+y<=1, eroding by a horizontal segment of length1/4 leaves a nonempty
triangle, but adding the segment back misses the original top vertex. Every
positive horizontal segment fails the true Minkowski equality. The regression
checks both its zero capacity and its nonempty positive erosion.

For x in R define the full line-fiber parameter endpoints

    U(x)=min_{alpha_i>0} (b_i-A_i x)/alpha_i,
    L(x)=max_{alpha_j<0} (b_j-A_j x)/alpha_j.

Compactness and g!=0 ensure that both index sets are nonempty. Because x is
feasible, L(x)<=0<=U(x). The full fiber is exactly
{x+s*g:L(x)<=s<=U(x)}. Its parameter length U-L is independent of which point
x on that fiber is used.

We have the equivalence

    R = E_t+[0,tg]
      iff EVERY nonempty full g-fiber has length at least t. (2)

Necessity: a g-parallel fiber of a Minkowski sum with [0,tg] is the corresponding
fiber of its other summand extended by t. For sufficiency, take arbitrary x in R
and set s=max(0,t-U(x)). Then 0<=s<=t. Let p=x-s*g. The inequality U-L>=t implies
-s>=L and t-s<=U; hence p,p+t*g are in R. Therefore p is in E_t and x=p+s*g.
This explicit formula, not an assumed decomposition, proves reverse inclusion.

The formula also constructs a feasible point in the eroded H-system, even when
maximal removal makes the residual lower dimensional. The numerical routine
returns and independently validates that point.

## 2. Compute the exact capacity from opposing row pairs

For alpha_i=a>0 and alpha_j=-beta<0, define

    v_ij = beta*A_i+a*A_j,
    C_ij = beta*b_i+a*b_j,
    Delta_ij(x) = (C_ij-v_ij*x)/(a*beta).

The vector v_ij annihilates g. Also

    U(x)-L(x) = min_{i positive, j negative} Delta_ij(x).

Thus the largest removable parameter is

    mu_g(R)=min_{i,j} [C_ij-max_{x in R}(v_ij*x)]/(a*beta).   (3)

Each maximization is an ordinary linear program on the ORIGINAL inequalities.
There are at most m_+*m_-<=m^2/4 pairs. No projection facet list, vertex list,
edge graph, circuit list, or guessed parent model is needed. Redundant original
rows may increase the number of pairs but do not change the answer.

Equation (3) is also meaningful for supported unbounded H-inputs whose g-fibers
have finite two-sided bounds, provided its LPs have finite optima. The code
returns an explicit failed search if a required objective is unbounded. All
uniform summand/order statements in this note are stated for compact polytopes;
the Lean sufficiency theorem itself needs only finite positive-row data and
the stated pairwise inequalities, not compactness.

### Finite proof of the whole equality

For each opposing pair the certificate gives a nonnegative vector lambda_ij
on ORIGINAL rows such that

    sum_k lambda_k A_k = v_ij,
    sum_k lambda_k b_k <= C_ij-t*a*beta.                     (4)

For every x in R, multiplying its inequalities by lambda and summing yields
v_ij*x<=C_ij-t*a*beta. Thus every pair width is at least t. Equations (2)--(4)
prove R=E_t+[0,tg] globally; the checker is not sampling feasible points or
assuming that the proposed summand fits because its endpoints happen to fit.

The certificate has sparse positive multipliers with exact rational entries.
Verification checks every normal identity, every constant inequality, and the
complete opposing-pair coverage. It never calls LP discovery.

### A sharp upper witness, not just a successful extraction

One pair i*,j* and feasible point x* attain the capacity. Their Delta is t.
The global lower certificates imply the full fiber there cannot be shorter,
while this pair implies it cannot be longer. Its actual endpoints are computed
and checked against every original inequality.

This also proves that no OTHER summand P can satisfy R=P+[0,sg] with s>t.
Write x*=p+r*g in such a decomposition. Feasibility of p bounds the backward
portion using row j*, and feasibility of p+s*g bounds the forward portion using
row i*. Their sum is the same pair width, forcing s<=t. Maximality is therefore
not limited to the erosion chosen by the implementation.

The code normally removes the maximal amount. Its single-step API also accepts
any smaller nonnegative requested amount, with the same sharp capacity evidence.

## 3. Maximal transverse removals commute

For compact polytopes and nonparallel nonzero g,h,

    mu_g(K+[0,s*h]) = mu_g(K),   s>=0.                       (5)

First, any fiber of K+[0,s*h] contains a translate of some full g-fiber of K.
Therefore its length cannot be smaller than mu_g(K).

For the reverse inequality project along g. Write Z=pi_g(K). A minimum-length
g-fiber occurs above a VERTEX of Z. One elementary proof is to express any
projected point as a convex combination of projected vertices. The corresponding
convex combinations of their fiber endpoints lie in K, so its fiber length is
at least the same combination of vertex-fiber lengths. Hence the minimum over
all fibers is attained among those vertex fibers. This works also when Z or K
is lower dimensional.

Let z be such a projected vertex. Its exposing normals have nonempty interior
in the full dual space of the quotient. Since h is not parallel to g, choose
one such normal c with c*h!=0. The c-exposed face of K is precisely the shortest
g-fiber over z, while the c-exposed face of [0,s*h] is a singleton. The exposed
face of their sum is therefore a translated copy of that fiber. Its projected
support is a singleton, so it is an entire fiber of the sum. This realizes the
same minimum and proves (5).

If R=P+[0,mu_g(R)*g], (5) applied with g,h exchanged says mu_h(P)=mu_h(R).
Inducting gives order-independent capacities for a finite list of pairwise
nonparallel fixed oriented directions. The residual H-description is exactly

    A_i x <= b_i-sum_j mu_(g_j)(R)*max(A_i g_j,0),             (6)

so its right-hand sides commute as well. No exponential search over the order
of candidate directions is required. The test exercises all24 orders of four
planar segment directions, including successive dimension drops to a point.

Parallel duplicates are NOT covered by (5). After maximally removing one copy,
that same direction has zero remaining capacity. Direction rescaling changes
its scalar parameter, and reversing orientation can translate the residual;
the order statement fixes each oriented input vector. The tests explicitly
retain the zero-capacity repeated-direction case rather than charging another
copy for free.

This is a statement about segment summands. It does not establish analogous
commutativity for arbitrary higher-dimensional Minkowski subtraction, or say
that the remaining polytope is indecomposable into nonsingular summands.

## 4. Recover a short-route core without being given its chart

After all certified removals, the same row normals A describe the residual P
with the shifted right-hand sides (6). Some inequalities have become redundant.
The code removes them SEQUENTIALLY, each time providing nonnegative combinations
of still-retained OTHER rows implying the removed one. Simultaneously deleting
mutually redundant duplicates would be unsafe; self-dependent or already-deleted
row certificates are rejected.

The implemented sufficient core recognizer seeks an affine chart in which P is

    y_i>=0,
    y_i<=u_i+sum_j F_ij*y_j,
    u_i>0, F>=0, F_ii=0, and F*w<w for some w>0.             (7)

This is the positive-feedback box condition already used in the broader project,
not a new conjectural diameter oracle. For completeness: the weighted sup norm
makes F a strict contraction. Every principal active system I-D*F is invertible
with nonnegative inverse. For each lower/upper choice pattern D, solve
(I-D*F)y=D*u. This gives a feasible vertex, with a positive coordinate at every
upper choice and zero at every lower choice. A lower and upper row cannot be
tight simultaneously because u_i>0 and F*y>=0. Thus these are exactly all
vertices. Changing one choice shares d-1 independent active rows and gives an
ordinary edge. Every vertex pair is connected in at most d steps.

### What is actually discovered

The discovery routine chooses a simple coarse endpoint as a possible anchor.
Its d tight retained rows, with sign reversed, define y=B(x-anchor). No coordinate
basis is supplied. The other d rows must transform to upper bounds with one
positive coefficient and nonpositive coefficients elsewhere, assigned bijectively
to the coordinates. This recovers F and u. The routine solves (I-F)w=1 and checks
w>0 and Fw<w exactly. The verifier simply checks the stored positive witness.

This recognizer is sufficient, not complete for all affine feedback models:
a selected endpoint may be an unsuitable all-lower anchor even when another
anchor would work. The implementation does not search all2^d corners. Once one
chart is certified, however, it is reused to route arbitrary endpoint pairs;
the tests do so for every pair of the small final polytopes. Maximal peeling may
also leave a lower-dimensional core, which the extractor certifies but the
current full-dimensional2d-row core recognizer need not accept.

### Recover the correct parent endpoints automatically

For an original vertex x use the sum of ALL its tight original row normals as
an exposing objective c. Positive coefficients and full active rank expose x
uniquely. In the proved Minkowski decomposition, every nonzero extracted segment
has a unique c-maximizer: otherwise their sum face could not be a singleton.
Select its upper endpoint when c*g_j>0, or zero when c*g_j<0, and subtract these
choices from x. This recovers the coarse vertex p. Original tight rows remain
tight there with their shifted right-hand sides, so the same positive multipliers
certify the parent exposing objective required by the old lifter.

The core bit-flip route supplies L<=d. The unchanged implicit_minkowski_lift.py
then gives at most L+(L+1)q ordinary edges of P+sum[0,g_j]. Because the decomposition
has been proved equal to the final H-input, these are edges of R. The new verifier
additionally checks every returned point against the ORIGINAL final inequalities,
full vertex active rank, shared edge rank d-1, and both endpoint blockers.

Thus successful recognition provides the all-endpoint sufficient bound

    diameter(R) <= (q+1)d+q.                                 (8)

q counts distinct extracted positive segment directions. Initially common final
facets need not be preserved by the ambient route lifter; for a carrier-specific
application this procedure must be run on a description of the actual carrier.
Neither shortestness nor a universal decomposition premise is smuggled into (8).

## 5. Exact final-H tests, not input summand descriptions

In the small nontrivial feedback examples, the test harness constructs core
vertices, adds one or two segments, and independently reconstructs the COMPLETE
final H-description by supporting-plane enumeration. It then passes only that
final A,b, endpoint coordinates and candidate directions to the new algorithm.
Core inequalities, lengths, chart, and route are not passed. All recovered lengths
and every returned edge are compared with independent final-H vertex enumeration.
This fixture-generation enumeration is test-only, not part of discovery.

The larger family has an explicit final H-form. Let p=d-2 and use the p-dimensional
variable-width star

    0<=x_0<=1, 0<=x_i<=1+x_0 (1<=i<p).

Its planar factor is the zonogon generated by e1,e2, lambda*(1,1), and
mu*(1,1+epsilon), with lambda=3/7 and mu=2/5. The planar inequalities are the
positive and negative supporting perpendiculars to these four generators, each
with its exact support value. There are exactly2d+4 genuine FINAL facets.
The algorithm receives these inequalities, not the segment representation.

For the two supplied candidate vectors (1,1) and (1,1+epsilon), it recovers the
exact parameters3/7 and2/5, removes the now-redundant diagonal planar rows, and
recognizes the star times square. In dimensions12,24,32 it returns respectively
14,26,34 original ordinary edges. The all-endpoint safe bounds are38,74,98.

The32D final input has68 facets and8,589,934,592 vertices by its explicit product
structure, with at least536,870,941 genuine edge directions. Its near-parallel
planar directions are separated by epsilon2^-160. The preceding wall-refinement
cross-ratio argument gives a genuine final cone of width at most2^-80 after any
affine preconditioner, while the recognition/routing bound is independent of
that separation. No graph or full direction dictionary is enumerated here.
This is a new closed-final-H two-segment test family, NOT a claim that the earlier
18-dense-segment example's final H-description has only68 rows.

A separate eight-dimensional case hides the same model behind a dense invertible
rational rank-one shear, unknown translation, row rescaling and row permutation.
Only transformed candidate directions accompany the FINAL transformed H-system.
Both lengths, a valid feedback chart and a ten-edge original route are recovered.
No affine-indecomposability claim follows from dense coordinates: these examples
retain their known affine product structure, and that is why a core is present.

An additional positive control keeps a constant inequality, a loose duplicate,
a coincident rescaled facet and a repeated candidate. Original rows are preserved
through extraction; redundancy has explicit certificates; the third repeated
candidate has capacity zero.

## 6. Complexity and verification boundaries

There are polynomially many LP calls for a supplied list of directions: at most
m_+*m_- per direction before objective caching, then at most m redundancy LPs.
They optimize directly over H-rows, not enumerated vertices. The particular
implementation is exact rational Bland simplex with warm tableaux and an explicit
pivot cap. NO polynomial pivot bound or strongly polynomial runtime is claimed.
Bit sizes and conditioning can affect the discovery work; a cap or unsupported
core reports failure, not geometric nonexistence or a diameter lower bound.

Verification uses exact rational linear combinations, primal/dual equality,
rank checks and the existing supporting-face edge verifier. It invokes neither
simplex nor generic-objective discovery. It does recompute the core's explicit
bit-flip coordinate formula, not a graph search. Discovery statistics are reported
metadata, not proof assumptions. The H equality does not rely on a count of passed
examples or a numerical tolerance.

The two new Lean candidates prove the finite original-halfspace segment equality,
its derivation from positive row certificates, and a sharp upper bound for ANY
candidate summand in that direction. They also prove the elementary RHS subtraction
commutation. The stronger capacity-invariance/order theorem has the complete
convex-fiber proof above and exact tests, but is not a new full Lean declaration.
The feedback recognition, rational simplex and whole integrated routing algorithm
are not kernel-verified merely because these certificate cores exist.

There is no new open root child, circular distance premise, hosted trial workflow,
secret usage, dependency-pin change, or Prove2Me acceptance. The code reuses the
previous wall lifter unchanged, with its dependency hash recorded. Compiling the
new two modules and auditing all eight printed declarations remains the next
verification-agent task.

## 7. Remaining mathematical target

For a GIVEN direction, the extractor now answers a general exact geometry
question, including a maximality witness. For a certified residual feedback core,
the complete path to actual original edges is implemented. This removes a supplied
Minkowski decomposition/route requirement on those inputs.

It does not find every useful direction, guarantee a nontrivial segment summand,
or recognize every possible residual parent. Many polytopes, including the
triangle control, have zero capacity in a proposed direction. Useful coarse
models need not arise from segment subtraction at all. The new complete
direction-wise test should be used to identify or rule out actual decompositions,
not turned into an assumed universal summand theorem.

The next general step is candidate-direction or broader coarse-model discovery
with a bounded resource count. That is now separate from certifying a candidate's
length, decomposition equality, order, and original-edge route; those tasks have
explicit mathematical and executable certificates.

## 8. Executed totals

The completed run checks384 original-H route certificates and1,160 ordinary-edge
occurrences. Three independently reconstructed small final H-polytopes have42
vertices,70 edges and716 ordered graph distances; all379 unordered pairs including
stationary endpoints are routed with the recovered chart. Of these,106 lifts are
longer than the graph distance, explicitly preserving the no-shortestness scope.
The chart is reused for376 cases with a different source than the discovery source.
Four large/dense-affine instances and the duplicate/constant-row boundary case
supply the remaining five certificates. The large graphs are not enumerated.

Independent numerical checks compare160 LP optima and20 directional capacities
with complete small vertex enumerations. All24 orders of a four-direction peeling
agree, including lower-dimensional intermediate cores. Twenty-four forged,
malformed or unsupported cases are rejected. The suite records sequential
Farkas proofs, final original-row edge evidence and exact source/dependency hashes;
its measured runtimes are observations, not algorithmic guarantees.

## References consulted

Antoine Deza and Lionel Pournin, *Diameter, decomposability, and Minkowski sums
of polytopes*, Canadian Mathematical Bulletin62 (2019),741--755,
arXiv:1806.07643, DOI10.4153/S0008439518000668.
https://arxiv.org/abs/1806.07643

Katharina Jochemko and Mohan Ravichandran, *Generalized permutahedra: Minkowski
linear functionals and Ehrhart positivity*, Mathematika68 (2022),217--236,
DOI10.1112/mtk.12122. Theorem2.2 recalls the classical Shephard summand criterion.
https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/mtk.12122

The repository's preceding `IMPLICIT_WALL_REFINEMENT_2026-09-13.md` supplies the
implemented L+(L+1)q route lift. No external analytic normal-width theorem is
needed for the new extractor or for the recognized feedback-core instance route.
