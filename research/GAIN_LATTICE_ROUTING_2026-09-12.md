# Quantized gain cycles: a compact all-basis certificate beyond magnitude balance

## Status, contribution, and boundaries

This is an add-only continuation of PR #210 from
`a8b93f3b0e9198517d77b65996d8694a3799ebfe`. Existing signed, network, and
Minkowski files are not changed. The exact shadow state machine in
`scripts/signed_basis_shadow.py` is reused through a subclass; its source hash
is recorded separately. No workflow, pin, publication packet, or Prove2Me status
is changed by this continuation.

The new mathematical result is a compact, verifiable **all-basis inverse bound**
for two-variable inequalities with genuinely inconsistent magnitude cycles.
It does not assume every cycle gain has magnitude one. Instead, cycle magnitudes
must lie in powers of a supplied rational base q>1. Exact potential balancing
controls path amplification; the integer cycle lattice controls near-cancellation.
These two controls are both necessary to the argument.

A useful explicit consequence is a uniform quartic ordinary-edge bound for a
calibrated family with q=1+1/(dR) and balanced edge exponents of magnitude at
most R. There may be arbitrarily many magnitude-unbalanced cycles, arbitrarily
many rows, arbitrary right-hand sides, and arbitrary positive original row or
coordinate scales. For fixed R this is a polynomial in dimension alone.

The ordinary-edge diameter consequence uses the **classical** wide-normal-cone
result of Dadush--Haehnle, not a newly claimed shadow-simplex theorem. A finite
route constructor now also accepts arbitrary rational two-variable gains, but
outside the certified regimes its success is an instance certificate, NOT a
uniform polynomial diameter or runtime result. No theorem is inferred merely
from a sampled pivot sequence being short.

The two new Lean modules contain finite cycle/gap and conditioning-obstruction
cores plus a selected-carrier route adapter. They are UNCOMPILED candidates.
The complete gain-graph extraction, all-basis theorem, analytic normal-cone
application, and full routing algorithm are not all end-to-end Lean declarations.

## 1. The exact normal form and what the recognizer discovers

Given rational rows with at most two nonzero coefficients, orient the support
of a binary row by i<j. Its homogeneous equation has the form

    z_j = sigma_r * g_r * z_i,   g_r>0, sigma_r in {+1,-1}.

Positive diagonal scaling x_i=s_i*z_i changes g_r to g_r*s_i/s_j. A positive
row scale does not change g_r. Choose a spanning forest of the support multigraph
and propagate positive s_i so every forest gain becomes one. This step works
for arbitrary rational gains; it does not assume cycle consistency.

For each remaining row, compute its exact residual magnitude. The certificate
requires that it be q^ell_r for an integer ell_r, for the supplied q>1. All
signs are retained. Forest rows have exponent zero; chord exponents represent
fundamental cycle gains. Integer exponents are found by exact rational-power
comparison, not floating logarithms or integer factorization. For reduced
q=U/V>1, a positive power has numerator U^ell, so the numerator bit length gives
a finite exponent-search bound. Failure means this base does not certify the
input; it does not mean a large diameter or an infeasible polyhedron.

The base q is supplied, not automatically discovered for every rational matrix.
The arbitrary original tree gains and unknown positive coordinate scales need
not themselves be powers of q. They are absorbed before the chord test.

### Spread the residual exponents instead of hiding them in one chord

A further coordinate scale q^p_i changes an exponent to

    ell'_r = ell_r + p_i - p_j.

For an integer radius R, requiring |ell'_r|<=R is precisely the difference
constraint system

    p_j <= p_i+ell_r+R,   p_i <= p_j-ell_r+R.

Bellman--Ford either supplies integral potentials or a negative cycle. Binary
search finds the smallest feasible integer R. The final certificate contains
only the resulting positive diagonal, original-row exponent identities, and a
negative-cycle witness for R-1. The independent verifier does not rerun the
balancing search.

The lower-radius witness is stronger than a failed integer search: summing its
constraints cancels ANY real potentials. Thus R-1 is infeasible even among real
logarithmic coordinate scales. This proves optimality of the integer radius;
it does not claim that R is the exact optimum over fractional radii or that the
resulting gauge optimizes the actual Euclidean condition number.

## 2. A gain-component kernel works for arbitrary rational gains

Propagate signed multiplicative weights from a root in each connected support
component. If all edge equations agree and no unary row occurs, the homogeneous
solutions on that component are one free scalar times its propagated weights.
A unary row pins the scalar to zero. Any inconsistent signed gain cycle also
pins it: it gives t=G*t for G!=1. This is not infeasibility, because homogeneous
zero remains a solution.

Therefore the homogeneous kernel dimension equals the number of unpinned,
consistent components. This handles parallel rows, arbitrary signs, dependent
row collections, zero rows, and magnitude-inconsistent cycles. The code verifies
its returned kernel vectors against every supplied row.

Deleting one row from a nonsingular d-row basis leaves a one-dimensional kernel.
Choose its weighted-component generator g. If the deleted row is a, its inverse
column is exactly

    g/(a.g).

The denominator is nonzero by nonsingularity. This identity gives an exact
sparse basis inverse for arbitrary two-variable rows. Only the following extra
argument supplies a *uniform bound* on those columns.

## 3. The all-basis theorem: path amplification divided by cycle separation

Apply the certified diagonal scale and positively normalize each row so its
largest coefficient magnitude is one. Unary rows then have coefficient +/-1,
and every row has Euclidean norm at most sqrt(2).

Let T be the sum of the d-1 largest absolute residual binary exponents, using
all original row occurrences. If there are fewer than d-1, sum all of them.
Set

    Gamma = q^T.

Every simple support path uses at most d-1 distinct rows. Its absolute gain
product, in either direction, is therefore between 1/Gamma and Gamma. In
particular T<=(d-1)R. This bound does not enumerate paths.

Choose a spanning forest and take g to be the gcd of all fundamental cycle
exponents. Every closed-walk exponent is an integer multiple of g: gauge the
forest to zero, then sum the signed chord residuals. Define

    eta = 1                   if g=0,
    eta = 1-q^(-g)            if g>0.

For EVERY cycle whose full signed gain G is not one,

    |1-G| >= eta.                                             (1)

A sign-negative cycle has |1-G|=1+|G|>=1. A sign-positive nontrivial cycle has
magnitude q^k with a nonzero multiple k of g. If k>0, q^k-1>=q^g-1>=eta; if k<0,
1-q^k>=1-q^(-g)=eta. When g=0 all magnitude cycles are balanced, so only negative
sign cycles can pin a basis component and their gap is two.

### All-basis inverse bound

For every nonsingular normalized square basis B,

    max_ij |(B^-1)_ij| <= U := Gamma/eta.                      (2)

To prove this, delete a row a and let C be the unique free component of its
remaining kernel.

* If a is unary, normalize g to one at that coordinate. Its inverse-column
  entries are path gain products bounded by Gamma.
* If a joins C to a pinned component, the inverse column again consists of
  path products. If the free endpoint carries the smaller row coefficient,
  include the deleted edge in the path, starting at the pinned endpoint.
  That extended path still has at most d-1 edges because at least one vertex
  lies outside C. This avoids multiplying by a spurious second path factor.
* If both endpoints of a lie in C, root g at the endpoint whose normalized
  row coefficient has magnitude one. The denominator a.g is, up to sign,
  1-G for the cycle consisting of a and the path between its endpoints.
  Nonsingularity excludes G=1. The numerator is bounded by Gamma and (1)
  bounds the denominator by eta.

Coordinates outside C are zero. The row cannot avoid C entirely, since it
must kill the remaining kernel. This covers every possible basis, without
enumeration and without a bound on its determinant.

The two factors in (2) have different jobs. Small per-edge exponents alone do
not exclude nearly resonant cycles. A lower bound on each *chosen fundamental*
cycle's individual distance from one is also insufficient, because combinations
of those cycles can nearly cancel. For instance, two chords with fundamental
gains 2 and 2+epsilon are individually far from one, but their two-edge cycle
has gain (2+epsilon)/2 and a basis inverse of order 1/epsilon. The gcd/power
certificate controls ALL closed combinations, not just the chosen generators.

## 4. A new magnitude-unbalanced polynomial regime

Suppose R>=1 and the certified U satisfies U<=6dR. A simple all-dimension family
that guarantees this is

    q=1+1/(dR),    |ell'_r|<=R.

Indeed Gamma<=q^(dR)<=3 by the binomial bound on (1+1/N)^N, and g>=1 implies
1/eta<=q/(q-1)=dR+1. Therefore U<=3(dR+1)<=6dR. When g=0 the old signed-unit
criterion already applies and has U=1.

There is no bound on the number of unbalanced cycles or rows. For R=1, rows
may carry either sign and residual magnitude 1, 1+1/d, or its reciprocal.
Any collection of such rows, with arbitrary RHS values, satisfies the stated
all-basis certificate. Dense support graphs are permitted. The right-hand sides
do not enter this condition, and the original positive diagonal and row scales
may have very large encoding sizes.

### Classical geometric consequence

A normalized row has norm <=sqrt(2), and an inverse column has norm <=U*sqrt(d).
The relative distance of that row to the span of the other basis rows is at
least

    delta = 1/(sqrt(2d)*U).

Every independent subset extends to a basis when the full row rank is d, so
this is a GLOBAL delta-distance property. At an h-dimensional face, orthogonal
projection preserves this property (Dadush--Haehnle, Lemma19). Thus the face's
normal cones are tau-wide for tau=delta/h. Their Theorem3/11 gives

    diameter(face) <= 8*sqrt(2d)*U*h^2
                     * (1+ln(sqrt(2d)*U*h)).                 (3)

This is an ORDINARY-EDGE theorem for pointed full-dimensional intrinsic models,
including unbounded polyhedra and nonsimple vertices. The point case costs zero.

When U<=6dR and 1<=h<=d, elementary inequalities give

    diameter(face) <= 360*R^2*d^2*h^2.                        (4)

For details, use sqrt(2)<=3/2, ln(6sqrt(2))<=ln9<=4,
lnR<=R-1, and ln d<=2(sqrt(d)-1). The logarithmic bracket in (3) is at most
R-1+5sqrt(d)<=5R*sqrt(d). Multiplication yields (4).
At h=d the safe bound is **360 R^2 d^4**, uniform in row count and RHS data
for fixed R. Constants are conservative, not claimed optimal.

**Do not silently replace d by h in (4).** A calibrated ambient quantum need
not remain calibrated to the smaller face dimension. Projection preserves the
original delta; the inherited bound retains d. The implementation reports
360 R^2 d^2 h^2. A separate fresh intrinsic certificate may give a better bound.

As in the preceding signed work, the analytic normal-cone theorem is external,
classically attributed, and not imported as a new Lean axiom. The contribution
is the explicit gain-lattice/all-basis certificate and its exact implementation,
not a newly claimed general shadow-simplex diameter theorem.

## 5. What no affine preconditioner can fix

It is tempting to try to remove every bad gain gap by allowing a more general
linear change of coordinates. A four-row obstruction rules out that approach
for GLOBAL all-basis conditioning.

Consider the row directions e1, e2, p=e1+e2, w=e1+(1+epsilon)e2, with epsilon>0.
After any invertible linear transformation, write the first two transformed
rows as u,v; the other two are u+v and u+(1+epsilon)v. If D=det(u,v), then

    det(p,w)=epsilon D, det(u,p)=D, det(v,w)=-D.

Let s(a,b)=|det(a,b)|/(||a|| ||b||). This is the relative separation of the two
row lines. All four norms cancel in the identity

    s(p,w)*s(u,v)=epsilon*s(u,p)*s(v,w) <= epsilon.             (5)

If every independent row pair had relative separation >=delta, the left side
would be >=delta^2. Hence for EVERY invertible affine coordinate change and
positive row scaling,

    global delta <= sqrt(epsilon).                           (6)

At epsilon=2^-80, delta cannot exceed2^-40. The tests verify the determinant
identity for fifty rational dense transformations, including one that improves
the scale from epsilon to order sqrt(epsilon); the all-transformation proof is
(5), not those samples. Translation cannot help because it changes RHS values,
not row directions.

This is NOT a graph-diameter lower bound. A two-dimensional polytope with these
few row directions can have only a few vertices. Nor does (6) rule out using
only feasible bases, finding a favorable projective model, grouping near-parallel
rows, or a direct combinatorial route. It rules out a uniform all-independent-
bases conditioning proof for unrestricted two-variable systems by affine
preconditioning alone. Our small triangle with epsilon=2^-80 is routed in one
edge even though its global gain bound is enormous.

## 6. Exact original-H routes, also outside the certified class

The gain-component algorithm computes kernels and basis inverse columns for
ANY rational two-variable row system. The new GainModel reuses the previous
SignedModel's parametric-objective and symbolic-RHS state machine unchanged,
overriding its model extraction and inverse operations. All quotient coordinates
are exact weighted-component coordinates of the actual endpoint-common face.
Inconsistent gain cycles pin components; they are not falsely treated as free
translations or infeasibility.

The new independent verifier checks every symbolic basis, positive exposing
weights, multiplier interval, exact lexicographic entering ratio, original
feasibility, shared tight rank d-1, original entering/leaving blockers, and
final endpoint coordinates. Stationary limiting basis pivots remain in the
certificate but are not charged as edges. It also independently validates the
conditioning certificate when supplied; omission or alteration is rejected.

A supplied gain_base requests a gain-lattice certificate. Without that optional
field, arbitrary rational gains can still be routed and verified, but no uniform
length bound is attached. The constructor's finite objective samples are NOT
the exponential random-shift distribution in the classical diameter proof.
There is no claimed polynomial runtime or pivot bound for this particular
sampler or capped degenerate endpoint-basis search. A valid long sampled route
would not invalidate a smaller existential diameter bound, and the verifier
does not pretend otherwise.

## 7. Executed examples and checks

The 32-dimensional example has164 original inequalities and78 checked edges;
the 24-dimensional example has108 inequalities and51 edges. Both have many
magnitude-unbalanced cycles, optimal integer radius1, cycle gcd1, and
q=1+1/d. The graph is not enumerated. Additional positive coordinate rescalings,
row permutations and huge scale ratios are recovered without supplying them.
A four-dimensional cut example has26 vertices, not a cube graph. Its complete
H-graph is independently enumerated for route checks.

A separate48-dimensional integer cycle basis has diagonal49 and cyclic
next-coordinate coefficient48. Its determinant is49^48-48^48, independently
checked by elimination, while every inverse entry after row normalization is
<=2. A comparison near-resonant two-row block embedded in dimension48 has
normalized inverse maximum49: bounded inverse entries really can grow linearly
with d in the new class, unlike the signed half-integral alphabet.

The execution receipt records all final counts and source hashes. Small matrix
checks compare3,258 row collections and1,945 nonsingular bases with independent
Gaussian elimination, plus the two48-dimensional checks. Three hundred rational
orthogonal-projection checks verify inherited relative separation. Four hundred
independent small gauge feasibility checks agree with brute force. Three hundred
sixty calibrated inverse inequalities are checked exactly.

Small independent original-H enumeration yields77 vertices,142 edges and1,461
ordered distances across seven systems, including a genuinely degenerate gain
cycle with zero rows, an implicit-equality face, a nonlattice system, and the
near-resonant triangle. Together with seven larger/scaled runs, the suite
verifies776 route certificates and1,921 actual edge occurrences;33 stationary
basis pivots are not counted as edges. Twenty-five invalid/forged inputs are
rejected. Large cases do not enumerate the ambient graph or all bases.

The evidence is finite computation, not Lean acceptance. The all-dimension
claims are supported by the structural arguments above and the cited analytic
theorem, not inferred from how many examples passed.

## 8. Connection to the same selected-carrier certificate

If each actual selected carrier has its OWN intrinsic gain certificate giving
cost_i<=360 R^2 h_i^4 with a common R, verified #206/#209 supplies sum h_i<=3e.
For h_i<=H this yields

    sum cost_i <=360 R^2 H^3 sum h_i <=1080 R^2 H^3 e.

The actual certificate then assembles

    D+1080 R^2 H^3 e,   or 1+1080 R^2 d^3(n-d) at D=1,H=d.

The new Lean wrapper consumes the actual local routes and their certified costs;
it does not assume arbitrary carriers have these models. If using a single
ambient gain model instead, use (4)'s ambient-dimension dependence rather than
claiming face-by-face recalibration for free.

The remaining boundary is unrestricted cycle-gain resonance, multiple unrelated
multiplicative scales, or nonsparse rows. The new certificate handles a genuine
family of magnitude-inconsistent systems and shows exactly why checking only
individual fundamental gaps or hoping for arbitrary affine preconditioning
cannot by itself settle the unrestricted problem. Polynomial Hirsch is not
proved by this continuation.

## Primary attribution

Daniel Dadush and Nicolai Haehnle, *On the Shadow Simplex Method for Curved
Polyhedra*, arXiv:1412.6705; SoCG2015, DOI10.4230/LIPIcs.SOCG.2015.345.
Theorem3/11 supplies the wide-normal-cone graph-diameter bound; Lemma19 proves
preservation of delta-distance under orthogonal projection. Full primary text:
https://arxiv.org/html/1412.6705 .

The existing2026 circuit-diameter result for general TVPI remains a circuit
result, not an ordinary-edge justification for cases without this certificate:
Dadush--Kober--Koh, arXiv:2602.05699, Corollary6,
https://arxiv.org/html/2602.05699 .
