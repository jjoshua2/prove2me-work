# Discover the exact minimal face of a linear image

## What the formal theorem constructs

Let P={z:a_i(z)<=b_i} and let G be linear. The finite input consists of a
feasible anchor x, exactly its tight original rows J, and for every i in J a
nonnegative original-row dual vector lambda_i and an image functional psi_i:

    -a_i = sum_j lambda_ij a_j + psi_i composed with G,
    -b_i = sum_j lambda_ij b_j + psi_i(Gx).

These are exact zero-slack optimality identities on the fibre Gz=Gx. The anchor
is strict on every original row outside J. No image exposing functional,
source vertexhood, source edge, boundedness or relative-interior oracle is an
input. The strict anchor is finite, directly checkable data, not a quantified
geometric interior assumption.

The theorem constructs an image functional f exposing exactly G(H), where
H=P intersect {a_j=b_j for j in J}. It proves actual Mathlib IsExtreme, and
that G(H) is the SMALLEST extreme subset of G(P) containing Gx. Finally, for
EVERY image submodule W, all differences Gz-Gx with z in H belong to W iff G
sends the selected-row kernel into W. This determines the entire affine
direction space, not merely an upper bound on its dimension.

## Proof of exposure

At the anchor, subtract each dual identity from its attained value. The sum
sum_j lambda_ij*(b_j-a_j(x)) is zero. Every term is nonnegative. Strict slack
outside J therefore forces every lambda_ij outside J to vanish. Summing the
remaining identities produces

    f = -sum_(i in J) psi_i,
    f composed with G = sum_(j in J) (1+sum_(i in J)lambda_ij) a_j.

Every displayed original-row coefficient is at least one. For any feasible z,
the image support deficit is a sum of nonnegative original-row deficits and
vanishes exactly when every row in J is tight. Thus the WHOLE supporting slice
of G(P), not just some listed points, is exactly G(H). The supporting-slice
IsExtreme proof reuses accepted #246 with variable/namespace renaming.

## Minimality and exact image direction tests

If a vector v annihilates every selected row, choose a positive epsilon below
the finite ratios (b_i-a_i(x))/(|a_i(v)|+1) for unselected rows. Then BOTH
x+epsilon*v and x-epsilon*v are feasible and remain in H. The source need not
be compact or full dimensional. This is a direct finite-slack argument, using
the same finite-minimum method as accepted #245, not a topological theorem.

For z in H apply this to v=z-x. The point Gx is a STRICT convex combination of
Gz and G(x-epsilon*(z-x)), with weights epsilon/(1+epsilon), 1/(1+epsilon).
Every extreme subset containing Gx must therefore contain Gz. This establishes
minimality. It prevents using an arbitrary larger supporting face as a claimed
minimal face when deciding an edge query.

If all face differences lie in W, the feasible forward perturbation puts
epsilon*Gv in W; multiplication by epsilon inverse puts Gv in W. Conversely,
any difference z-x from H annihilates the selected rows. This proves both
sides of the submodule test equivalence and justifies rank-one recognition.

## How the executable discovery supplies the finite premises

For a query with distinct feasible image endpoints u,v, use their midpoint
w=(u+v)/2. Two feasibility LPs find source lifts, without requiring source
vertices. On the fibre Gz=w, maximize every original row slack b_i-a_i(z).
A zero optimum gives the exact dual identities above. A positive optimum or
an unbounded-ray witness gives a feasible fibre point strictly slack on that
row. Average all these witnesses and a seed: the resulting anchor is tight
on the forced rows and strict on every other row. The checker simply verifies
those strict inequalities and dual identities; it does not trust averaging,
optimization, rank or any chosen active-set guess.

The proof that a finite optimum has such a dual witness is standard linear
programming duality. This existence/solver termination argument is separate
from the new Lean certificate theorem. The exact LP engine is the unchanged
historical source ea511a79164d953792942d8be3dd3537646738d6, transplanted without
its retired ancestry. It uses capped Bland simplex, not a polynomial pivot
claim. There are polynomially many LP calls for one endpoint query; no complete
source/image vertex graph is enumerated.

## Positive and negative image-edge decisions

If the selected-row kernel has an image direction transverse to v-u, a small
feasible two-sided perturbation gives two image points averaging to (u+v)/2
but outside its line. An extreme segment [u,v] could not contain their midpoint
without containing those points. The negative certificate checks only actual
feasible points and a nonzero two-by-two image minor, not the nullspace search.

Otherwise rational row elimination constructs #246's rank-one image identity
modulo J. Two LPs supply sharp lower/upper original-row witnesses for the edge
coordinate. When the supplied endpoints are the true extrema, the UNCHANGED
#246 arithmetic auditor certifies the entire exposed image segment. When an
endpoint is not extreme, the output instead exhibits a feasible image point
beyond it on the same line. That endpoint lies strictly inside a feasible
segment, directly refuting extremality. Unbounded endpoint objectives supply
such a point from an exact feasible ray.

Thus on feasible distinct rational endpoints, the finite mathematical algorithm
is complete if its exact subroutines finish. A pivot cap or infeasible input
returns an incomplete-query error, NEVER a negative geometric verdict. Neither
the producer, JSON parser nor individual data certificates are Lean-extracted.
The Lean theorem proves the geometric bridge behind the finite face certificate;
#246 separately proves the positive whole-edge certificate.

## Executed evidence and remaining task

The deterministic exact suite checks222 endpoint queries:39 edges and183
non-edges. Six independently enumerated small source systems give49 source
vertices,47 distinct image points and32 image hull vertices. All209 distinct
small image-point pairs are classified against independent planar hulls;
133 queries include a nonvertex image endpoint. The reference systems contain
47 source edges whose projections are NOT image edges. Those projections are
not silently counted as valid steps.

Thirteen further cases include image dimension16, source lineality (NO source
vertices), unbounded fibres, an unbounded image with a bounded edge, an image
ray with no finite edge, lower-dimensional images, constants/duplicate rows,
unknown dense affine source coordinates and near-parallel projections at
2^-120. Seventeen malformed/forged/capped cases are rejected. Rechecking every
boundary certificate still succeeds with all discovery and elimination entry
points replaced by raising stubs. These counts are exact Python evidence, not
Lean verification or a route-length result.

The standalone Lean source has288 lines and six axiom printouts. The current
runtime has no Lean/Lake executable; direct public toolchain-network preflight
failed at DNS. No local compilation is claimed. A prepared pinned final gate
must establish compilation, the transitive standard axioms and authenticated
platform acceptance. There is no new workflow, pin, permission or secret use.

This is a COMPLETE per-pair edge recognizer, not a polynomial-length route
construction. It does not imply that projecting a short source path works, or
that the source row count is the original IMAGE facet count in a Hirsch bound.
The separate #244 core-walk concatenation remains owned by its existing agent.
The conjecture-level task is to select polynomially many genuine image edges
or find another universally controlled carrier model, not to mistake efficient
edge recognition for a proved polynomial diameter.

Primary background: K. Cheung, Linear Programming Duality,
https://people.math.carleton.ca/~kcheung/math/notes/MATH5801/03/3_2_duality.html .
The result is classical polyhedral geometry completed as an exact project
interface, not a historical novelty claim.
