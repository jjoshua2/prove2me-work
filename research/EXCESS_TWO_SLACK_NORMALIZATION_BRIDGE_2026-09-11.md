# Excess-two slack normalization: exact remaining bridge

Date: 2026-09-11. This is a mathematical derivation and implementation handoff, NOT a Lean-verified declaration or Prove2Me submission.

## Target

Let P = {x in R^h : A x <= b} be nonempty, bounded, and strictly feasible, with m <= h+2 rows. The desired conclusion is DiamLE P 2. Irredundancy is not needed for the argument below, though the common-face application supplies an irredundant presentation and its presentation-independent count.

The normalized two-moment theorem is already public Proved. The dimension-changing injective-affine transport theorem is verified in commit be54654435d3c317d676f3ea03c79d07f089992a. Thus only construction and exact image identification remain.

## 1. Injectivity of row evaluation

If A g = 0, then x+t*g is feasible for every real t whenever x is feasible. Boundedness forces g=0. Hence rank A=h. This uses nonemptiness; do not infer injectivity from an empty polyhedron's vacuous boundedness.

Alternatively, when a reference extreme point is already supplied, PolynomialVertexSpan.vertex_tight_rows_span_checked gives this injectivity directly.

## 2. A strictly positive annihilating row weight

Boundedness implies that {g : A g <= 0}={0}: any nonzero such direction would generate a feasible ray. Therefore the positive hull of the row normals is the whole R^h. A separation/Farkas argument supplies the latter implication.

For each row a_i, choose nonnegative coefficients expressing -a_i as a positive-hull combination of the rows. Add all those representations to the identity sum_i a_i = sum_i a_i. The resulting coefficients lambda_j=1+sum_i c_ij are strictly positive and satisfy sum_j lambda_j*a_j=0. This includes zero or redundant rows; no genericity assumption is needed.

For a strictly feasible point x0, every slack b_i-(A x0)_i is positive. With m>0,

c = sum_i lambda_i*b_i = sum_i lambda_i*(b_i-(A x0)_i) > 0.

Handle h=0 separately: its ambient space has one point, so the diameter claim is immediate. For h>0, bounded nonempty P cannot have m=0. This prevents an unjustified division by c in the zero-row case.

## 3. Diagonal slack embedding

Define f(x)_i = lambda_i*(b_i-(A x)_i)/c.

This is an injective affine map from R^h into R^m. Its linear direction space is U=range(-D A), where D=diag(lambda_i/c) is invertible. Thus dim U=h and its annihilator has dimension m-h <= 2. The coordinate sum functional annihilates U and satisfies sum_i f(x)_i=1.

Let q=f(x0). Since the sum functional is nonzero and lies in the annihilator, extend it to a basis of that annihilator. There is at most one additional functional, represented by coefficients t_i. If the annihilator is only one-dimensional, choose t=0 and mu=0. Otherwise choose the second basis functional and set mu=sum_i t_i*q_i.

The exact affine image is

f(R^h) = {z : sum_i z_i=1 and sum_i t_i*z_i=mu}.

Prove both inclusions. The reverse inclusion uses annihilator completeness/rank-nullity, not just the fact that both displayed equations hold on the image. Establishing only those two equations is insufficient.

## 4. Exact feasible image and graph transport

Since lambda_i/c>0, x is feasible iff every coordinate f(x)_i is nonnegative. Combining this with the exact ambient-image equality gives

f(P) = {z >= 0 : sum_i z_i=1 and sum_i t_i*z_i=mu}.

Apply HirschExcessTwo.momentSlice_diamLE_two, then
Hirsch.affineMap_diamLE_image_iff_of_injective.
This yields the desired actual vertex-edge diameter bound, rather than a bound on an arbitrary feasible-point or circuit graph.

Every additional original-row equality a_i*x=b_i is exactly the zero-coordinate constraint f(x)_i=0. Therefore the same embedding identifies each selected-row equality face with a coordinate support face. The proved intrinsic supportFace_diamLE_two then transfers without using ambient edges outside that face.

## Implementation order

1. Concrete affine slack map; injectivity; exact image as a translated row-evaluation range intersected with the orthant; zero-slack/equality equivalence.
2. Positive annihilator vector from boundedness, with explicit h=0 / m=0 handling.
3. Codimension-at-most-two image characterization using a nonzero sum functional.
4. One end-to-end H-presentation theorem and its intrinsic selected-row-face corollary.
5. Connect the existing common-face strictly feasible irredundant model and row-count invariance: M_min <= commonFaceDim+2 implies intrinsic diameter <=2.

Do not publish steps 2 or 3 as Open conjectural children merely to repackage them. Complete and compile them first. This is a genuine low-excess base case, not an assertion that all circuit carriers have low excess and not a solution of the general Polynomial Hirsch frontier.
