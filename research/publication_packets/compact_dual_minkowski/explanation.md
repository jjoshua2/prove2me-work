# Compact dual sufficiency for Minkowski erosion

Let a_1,...,a_m be continuous real linear functionals on a real normed vector
space E. Let Q be compact and convex and let h_i bound a_i on Q. Write

R = {x : a_i(x) <= b_i for every i},
P = {p : a_i(p) <= b_i-h_i for every i}.

Then R = P+Q if and only if, for every x in R and every nonnegative weight
vector w, some q in Q satisfies

sum_i w_i (a_i(x)+h_i-b_i) <= sum_i w_i a_i(q).

The same q need not work for different weighted tests. The theorem proves
that passing ALL these tests gives one q that satisfies every original row
simultaneously, which in turn supplies the decomposition x=(x-q)+q.

## Proof

First prove a compact theorem of the alternative. If a compact convex set
K in R^m does not intersect the nonnegative orthant, Mathlib's geometric
separation theorem gives a continuous linear functional f which is
nonnegative on the orthant and strictly negative on K. Its coordinate
coefficients w_i=f(e_i) are nonnegative. Expanding each vector in the coordinate
basis yields f(z)=sum_i w_i z_i. Thus the assertion that every nonnegative
weighted test is nonnegative at some point of K contradicts separation.
The reverse implication is immediate.

Apply that result to the compact convex slack image
K={ (a_i(q)-r_i)_i : q in Q }. This proves that the simultaneous inequalities
r_i<=a_i(q) have a solution q in Q exactly when every nonnegative weighted
combination is satisfied somewhere in Q.

For a fixed x in R, take r_i=a_i(x)+h_i-b_i. Simultaneous feasibility says
x-q lies in P. This proves R subset P+Q. Conversely, a_i(p)<=b_i-h_i and
 a_i(q)<=h_i imply a_i(p+q)<=b_i, proving P+Q subset R. Necessity of the
weighted tests follows from the same inequalities.

## Scope and relationship to the Hirsch work

This closes the unrestricted-dual sufficiency step of the candidate-extraction
argument: whole-polyhedron equality, not merely necessary inequalities or
sampled point reconstruction. It uses the established Mathlib separation
theorem; no Farkas, feasibility, circuit-generation, or diameter axiom is added.
The original polyhedron need not be bounded, simple, full-dimensional, or
nonempty. The candidate need not be a simplex, full-dimensional, or nonempty.
Continuity of the finite family of functionals, compactness and convexity of
Q, and the support upper bounds remain explicit.

The theorem still quantifies over ALL nonnegative weight vectors. A future
bridge must show that the finite positive-circuit lists used by the exact
extractors imply these tests. This packet does NOT certify completeness of
those Python enumerators, find a useful candidate Q, construct a short edge
route, or resolve Polynomial Hirsch. It supplies one reusable geometric lemma
needed to turn the finite extraction evidence into a complete formal chain.

This is a classical separation consequence, not a claim of a new general
convex-geometric theorem. The specific original-inequality erosion interface
and its complete standalone formal proof are the present contribution.

## Verification provenance

The proof is self-contained apart from Mathlib at the repository pin. Its
key API, ProperCone.hyperplane_separation and ProperCone.mem_positive, was
checked against commit c5ea00351c28e24afc9f0f84379aa41082b1188f. All helper
lemmas are proved in solution.lean; the public theorem is top-level solution.

The originating container had no Lean/Lake executable, and external toolchain
downloads failed. No local compilation is claimed. A single isolated hosted
verification/publication request is intended for this frozen packet under the
user's new comment gate; a failed build must never be described as acceptance.
The Actions result and authenticated Prove2Me verdict must be recorded
separately. PR #210's active publication is not changed or triggered here.
