# Direct routes for contractive feedback boxes

This is the mathematical continuation of #204's cyclic negative controls.
It is a paper proof and an exact finite regression, **not a new Lean theorem
or Prove2Me acceptance claim**. The recursive ProductTree theorem is a separate
verified result. This criterion supplies routes without a product separator.

## Statement and finite hypothesis

Let d>=1, let M be an entrywise nonnegative real d-by-d matrix, and let b,w
have strictly positive coordinates. Assume the componentwise strict inequality

```
M*w < w.
```

Then the bounded full-dimensional polytope

```
P(M,b) = {x : 0 <= x_i <= b_i + (M*x)_i for every i}
```

has the ordinary graph of a d-cube, hence ordinary-edge diameter exactly d.
In particular it satisfies n-d for its 2d displayed inequalities.
The witness w is finite data; neither product factorization nor a projective
chart is assumed. The criterion does not apply to arbitrary paired inequalities.

## 1. All principal systems are invertible and positive

Put rho=max_i (M*w)_i/w_i<1. After diagonal scaling by w, M has nonnegative
entries and row sums at most rho. Every principal submatrix has the same
property. Its powers therefore converge to zero in the maximum row-sum norm,
and the geometric series gives

```
(I-M_SS)^(-1) = sum_(k>=0) (M_SS)^k >= I.
```

For every coordinate set S define v(S) by zero outside S and

```
v(S)_S = (I-M_SS)^(-1) b_S.
```

The empty set gives the origin. Coordinates in S are at least b_i>0. Their
upper inequalities are equalities. Outside S, the lower inequalities are
equalities and the upper slacks are at least b_i>0. Thus v(S) is feasible
and has exactly the indicated one active inequality from each coordinate pair.
The active matrix is nonsingular: eliminating the fixed-zero coordinates
leaves precisely I-M_SS. Hence every v(S) is a vertex and distinct S give
distinct vertices.

## 2. Boundedness, interior and completeness of the vertex list

For feasible x, let u=max_i x_i/w_i. At an index attaining the maximum,

```
u*w_i = x_i <= b_i + u*(M*w)_i,
```

so u<=max_i b_i/(w_i-(M*w)_i). This is a finite bound on every coordinate.
For sufficiently small delta>0, delta*w is strictly feasible, since
`delta*(w-M*w)<b`; hence P has full dimension d.

No point of P can have both inequalities in one coordinate pair active:
that would require 0=b_i+(M*x)_i>=b_i>0. A vertex of a full-dimensional
H-polytope has active normals spanning R^d, so at least d active rows. There
are at most d here. Consequently every vertex selects exactly one row from
each pair and is the unique v(S) constructed above. The 2^d vertices are a
complete list, and each has exactly d independent active rows.

Every displayed row defines a facet. For x_i=0, take all other coordinates
strictly positive and sufficiently small. For an upper equality, take the
other coordinates sufficiently small and positive, and solve
`(1-M_ii)*x_i=b_i+sum_(j!=i)M_ij*x_j`. The coefficient 1-M_ii is positive;
the remaining upper bounds stay strict because their right sides are at least
b_j. These give relative interior points of the respective row faces.

## 3. Actual ordinary edges and a constructive route

If S and T differ at exactly one coordinate, v(S) and v(T) share d-1 of the
active rows of v(S). Those rows are independent. Their common row face has
dimension at most one and contains the two distinct vertices, so it is a
one-dimensional face. The segment between them is an ordinary edge.

Conversely, simplicity implies that an edge incident to v(S) retains d-1
of its active facets. With the corresponding d-1 coordinate choices fixed,
there are exactly two vertices in that row face: the two choices at the
remaining coordinate. Thus adjacent vertices differ in exactly one choice.
The vertex graph is therefore exactly the d-cube graph.

To route v(S) to v(T), change each index of the symmetric difference once,
in any order, solving the indicated principal system after each change.
Each step is an ordinary edge. The length is |S symmetric_difference T|<=d;
opposite sets require d steps. The construction uses at most d+1 principal
linear solves for a given pair; it does not enumerate all 2^d vertices.
No claim about bit complexity for arbitrary real input is made.

## 4. The cyclic examples are outside recursive projective products

Take b=w=1 and M=epsilon times the cyclic predecessor permutation, where
0<epsilon<1. The witness inequality is immediate in every dimension, so all
these cyclic feedback polytopes have diameter d. For d>=3 they have no
nontrivial projective product factorization, as follows.

Their facet incidence is cubical by the vertex/edge construction above (more
directly, every consistent partial coordinate choice occurs, by extending it
to complete choices). Each facet has exactly one disjoint mate, namely the
other facet in its coordinate pair. Facets of different Cartesian factors
always meet, so both members of every pair must belong to the same factor.

Normalize any proposed projective chart at the feasible origin; its
nonvanishing denominator there permits this normalization. After subtracting
the image of the origin, its numerator is an invertible linear map, which
can be absorbed into factor coordinates. Thus its row unshearing has the form
`A_i-b_i*c`. The lower normals -e_i are unchanged and form a basis, so each
factor's row-functional subspace is spanned by its assigned coordinate axes.
The upper normal for i becomes `e_i-epsilon*e_(i-1)-c`.

If a cyclic edge k->k+1 crosses factor groups, its upper row forces
c_k=-epsilon. Every other index outside k's group would force c_k=0.
Therefore the entire complement of k's group is the singleton {k+1}.
But the outgoing edge of that singleton crosses again and would force its
complement to be a singleton, impossible for d>=3. A nontrivial partition
of a cycle necessarily has a crossing edge, yielding a contradiction.

For d>=4, this excludes a ProductTree for this displayed system: its excess d
is too large for a small leaf, and affine steps cannot create a projective
product split when none exists. Thus the direct feedback criterion handles
an infinite family outside the recursive small-excess product criterion.
It still handles combinatorial cubes; it says nothing about arbitrary
high-dimensional carriers or a uniform joint cost for the root conjecture.

## Attribution, checks and formalization target

The nonnegative inverse argument is elementary nonsingular M-matrix theory;
no novelty in matrix theory or cube-graph routing is claimed. For adjacent
classical context see Foniok, Fukuda, Gaertner and Luethi,
[Pivoting in Linear Complementarity: Two Polynomial-Time Cases](https://arxiv.org/abs/0807.1249).
Their K-matrix pivoting results concern complementarity orientations; the
ordinary-edge polytope statement here is proved above and does not follow
merely by importing their iteration count.

`test_contractive_feedback_boxes.py` checks selected principal systems against
an independent exhaustive active-row enumeration, verifies the full edge graph,
and rejects violations of the finite hypotheses. Those rational computations
are examples, not a proof of the universal real statement.

The next Lean task is to formalize the active-choice vertex classification
and the d-1-common-active-row edge lemma, then compose coordinate toggles.
Do not add an arbitrary coupled-leaf constructor to ProductTree. A future
selected-carrier adapter must certify an equivalent model of this exact form
for each actual portal pair before charging its intrinsic dimension.
