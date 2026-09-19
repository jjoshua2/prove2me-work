# An actual completion, rather than a supplied summand equality

Given any positive-length list of real vectors v_i, put P=conv{v_i}. Construct
Z as the sum of ALL ordered-pair segments [v_i,v_j], using n^2 independently
bounded scalar coefficients. Let Q={q: q+v_i is in Z for every i}. The target
proves compactness and convexity of both Z and Q, nonemptiness of Q, and the
WHOLE-SET identity Z=P+Q. The segment positions are explicit; neither a summand
nor an assumed support-function equality is an input.

## A support witness with every required translation

Fix ANY linear objective f and choose a generator v_k maximizing f(v_i).
In each ordered segment (k,i), select v_k. In every other segment choose an
endpoint maximizing f. Their sum z maximizes f on Z, since every component is
maximal even when the comparison ties. Put q=z-v_k. For every i, changing just
the coefficient in the (k,i) slot from one to zero replaces v_k with v_i.
Consequently q+v_i belongs to Z. This is a witness to membership in the actual
intersection Q, not just to one supporting halfspace. Also v_k+q=z, so every
objective has a maximizing point of Z inside P+Q. For i=k the changed diagonal
segment is stationary, which is harmless and included.

Z is a continuous affine image of a compact coefficient cube. Convexity is
proved on the coefficients using the exact sum-to-one identity. Q is an
intersection of closed convex translates of Z and is bounded by any one of
those translates (n>0 supplies a generator). The zero objective's same witness
proves Q nonempty. Convexity extends q+v_i in Z from generators to every p in P,
so P+Q is contained in Z. The finite hull P and Q are compact, hence P+Q is
closed and convex. A point of Z outside P+Q would be strictly separated by a
continuous linear functional, contradicting the explicit support witness.
Thus equality holds for the complete bodies, not merely sampled objectives.

## Exact scope and remaining quantitative obstacle

No distinctness, irredundancy, rank, independence, full dimension or sign/generic
objective restriction occurs. Repeated and interior generators, collinear
families, d=0 and n=1 are included. Positivity of n matters: an empty generator
family would not supply the translation used for compactness of Q.

The represented segment count is n^2, including zero-length diagonal segments
and duplicate directions. It is NOT an optimal inventory or an original-facet
count. An H-polytope can have a large complete vertex inventory; supplying that
inventory does not give a polynomial bound in its original row count. A large
inventory in this one construction also does not prove that all completions
must be large. This theorem proves no genuine zonotope-edge route, and an edge
of the coefficient cube is not silently identified with an original Z edge.

Accepted #309 and #310 already establish the appropriate contraction and
endpoint lifting once a genuine route bound on a compatible sum is available.
This result supplies an explicit completion for arbitrary finite generators;
the separate genuine-edge route argument and the original-row complexity issue
are still necessary. It does not settle Polynomial Hirsch or improve a known
best classical diameter bound. The classical normal-fan and Minkowski-summand
viewpoint is credited (Deformed Graphical Zonotopes, Discrete & Computational
Geometry,2023, DOI10.1007/s00454-023-00586-x); no historical novelty is claimed.

## Verification boundary

The proof uses pinned Mathlib compactness, convex hulls and strict separation,
not an unproved imported target or a supplied summand theorem. The public type
expands the coefficient body and erosion using only Mathlib symbols and has a
matching top-level solution. Five transitive axiom reports cover compactness,
whole-hull translation, the support witness, completion, and the public root.
The packet uses the committed Lean/Mathlib pin and unchanged publication gate.

No local Lean/Lake executable is available and the compiler host did not resolve.
The prepared standalone proof receives one user-requested new top-level PR
publication comment, not a speculative hosted edit/compile loop. Source checks
and rational tests are not Lean verification; preserve the actual gate result.

The exact standalone rational test reconstructs both polygonal bodies and
checks their WHOLE-SET equality on 46 models, including duplicates, interior
points and lower-dimensional cases. It separately checks 1208 support witnesses,
6627 single-slot replacement identities and 42189 coefficient bounds. Nine
selected examples reach dimension64 without full high-dimensional enumeration.
Nineteen saved witnesses replay with discovery disabled and four forgeries
fail. Clean script-only replay reproduces the full report and fixture exactly.
These are supporting tests, not Lean-extracted Python or a universal JSON audit.
