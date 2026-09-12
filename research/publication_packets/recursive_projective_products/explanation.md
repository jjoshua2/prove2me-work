Induct on the geometric ProductTree. At a leaf, apply the already-Proved
small-excess H-polyhedron theorem. At an affine node, transport extreme points,
ordinary edges and the padded walk through the given affine equivalence.
At a split, use the inductively obtained factor bounds and the Cartesian-product
walk construction to add their costs. The row and coordinate equivalences imply
sum_i(counts_i-dims_i)=n-d. The row identities identify the feasible product with
the source polyhedron. Finally transport this exact cost through the positive
projective chart, proving its inverse, slack scaling, segment/extreme-set and
ordinary-edge preservation explicitly.

The submitted proof contains the transport, product-walk and row-count proofs.
Its only imported diameter theorem is the already-Proved excess-at-most-three
bound. The separate local driver retains this input as an explicit premise and
has a standard-axiom audit. The registered ProductTree definition has only
geometric constructors; it does not contain a diameter-bound premise.

No recognition-completeness, JSON-to-Lean certificate translation, universal
carrier factorization or resolution of Polynomial Hirsch is claimed here.
