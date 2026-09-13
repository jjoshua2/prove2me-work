# The remaining rank cutoff: an explicit injectivity proof

This is a mathematical next-step note, not a Lean-checked declaration and not
part of the new allocation theorem's hypotheses. The current finite family has
one slot per support. To justify the enumerator's rank-plus-one limit, prove:

For a real linear map A:R^n -> R^k and a nonzero nonnegative null vector z with
minimal support among ALL nonzero nonnegative null vectors,

    |support(z)| <= rank(A)+1 <= k+1.

The accepted #218 `prune` lemma already permits signed pruning directions. It
requires only that the direction is supported on z and has a positive entry.
This gives a short proof that avoids a new cone-extremality or LP theorem.

Choose j with z_j>0. Let V be the coordinate space on support(z). Define

    T: V -> range(A) x R,    T(y)=(A(extension y), y_j).

Claim: T is injective. It is enough to consider T(y)=0. If y is nonzero, either
y or -y has a positive coordinate. Call that vector v. Its extension is in the
kernel of A, supported on z, and v_j=0. Apply the accepted minimum-ratio pruning
lemma to z and v. It supplies t>0 and z-t*v>=0 with strictly smaller support.
The new vector is in ker A, and its j coordinate is still z_j>0, so it is NOT
zero. This contradicts the support minimality of z. Hence y=0 and T is injective.

Finite-dimensional rank monotonicity now yields

    dim(V)=|support(z)| <= dim(range(A) x R)=rank(A)+1.

This proof also shows that the entire signed kernel on the chosen support is
one-dimensional, not merely that its nonnegative part is one ray. To derive
that statement directly, subtract a suitable multiple of z from an arbitrary
supported kernel vector to make its j coordinate zero and use the same argument.

The formal interface should consume #218's actual Circuit predicate or an exact
transport of it, not define a 'circuit' to include the desired support bound.
Keep the full support-minimality quantifier; minimality only among negative
certificates is insufficient without the already-proved conversion step.

After the rank cutoff, connect the exact rational enumerator to the normalized
unique ray on each qualifying support. This still does not discharge support
optimization over every original point x, discover useful candidate shapes,
or prove Polynomial Hirsch. Those are separate named obligations.
