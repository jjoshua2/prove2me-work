# Positive circuits: signed kernel and sharp rank cutoff

## Exact result

Let A:R^n -> R^k be real linear and x>=0 be a nonzero vector with Ax=0.
Write S=supp(x). Minimality of S among nonzero nonnegative null vectors is
EQUIVALENT to every signed vector z supported on S with Az=0 being a scalar
multiple of x. Under either equivalent condition,

    |S| <= dim(range(A))+1.

Minimality here is the same original hypothesis constructed by accepted #218:
any nonzero nonnegative null vector supported on S must have all of S as support.
It is not replaced by signed-kernel uniqueness as an unproved assumption.

## Proof of the previously missing signed-kernel direction

For any signed null vector z supported on S, choose j in S minimizing z_i/x_i
and set t=z_j/x_j and q=z-t*x. Since x_i>0 on S, q is nonnegative; outside S,
both x and z vanish. Also Aq=0, supp(q) is contained in S, and q_j=0.
If q were nonzero, positive-support minimality would force q_j to be nonzero.
Thus q=0 and z=t*x. Conversely, if every such z is a multiple of x, every
nonzero supported null vector has the same support as x: its scalar is nonzero.
This gives the equivalence, not only one implication.

## Proof of the sharp global rank bound

Choose j with x_j nonzero. Extend a coefficient vector v on S by zero outside S.
The map

    v |-> (A(extend(v)), extend(v)_j)

is linear from R^S into range(A) x R. It is injective: a kernel element extends
to a supported null vector, hence equals t*x by the preceding result. Its j-th
coordinate vanishes, so t=0. Comparing finite dimensions gives the bound.
The Lean source constructs this injection and proves its injectivity; it does
not simply postulate rank-nullity or a sparse-certificate theorem.

The bound is sharp: the k+1 columns e_1,...,e_k,-sum(e_i) have positive null
vector (1,...,1), a one-dimensional kernel, and rank k. A zero column gives a
singleton positive circuit, also covered when k=0. An empty coordinate type
has no nonzero x, so the theorem is vacuous there. Redundant constraints and
rank-deficient matrices require no case exclusion.

## Connection to accepted work and exact remaining boundary

Accepted #218 (theorem 8f3c4cc7-be73-4ecf-9e17-816c710e20d7) already constructs a
fixed family of minimal positive supports detecting all nonnegative-kernel
linear tests. This new theorem applies directly to EVERY nonzero member of
that family, with exactly its existing minimality premise. It supplies both
the rank-plus-one cutoff and the signed nullspace criterion underlying the
finite enumerator. No old packet is resubmitted or modified.

For the allocation matrix in #219, put A=C^T. Its rank is at most the allocation
dimension K, so supports of size at most K+1 suffice. This is a mathematical
composition with #218/#219; this packet's public statement is the independent
signed-kernel equivalence and rank bound, NOT a claim that the source code of
the Python enumerator, the full joint allocation adapter, or a quantitative
catalogue-size theorem has also been formalized here. Enumerating subsets up
to rank+1 is polynomial only when that rank is fixed. Ordinary-edge routing
of arbitrary residual carriers and Polynomial Hirsch remain separate.

The result is classical linear algebra. The contribution is this exact formal
interface and its proof, not a claim of a newly discovered classical theorem.

## Verification provenance

The source is self-contained apart from Mathlib at the unchanged committed
Lean 4.30.0 / c5ea00351c28e24afc9f0f84379aa41082b1188f pin. The public target uses
only Mathlib symbols and the problem preamble contains imports/opens only.
All three declarations have explicit transitive-axiom printouts.

The originating container has no Lean/Lake binary. A direct toolchain-download
attempt failed on DNS resolution, so no local Lean compilation is claimed.
Source inspection and any independent rational checks are not Lean verification.
The requested isolated PR comment gate must compile and audit this exact source
before any publication. Its observed state belongs in the receipt/handoff;
this explanation is not an ACCEPTED verdict. A Lean failure must be repaired
locally before another hosted attempt, not by speculative Actions iterations.
