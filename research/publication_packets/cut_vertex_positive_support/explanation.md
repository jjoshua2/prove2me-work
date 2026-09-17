# Constructed positive supports at actual cut vertices

## Exact statement and improvement over #290

Let S be any set of points in R^d and let Q be convexHull(S) intersected with
finitely many specified linear halfspaces C_j(y)<=b_j. For EVERY actual extreme
point x of Q, the theorem selects a finite family v_i IN S and positive weights
w_i with total one and barycentre x. Neither the family, its independence, the
weights nor an active-cut rank certificate is provided by the caller.

The homogenized support vectors (1,v_i) are linearly independent. If A is the
ACTUAL set of cuts tight at x, the vectors (1,(C_j(v_i))_{j in A}) are also
linearly independent. The selected support consequently satisfies BOTH

    n <= d+1,                 n <= |A|+1.

Finally, on this selected support, total mass one and the active equations
sum_i u_i C_j(v_i)=b_j uniquely determine the weights: any REAL u satisfying
those equations equals w. The competing weights need not be nonnegative.
This is uniqueness on the selected support, NOT a claim that the support set
itself is unique, canonical, or cheap to discover.

The preceding accepted #290 theorem required an already supplied positive
support and derived active-image injectivity conditionally. This theorem
constructs the support first and then composes with that actual proof. It is
not a resubmission of the old theorem under another name.

## Proof and precise dependency reuse

Pinned Mathlib's eq_pos_convex_span_of_mem_convexHull supplies a finite positive
affinely independent representation of x in S. Its proof is the standard
Caratheodory finite-support reduction. The new code explicitly reindexes that
finite type to Fin n, preserving both the scalar weight sum and the vector
barycentre by an exact sum-bijection proof.

Affine independence is converted to linear independence of (1,v_i) using the
zero-total weighted-vector-subtraction criterion. The selected points belong
to convexHull(S). Apply #290's active_image_independent to this convex set and
the original extreme-point hypothesis, with the barycentre identified as x.
Its finite-margin perturbation proof handles every inactive cut correctly.
No independent-cut, simple-polytope, positive-dimension, or compactness premise
is added. The active subtype in the conclusion uses x itself, not a supplied
list of allegedly active inequalities.

The ambient homogenized space has dimension d+1 and the active-image space
has dimension |A|+1, giving the two cardinal bounds. For uniqueness, subtract
a competing weight vector from w. The resulting homogenized image sum is zero:
its first coordinate is the mass difference, and all others are active cut
value differences. Linear independence forces every weight difference to vanish.

The complete 8,163-byte namespace prefix of the accepted #290 source is copied
BYTE-FOR-BYTE, including its finite-margin and sum-projection proofs. Only the
old public theorem solution and its print suffix are excluded. Its accepted
source blob is 56e38bebb4d5b3501ee47c05df59631d5c5c0543; full source SHA256 is
3dd3f72bd43461fc68baadd0e12b0dad7526c0cedeece628ca9cdf256b1dd499. The accepted
platform theorem is c3781e27-7eb2-4ffc-bb5b-e85ffe60c480, submission
68ad9f06-cdc9-4a25-85fc-b62c5e9b711d. Those proofs are actual dependencies,
not assumed statements, and that public theorem is NOT registered again.

## Scope and relevance to Polynomial Hirsch

This is the support-selection and active-value-recovery interface needed by
the #277 cut-image alphabet argument. With S the generating base vertices,
the theorem gives an independent positive base-vertex support, without the
caller supplying one. The support points belong to the BASE and need not
individually obey the new cuts; requiring that would incorrectly trivialize
the geometric application.

S may be infinite, noncompact, or contain redundant interior points. The
hypothesis concerns convexHull(S), not its closure. The zero-dimensional case
and an empty active set are included. An empty generating set simply has no
extreme point satisfying the premise. Positivity and nonempty support follow
from the selected representation, not extra user assumptions.

The next distinct step is extracting a minimal set of active rows and using
its small affine system in a finite coordinate catalogue. This packet does
not do that extraction, enumerate all supports, prove a uniformly polynomial
catalogue for arbitrary carriers, or construct an ordinary-edge route. A
finite support theorem is not by itself a Polynomial Hirsch proof. Classical
Caratheodory/convex geometry is credited; no historical novelty is claimed.

## Prepared gate and separate supporting tests

The source is 322 lines, imports Mathlib only, and retains Lean v4.30.0 /
Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f. The public target is extracted
exactly from theorem solution; the preamble has imports/open/options only.
Four transitive axiom printouts cover the accepted dependency and new proof.
No proof admission or target self-import appears in the submitted source.

This runtime has no local Lean/Lake executable and DNS resolution of GitHub
and the Lean release host fails. No local compilation or axiom success is
claimed. The user requests the existing comment-triggered final verification
and publication attempt. Only the actual resolved-head compiler and trusted
publisher result can establish verification or acceptance. No workflow, pin,
permission, credential, or secret-split change is part of this packet.

The exact standalone supporting test reconstructs six original-H models from
178 square systems and obtains 34 cut vertices. It SELECTS 68 positive
independent supports (including 34 cases with redundant generators), and
recovers their weights uniquely from active values. Forty-three chosen support
points are outside the cut set, an important valid case. Six simplex cases
in dimensions 0,1,2,3,8,16 attain the sharp size bound; seven malformed or
out-of-scope controls are rejected. Redundant active cuts and inactive gaps
through 2^-240 are tested. These are Python/SymPy checks, not a kernel-verified
runtime algorithm or parser, and not a substitute for the Lean gate.

Coordination is recorded on #290 in comment5712364514. The separately owned
#289 moment catalogue and other open branches are left unchanged. No earlier
accepted or pending packet is retriggered by this publication request.
