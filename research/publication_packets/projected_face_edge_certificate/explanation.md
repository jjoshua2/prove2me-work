# Actual image edges from original rows, without lifted adjacency

## Result and why this is not the previous projection check

Let P={z:a_i(z)<=b_i} be any finite real H-polyhedron and G a linear map.
Neither P nor its fibres is required to be bounded. The theorem takes two
FEASIBLE lifts x,y with Gx != Gy. It does not require x,y to be source vertices
or adjacent, and does not require a one-dimensional source face.

Finite original-row witnesses prove that the ENTIRE maximizing slice of GP
is [Gx,Gy], and conclude

    Gx != Gy AND IsExtreme R (GP) (segment R Gx Gy).

This is exactly the repository's ordinary-adjacency predicate, inlined with
Mathlib symbols for the public target. It is not a circuit step, a projected
chord, or a predicate renamed to include the desired conclusion. The theorem
also returns the exposing bound and exact supporting-slice equality.

The previous PR241 computational criterion required the preimage slice itself
to be an edge with common-row rank d-1. The present theorem instead certifies
that its IMAGE is one-dimensional. Its fibres can have any dimension, and be
unbounded. It neither imports nor depends on PR241's uncompiled bounded-image
representative proof, whose publication comment was independently blocked.

This is a finite-certificate formalization of classical linear/convex geometry,
not a historical novelty claim. Mathlib's actual extreme-set definition is
used, as in Solutions.PolynomialMinkowskiExposedEdges. The project contribution
is this full original-H certificate interface and its proof, rather than a
new classical statement that exposed faces are extreme.

## Certificate data

Select original rows J and strictly positive lambda_j, and give an image-space
functional f such that

    f o G = sum_(j in J) lambda_j a_j.

Both lifts satisfy every original inequality, and all selected rows are tight
at both. With beta=sum lambda_j b_j, this proves f<=beta on GP. Strict positivity
shows equality exactly when every selected row is tight: no undesignated row
is silently assumed to be an equality and no zero exposure weight is treated
as if it imposed a constraint.

Put v=Gy-Gx. Supply a source-space functional phi with phi(y)-phi(x)=1 and
image vectors w_j satisfying, on EVERY STANDARD BASIS COLUMN,

    G(e_i)=phi(e_i)*v+sum_(j in J) a_j(e_i)*w_j.

Linear extension is proved in the source, not assumed. Thus on the common
row face, subtracting the identity at x gives

    Gz=Gx+(phi(z)-phi(x))*v.

This is a finite certificate for the image-rank-one condition. Algebraically
it implies G(ker A_J) is contained in span(v); y-x is in ker A_J and maps to
nonzero v, so that image has exactly dimension one. Equivalently,
rank([A_J;G])-rank(A_J)=1. The checker verifies the displayed column identities,
not the output of a numerical rank oracle. The proof does not need to assume
that P is full-dimensional or that J has independent rows.

Finally supply nonnegative original-inequality weights u_lower,u_upper and
UNRESTRICTED selected-row weights gamma_lower,gamma_upper such that

    -phi=sum u_lower_i*a_i+sum gamma_lower_j*a_j,
     phi=sum u_upper_i*a_i+sum gamma_upper_j*a_j.

Their scalar right-hand sides are sharp at x and y respectively:

    -phi(x)=sum u_lower_i*b_i+sum gamma_lower_j*b_j,
     phi(y)=sum u_upper_i*b_i+sum gamma_upper_j*b_j.

These are finite coefficient/scalar identities. On the selected face they
prove phi(x)<=phi(z)<=phi(y). Equality-row coefficients are allowed to be
negative; imposing nonnegativity on them would needlessly reject valid edges.
They are not granted sign-free use on inequalities: only the selected TIGHT
rows receive unrestricted multipliers.

There is no supporting-face-equality oracle, existing source path, optimization
correctness assumption or unproved Farkas premise among these hypotheses.
Witness discovery and uniform route-length control remain separate.

## Entire-face proof

The exposing identity and strict positive multipliers identify all preimages
of the image maximum with the selected row face. The rank-one identity and
sharp endpoint bounds place every image point of that face in [Gx,Gy].

Conversely, every convex combination of x,y is feasible and remains tight on
J. Linearity sends it to the matching convex combination of Gx,Gy, and the
exposing identity is sharp there. This proves BOTH inclusions of the full
supporting-slice equality, including the endpoints. A separate elementary
proof makes a supporting maximum slice an actual Mathlib extreme subset.
Combined with Gx!=Gy, the conclusion is a genuine ordinary image edge.

Notice what is absent: no compact representative theorem, no bounded preimage,
no source-vertex correspondence, and no requirement that the straight segment
[x,y] itself be an ordinary edge. It can be a diagonal or contain points in
unbounded source fibres. Only the certified image segment matters.

## Exact producer and independent arithmetic auditor

scripts/projected_face_certificate.py has an exact rational producer and an
auditor. The producer uses elimination to discover row combinations, but the
auditor calls neither elimination, rank, LP nor convex-hull code. It recomputes
all original feasibility, tightness, coefficient, sign, normalization and
sharpness identities. Changing or dropping any needed certificate is rejected.
The auditor's coefficient form matches the theorem's linear-map equalities;
the Lean target inlines Mathlib symbols and has no custom preamble definitions.

Generic theorem verification does NOT automatically verify the Python JSON
parser or all numerical fixtures. Python is not Lean-extracted. Each concrete
instance needs its own kernel-checked finite data for a separate Lean instance
claim. No such per-fixture kernel evaluation is claimed here.

## Executed tests

The independent small reference enumerates source vertices and reconstructs
each complete planar image hull. All110 image edges in18 models pass the new
certificate, checked against223 original vertices,110 rank-gap computations
and1619 original-vertex support comparisons. Twenty image edges use NONADJACENT
source vertex lifts and have source face dimension greater than one. The
old lifted-edge hypothesis would exclude these specific lift certificates.
There are1765 finite column-identity checks in this small suite.

Eight larger examples use source dimensions8,32,64,128 with a hexagonal image,
and both bounded variable-height and unbounded fibres. They certify all six
image edges in each case. Their preimage faces have dimension d-1. An unknown
invertible rational affine coordinate change hides the product/projection
coordinates; the transformed certificates remain exact. Source graph and
vertex sets are NOT enumerated. These images are deliberately simple polygons,
not hard high-dimensional Hirsch instances.

A separate sequence test certifies 8-,16- and32-edge antipodal routes in image
cubes of dimensions8,16,32, represented in16,32,64 source coordinates with
unbounded fibres. Consecutive image endpoints coincide exactly across the
independently audited certificates, using the SAME source coordinate change.
The lifted points have large strictly positive fibre coordinates and are not
source vertices. The exposed preimage dimensions are9,17,33, not one. The
32-dimensional IMAGE has64 facets; the source description has96 rows. No image
or source graph is enumerated, and no source row count is misreported as the
image facet count. Cube routing is classical; these are applications checking
the interface, not a new diameter theorem for cubes or arbitrary carriers.

Twelve malformed cases fail, including a rank-two square diagonal, a proper
subsegment falsely offered as the entire edge, collapsed images, nonsharp or
negative witnesses, missing rows, false quotient identities and inexact data.
The suite also replaces all producer elimination/rank functions by raising
stubs and checks that the arithmetic auditor still works.

Reproduce:

    python3 scripts/test_projected_face_certificate.py

The source-hashed receipt is research/PROJECTED_FACE_EDGE_TESTS.json.
The fixture bundle preserves concrete original matrices and complete finite
certificates, not only aggregate claims.

## Research boundary and coordination

The verified general route-count problem is NOT solved by recognizing one
edge. A short sequence of these witnesses must still be constructed with a
polynomial bound measured in the ORIGINAL IMAGE facet count. This theorem
does not assert efficient discovery of all certificates, completeness of the
producer, or a uniform route bound. The existing compact-shadow counterexample
still rules out transporting arbitrary source graph paths to image edges.

PR244 owns fixed-core Minkowski fibre walks. This work neither copies that
pending packet nor modifies/triggers its workflow. Coordination is posted in
PR244 comment5666110074. PR241's blocked publication request was not retried
via another command or branch; none of its source is included in this proof.

The originating container lacks local Lean/Lake and public toolchain DNS.
Static/rational tests are not compilation. The actual final pinned gate and
transitive axiom audit must be recorded before upgrading this packet's status.
The 245-line standalone candidate has three final axiom printouts and no proof
admissions. Only an authenticated platform verdict establishes acceptance.
