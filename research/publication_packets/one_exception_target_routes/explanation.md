# One unrestricted target row, with an original m-d route bound

This extends accepted #323 rather than submitting its two-level theorem again.
The original body must be exactly both the finite real hull conv(C) and the m
original linear halfspaces in ambient dimension d. Endpoints are actual extreme
points. A supplied exceptional label set B has cardinality at most one; only
rows outside B that are tight at the target must have their boundary value and
at most one other value on all actual vertices. The exceptional row and all
non-target rows have no level bound. B may be empty or contain a non-target row.

The conclusion is an actual original-edge route with length at most the initial
missing target-label count, hence at most m-d. Every step preserves all acquired
target rows and acquires a new one. There is no supplied graph, improving neighbor,
active basis, rank, residual dimension, target uniqueness, or short-route witness.

## Geometric construction and the new last-row argument

Reuse the actual accepted #323 namespace proofs byte-for-byte, omitting only the
old public root and its final print commands. Those proofs establish active-kernel
triviality at a vertex, uniqueness from all target-tight rows, the active-label
count, complete locked-face geometry, and the improving-edge construction from
#322. The new helper improve_locked_row extracts the chosen-objective part of the
existing geometric construction without any level hypothesis. For any missing
target row, it returns an improving actual vertex joined by a whole original
extreme segment inside the face retaining all common target-tight rows.

If a missing target row lies outside B, its two possible vertex values force any
strict improvement to attain the boundary value. The resulting edge preserves
all acquired target rows and gains at least that one. Other target rows may be
gained incidentally; no exact-one-gain or shortestness statement is required.

If no such good row remains, target uniqueness provides a still-missing row q.
It lies in B. Cardinality at most one proves that every other target-tight row
is already attained. Take an actual improving vertex w from improve_locked_row;
all those other target rows remain tight at w. Suppose q has an intermediate
value A_q u < A_q w < b_q. Put

    t = (A_q w - A_q u) / (b_q - A_q u).

Then 0<t<1. The point (1-t)u+t v has the same value as w on every target-tight
row: on q by the displayed identity and on all other target rows by locking.
Their difference lies in the kernel of every target-active row. The already
proved extreme_kernel theorem forces equality, so w lies in the open segment
between feasible u and v, contradicting its extremality. Thus A_q w=b_q.
The acquired rows now determine the target uniquely. In particular the last
exceptional phase is one edge, independent of how many values q takes elsewhere.
This is a derived one-dimensional residual phenomenon, not an assumed cheap phase.

Strong induction on the missing-label cardinality now builds the whole route.
Missing labels are disjoint from all source-active labels, and at least d original
labels are active at the source. This gives initial missing labels <= m-d and
retains the original input parameter, with no expanded inventory factor.

## What this does and does not assert

Redundant/interior generators, redundant inequalities, nonsimple vertices,
lower-dimensional bodies, dimension zero, empty B, equal endpoints and exceptions
outside the target-active set remain allowed. m counts displayed original rows;
a separately formalized irredundant facet lattice is not part of this target.
Edges are nondegenerate whole IsExtreme segments in the original body. Local
exposure is used internally; a separate original-ambient IsExposed assertion is
not added. There is no claim of shortestness, all-facet nonrevisiting, efficient
vertex enumeration, or a polynomial-time implementation.

The exact finite-hull/H equality and the target-row condition outside at most one
exception are explicit structural premises. They are not proved for arbitrary
carriers. Consequently this is not Polynomial Hirsch. The next obstruction is
multiple independent unrestricted target rows, for which the remaining face need
not be a line. Their acquisition cost is not silently assumed bounded.

The geometric reasoning uses classical polyhedral face/rank and two-level routing
ideas. No historical-priority or best-known-bound claim is made. The project-level
advance is the formal extension of #323 to one completely unrestricted target row.

## Explicit family beyond the old two-level assumption (written application)

For every d>=1, write coordinates as x_0,...,x_(d-2),t and set

    0 <= x_i <= 1,
    0 <= t <= h(x),  h(x)=1+sum_(i=0..d-2) 2^(-(i+1))*x_i.

There are 2d original inequalities. h is strictly positive on the box. The body
is the convex hull of the bottom points (epsilon,0) and roof points
(epsilon,h(epsilon)), epsilon in {0,1}^{d-1}: express x as a convex combination of
box corners, apply the affine roof lift, and then interpolate vertically between
the bottom and roof points over x. Conversely those corners satisfy the rows.
Every such point is a vertex since its d selected active rows determine it
uniquely. A non-corner x or an interior vertical coordinate yields a nontrivial
convex decomposition, so there are no additional vertices.

Each box row takes only two values. At a bottom target the bottom row has one
value on all bottom vertices and 2^(d-1) distinct values on the roof vertices;
at a roof target the roof row has one value on the roof and 2^(d-1) distinct
values on the bottom. Distinctness follows by scaling binary subset sums by
2^(d-1); the resulting integer sums run from zero to 2^(d-1)-1. The boundary
value is disjoint from the other values. Thus exactly one target row may have
2^(d-1)+1 levels, while all other target rows have two.

At d>=2 these targets are outside #323's premise but within the new one-exception
premise. From roof all-ones to bottom all-zeros, flip each box coordinate on the
roof and then take the final vertical edge. Each is a genuine whole edge: the
other box coordinates and the roof equation, or all box coordinates for the
vertical segment, fix a one-dimensional face. This gives d explicit original
edges on 2d rows without enumerating the global level set. The family classification
and exponential count here are a written application, not separate Lean theorems
in this packet; the general one-exception route theorem is the public formal target.

## Executed exact supporting checks and honest boundaries

The new test script reuses the two unchanged prior geometric/target-row scripts.
Small reference hulls independently determine vertices, original rows, support
faces and edges. The producer does not read the reference edge table; it uses
#322's unchanged normalized-contrast constructor. The consumer checks original
edge membership, the full supporting slice, acquired-label preservation, strict
acquisition and both route bounds. Saved certificates also replay with edge
construction disabled.

All 22 small hull models pass: 142 actual vertices, 155 displayed rows, 116
qualifying targets (46 newly admitted relative to #323) and 26 rejected targets.
The 930 routes contain 1373 original-edge occurrences versus 1366 shortest-distance
total, with seven nonshortest outputs retained. Two hundred terminal steps use the
unrestricted exception. Models include redundant/interior generators, nonsimple
and lower-dimensional hulls, affine charts, sloping roofs and repeated rows.

Explicit d8/16/32/64 roof routes check 8/16/32/64 original edges and every original
inequality. Common-row right-inverse identities certify dimension d-1 along each
edge; endpoint row changes establish maximality. Exceptional level counts
129,32769,2147483649,9223372036854775809 are evaluations of the written formula,
not enumerations. Large full vertex graphs are not constructed. Seven malformed
controls are rejected, including a hexagon with two multilevel target rows.

The first dense large-certificate verification hit a 45-second process timeout;
no output from that attempt is counted as a completed aggregate. A sparse
implementation of the same exact matrix identities then completed the full large
stage. A clean three-script workspace reproduced both complete reports and both
full fixtures byte-for-byte. The Python programs and JSON parser are not Lean-
extracted or kernel-verified, and these computations are not compilation evidence.

## Formal verification boundary at preparation

Local Lean/Lake and cached dependencies were not found, and toolchain-host DNS
failed. Exact source/dependency/type checks and rational tests are not Lean
compilation. The complete standalone candidate is prepared for one normal pinned
compiler/axiom/publication gate. Five final transitive reports cover the new
chain and public solution. Preserve any actual failure instead of weakening this
target or running a speculative sequence of hosted proof edits. No pins, strict
0.10.7 guard, workflows, actor allowlist or verifier/publisher security split change.
