# Cut-stable direction routing handoff

Base main: dbfd755ef4b6b2eb272c0cb70f888bf78741b5ec, after #269.
Coordination on #269: comments5690701164 and5690765655.
No #270 private-marker, #268 BMC, pending publication or accepted source is
modified. This contribution is research/code, not Lean/Prove2Me acceptance.

## Exact proved interface

Given a genuine N-line edge-direction cover of a compact base, an edge after
k distinct nonzero cut-normal lines lies inside a base face spanned by at most k+1
old directions. Enumerate r base directions and r-1 cut kernels. The one-line
intersections cover every new direction, including nongeneric/nonsimple cuts.
Candidate bound: sum_r binom(N,r)binom(k,r-1)<=binom(N+k,k+1).

If no q+1 added boundary rows can meet anywhere in the FINAL polytope, truncate
at r<=q+1. This is independently certified with every required strict original-
row dual inequality; q is not trusted as an annotation. For q1, many arbitrary
cuts have bound N+k*binom(N,2). The 16D/30-cut example has3616 candidates versus
511738760544 without overlap. Its45-edge returned path is WORSE than an explicit
31-edge comparison; do not sell the inventory reduction as shortest routing.

The new objective-line path uses whole supporting duals and original tight-row
right inverses. It preserves the actual minimal common face, including nonsimple
and lower-dimensional cases. Generic objective construction is finite and its
actual try cap can fail; no partial route is reported complete. The final audit
uses no LP but DOES replay catalogue elimination, endpoint independence and any
supplied affine chart. Do not claim all Gaussian elimination is disabled.

The classical direction-cover diameter theorem is credited to Blanchard--De
Loera--Louveaux/Gritzmann--Sturmfels. The project contribution is the cut/overlap
closure interface and original-H constructor. Historical novelty is not asserted.

## Trusted base evidence, not arbitrary-direction inference

The code recognizes boxes and positive connected-building-set simplex sums,
reusing #269's canonical H proof/interface. An optional explicit affine chart
is checked. Arbitrary asserted direction covers are rejected. New cut edges
can leave the base coordinate-root cover; every actual edge is checked again.
Final H rows may be redundant. Genuine facet numbers are proved only where a
family argument or complete small reference establishes them. General polynomial
facet-count conclusions require the full-dimensional final case and pruning
redundant added cuts, not unqualified use of the ambient presentation count.

An arbitrary polytope inside a loose box needs at least d added facets active
at each vertex, so q is not magically fixed in that representation. Initial N
can also be exponential. No universal polynomial route claim follows.

## Local replay

    python3 -m py_compile scripts/cut_direction_routes.py scripts/test_cut_direction_routes.py
    python3 scripts/test_cut_direction_routes.py

Stages: small,large,overlap,affine,negative,assemble. Use all stages before
assemble, which rejects mismatched source hashes. --certificate on the main
CLI expects the NESTED certificate object, not the full result wrapper.

THREE unchanged dependency files are bundled:
exact_farkas_lp.py (ea511a79164d953792942d8be3dd3537646738d6),
endpoint_transfer_routes.py (27ec8b5b5b24b862bc38d7f3494960a4c75081d9), and
simple_tangent_policy_audit.py (73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976).
Those files are bundled for standalone replay but are not new additions.
The LP is capped exact Bland simplex, NOT a polynomial pivot-time guarantee.

The small suite:173 routes/420 edges versus372 BFS/38 nonshortest;1076 complete
original square systems;86 vertices/137 edges;56 edges outside old direction
cover. Extra many-cut case:1001 bases/34 vertices/68 edges in4D. Large graphs
are not enumerated. The full proof lists every numerical and scope boundary.

No local Lean/Lake executable was available; network DNS for the toolchain
failed. There is deliberately no uncompiled proof skeleton, speculative Actions
run, changed publisher, or new Prove2Me submission. Exact Python/SymPy tests do
not kernel-verify the mathematical theorem or arbitrary JSON.
