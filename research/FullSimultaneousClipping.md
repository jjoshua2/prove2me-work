# Full simultaneous clipping: connected radial traces and new endpoints

Continuation of PR #50, 2026-09-09. Branch:
`chatgpt/simultaneous-clipping-complete`.

## Status and publication boundary

The source now includes a single end-to-end statement for the old-walk result
and a stronger full-diameter statement. Consult the PR's tested commit and
Actions verdict for compilation status. The strict workflow compiles the
public wrapper, audits every new declaration, independently compiles a
flattened standalone proof, and reproduces both exact regression suites.
The offline packet manifest identifies exactly the source commit and proof
hash checked by that run. A failed workflow is not a completed verification.

No Prove2Me API action is performed. The user handles publication. The proposed
public name is `Hirsch.simultaneous_clip_diameter_le_outer_add_final_faces`;
`Solutions/Sol_Hirsch_simultaneous_clip_diameter.lean` gives its public-facing
exact type using only Mathlib and the existing Hirsch model. There is no claim
of literature novelty and no claim to have solved Polynomial Hirsch.

## 1. Precise strongest result

Let Q be a compact convex subset of finite-dimensional Euclidean space, and set

    P = Q intersect intersection_i {f_i(x) <= b_i},
    F_i = P intersect {f_i(x) = b_i}.

Here i ranges over a finite family and f_i is a continuous linear functional.
Assume:

* There is o in Q with f_i(o) < b_i for every added cut.
* `DiamLE Q D` in the existing Hirsch edge/stay graph model.
* `DiamLE F_i B_i` for each FINAL cut face.

Then

    DiamLE P (D + sum_i B_i).

The final endpoints can be ANY vertices of P. They need not be vertices of Q;
indeed the theorem allows zero surviving outer vertices. No simplicity,
irredundancy, full-dimensionality, prescribed finite subdivision, geometric
portal, or polynomial diameter hypothesis is hidden in the statement. Q need
not even be polyhedral: the supplied graph-diameter hypothesis is explicit.
Empty final cut faces have vacuous diameter bounds and redundant cuts are allowed.

The conclusion uses padded edge/stay walks, exactly as `Hirsch.DiamLE` does.
There is no extra endpoint-attachment charge. Each final cut face is charged
once across BOTH attachments and the entire outer route.

A separate theorem, `HirschRadial.simultaneous_clip_route`, completes PR #50's
old surviving-endpoint result with budget `L + sum_i B_i`. It only requires Q
convex and P compact, so a supplied outer vertex/edge walk can also come from
an unbounded outer set. The full-diameter extension uses Q compact to obtain
maximizing outer vertices for the attachments; this is not silently available
for an arbitrary unbounded relaxation.

## 2. Why finite breakpoint extraction is no longer a formal gap

Use the same fixed final radial map as PR #50:

    s_i = b_i - f_i(o) > 0,
    lambda_i(x) = (f_i(x) - f_i(o))/s_i,
    mu(x) = max(1, lambda_i(x) over all i),
    rho(x) = o + mu(x)^(-1) * (x-o).

A recursively defined finite maximum makes the following facts direct:
mu is continuous, mu >= 1, a maximizing row is attained unless mu=1, rho is
continuous, rho(Q) is contained in P, and rho fixes P. If rho(x) is not x,
then rho(x) lies in at least one final cut face.

The union of the old walk's edge segments is a connected trace. Its radial
image is connected, even if one face is entered infinitely many times or the
trace has no chosen subdivision. Each point of that image lies in a final cut
face or a clipped old edge.

The finite closed-cover lemma says: if a connected trace lies in the union of
finitely many closed sets, the labels covering its endpoints are connected in
the actual set-intersection graph. Otherwise take the union of labels reachable
from one endpoint and the union of the remaining labels. Those two finite
closed unions cover the trace and separate its endpoints, contradicting
connectedness. This is an actual geometric cover, not chronological overlap.

For compact P, intersections of closed extreme faces contain a parent extreme
vertex whenever they contain any point. PR #50 supplies that fact. The existing
one-charge-per-region routing theorem then turns set-intersection connectivity
into an edge route with total cost at most the sum of available face budgets.
No continuous vertex-selection map is asserted or needed.

Finiteness and closedness are essential to this particular connected-cover
argument; they are explicit hypotheses, not consequences of a general open cover.

## 3. The clipped-old-edge cost is proved, not supplied as a hypothesis

If E is an extreme segment of Q, then E intersect P is a closed extreme subset
of P. An open segment in P meeting E has endpoints in E by extremeness in Q.
The intersection is convex and collinear.

Any convex collinear set has graph diameter at most one in the Hirsch model.
If it has distinct extreme points u,v, every other point lies between them:
collinear betweenness leaves two other possibilities, each contradicting the
extremeness of u or v. Hence the set equals the segment [u,v], and that segment
is an extreme set of itself. Empty and singleton cases are included.

This avoids separately classifying every clipped segment by two attained
coordinate extrema and also covers harmless degenerate supports.

The full-diameter assembly uses only genuine old edges, together with one
zero-cost initial singleton. Stay steps add no points; their edge labels may
be interpreted as empty supports. This keeps the zero-length outer-walk case
valid without an artificial extra unit in the final budget.

## 4. New endpoints attach using only the SAME final cut faces

The survival restriction from PR #50 can be removed in three steps.

### A. A new vertex is on an added cut

Suppose a vertex u of P strictly satisfies every added cut. If u lay in a
nontrivial open segment between y,z in Q, apply one sufficiently small common
homothety centred at u to both y,z. The finite strict cut slacks ensure both
shrunken endpoints lie in P; u remains strictly between them. This contradicts
extremeness in P. Therefore u was already an extreme point of Q.

The Lean proof obtains the common shrinking scale explicitly from the two
finite radial gauges centred at u. It does not import a polyhedral vertex
classification theorem or assume irredundancy.

### B. Move outward through an active cut

For a new vertex u, choose an added cut i with f_i(u)=b_i. Compactness of Q
supplies an outer extreme point a maximizing f_i, with f_i(a)>=b_i. Every point
x of the segment [u,a] satisfies f_i(x)>=b_i.

Apply rho to this attachment segment. If mu(x)>1, a maximizing cut is tight at
rho(x). If mu(x)=1, then rho(x)=x belongs to P and f_i(x)>=b_i, so equality
holds and x lies in F_i. Consequently the entire radial attachment lies in the
union of the FINAL cut faces. Its active label may change; no label-preserving
claim is needed.

If u is already an outer vertex, choose a=u and use the trivial attachment.
Repeat at the other final endpoint v, obtaining an outer vertex c.

### C. Join once, charge once

Take a length-D outer edge/stay walk from a to c using `DiamLE Q D`. Join the
raw attachment [u,a], the outer edge trace, and [c,v], then apply the same rho
to everything. The resulting trace is connected and contains u,v, since rho
fixes P.

Its support family consists of the final cut faces plus at most D clipped old
edges and a zero-cost initial singleton. Apply the finite closed-face routing
lemma once to that whole family. Charging each final cut face once yields
`D + sum_i B_i`, not `D + 3*sum_i B_i` and not a charge per crossing.

## 5. Exact regressions that distinguish the stronger result

`scripts/test_full_clipping_diameter.py` is a rational certificate constructor,
not only a comparison of two numerical diameters. It finds the attachment
vertices, constructs the entire piecewise-rational radial trace, checks each
affine cell at both ends, rounds shared feasible checkpoints consistently,
extracts a simple support-label path, and explicitly assembles a final graph
walk. Final face diameters are independently computed by exhaustive graph BFS.

The old hull/graph routines enumerate every candidate vertex basis exactly.
No floating-point LP result is trusted. The concrete hull computations are not
Lean hull formalizations; they independently test the construction and its
hypotheses.

New deterministic results:

* Inner cubes `[1/4,3/4]^d` inside `[0,1]^d`, d=2,3,4: ZERO outer vertices survive.
  All 154 unordered distinct final endpoint pairs are checked. All 308 endpoint
  occurrences are new. There are 1,160 certified affine cells, 768 nonvertex
  checkpoint occurrences, and 70 zero-length outer connecting walks.
* Thirty seeded general clipping instances in dimensions 2-4 check another
  356 endpoint pairs, including equal endpoints, old/new mixtures, duplicate
  cuts, strictly redundant zero rows, and the no-cut case. They contain 1,350
  affine cells, 641 nonvertex checkpoint occurrences, and 72 zero-length outer
  walks. Every explicitly constructed final route meets its budget.
* In total: 510 pairs, 2,510 cells, 1,409 nonvertex checkpoint occurrences.
* PR #50's existing exact regression is retained unchanged, including the
  4D/5D Dantzig incidence witnesses and the genuine facet-sweep obstruction.

The committed JSON must match a fresh run byte-for-byte. Seeded cases are
finite tests, not evidence sufficient by themselves for the general theorem.

## 6. What this changes for the main research program

For compact monotone relaxations, two previously explicit technical obstacles
are removed: constructing a finite fixed-parent checkpoint subdivision is no
longer needed, and deleting constraints is not disqualified merely because
both desired endpoints cease to be outer vertices. The radial construction
and endpoint attachments give the actual fixed-parent connected repair network.

The remaining substantive obligation is now quantitative and application-specific:
choose a useful outer Q, establish its inexpensive diameter, and bound the total
intrinsic diameter of the FINAL added-cut faces. An inexpensive description
or polynomial number of faces does not prove an inexpensive total face budget.

For example, enclosing a polytope in a cube with diameter d and charging every
original facet would give only `d + sum_i diam(F_i)`. Replacing each facet by
an uncontrolled lower-dimensional worst-case diameter can reproduce a bad
recurrence rather than a fixed polynomial. The existing common-face/effective-row
and ordered-tail results may help with specific families, but their hypotheses
must be proved. Lower-dimensional faces are not automatically balanced.

The theorem also does not turn a circuit segment into an edge. Its old trace
is built from actual outer edges, whose clipped supports have dimension at most
one. The known hexagon circuit obstruction still applies. Nor does the full
statement automatically extend to an unbounded Q, since the maximizing outer
vertex used in the attachment may not exist there.

The formal global frontier remains
`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`). No cyclic decomposition, new Open child,
or claim of closing that frontier is made here.

## Reproduction and offline handoff

    python3 scripts/test_face_preserving_checkpoints.py
    python3 scripts/test_full_clipping_diameter.py
    lake build Solutions.Sol_Hirsch_simultaneous_clip_diameter
    python3 scripts/bundle_simultaneous_clipping.py
    lake env lean clipping_offline_packet/solution.lean

The GitHub workflow adds the strict 34-declaration axiom audit and independent
standalone `solution` audit. The packet contains the exact public theorem type,
flattened proof, source hashes, complete local source chain, and pin files.
There are no private `Solutions.*` imports in its standalone proof and no
Prove2Me API calls in the workflow or bundler. Compilation success is recorded
by the actual workflow receipt, not inferred from this document.
