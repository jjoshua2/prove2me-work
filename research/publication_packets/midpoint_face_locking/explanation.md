# Adaptive common-image-face locking

## Exact formal result

For a finite original H-system P={z:a_i(z)<=b_i}, a linear map G, and two feasible image points u,v, take a source anchor x above their midpoint. The anchor is tight exactly on J. For each i in J, nonnegative original-row coefficients and an image functional certify the zero maximum slack of row i in the fibre Gz=Gx.

The theorem constructs a linear image functional whose entire exposed slice is H=G(P intersect {a_J=b_J}). It proves that H is convex and extreme, contains both u,v, and is contained in EVERY convex extreme subset of the original image containing u,v. Thus it is the actual least common convex face, not a proposed source face or an assumed minimality oracle.

Every nondegenerate segment extreme in H is then extreme in the ORIGINAL image and is contained in every common target face. The restricted-face edge certificate is an explicit input to this last implication. In the implementation it is supplied by the accepted #248 normalized-tangent interface, applied to the restricted original rows. Original-image adjacency is not assumed in its place.

## Reuse rather than a repeated proof

The first 288 lines are the accepted #247 standalone proof, with ONLY its root declaration and corresponding axiom-print name changed to Hirsch.ProjectedFaceDiscovery.certified_minimal_face. Its accepted source blob is 5c2935e1f2bd6831cfc9c9df119038e71df74666 and its SHA-256 is f06d51585f7741405e8adffdd2012c8844c224110672df9c5d70e4648f39804a. This result is NOT submitted again under a new name. The new public target composes it with the midpoint/minimal-convex-face and original-edge preservation interfaces.

That accepted theorem constructs the exposer from the actual dual identities. Complementarity removes off-face coefficients; their sum gives a positive combination of precisely the selected rows. Its feasible backward perturbation proves minimality at Gx even with source lineality. The source anchor, fibre duals and selected rows remain finite witness inputs; no claim that the LP producer/parser has been Lean-extracted is made.

## Proof of the new interface

1. The selected equality face of the original H-system is convex. An explicit two-point convex combination preserves every inequality and selected equality. Applying G proves convexity of its image H without source boundedness.
2. The midpoint (u+v)/2 belongs to the open segment joining u,v, with both coefficients exactly one half. Since H is extreme in G(P), both endpoints belong to H. This remains valid when u=v.
3. If D is any CONVEX extreme subset containing u,v, it contains their midpoint. The accepted minimality-at-midpoint theorem therefore gives H subset D. Convexity is essential: Mathlib IsExtreme alone need not describe a convex face, for example a union of unrelated extreme vertices.
4. If [u,w] is extreme in H, transitivity of IsExtreme makes it extreme in G(P). Its subset relation to H and H subset D preserve every common convex target face. Nondegeneracy u!=w is retained in the public interface, so a stationary segment is not used as an ordinary edge.

These are classical face properties. The contribution is their finite original-row/image binding and their integration into the selector, not a historical novelty claim for transitivity or midpoint minimality.

## How the algorithm uses it

At EVERY current image vertex u, use the unchanged #247 zero-slack fibre construction at the midpoint of u and the fixed target v. It supplies the strict anchor, all forced original rows and their complete dual certificates. Restrict the source by adding the reverse inequalities for those rows. The original image of this restriction is exactly the least common image face H(u,v), not the potentially nonextreme image of an arbitrary source face.

Run #248's unchanged select_step/verify_step on this restriction. Keep the SAME original target objective and target lift throughout the route. It still strictly exposes v on each subset. The full image-ray endpoint LP varies all source lifts, and the lexicographic image-slice refinement is preserved. The new theorem transfers the restricted edge to the original image.

After moving to w, H(w,v) lies in H(u,v). Therefore every target face acquired along the way remains locked. The code checks a nested sequence of forced original-row sets in addition to each complete face certificate. This uses no image facet enumeration, no source vertex or edge premise, and no supplied neighbor list.

The standalone arithmetic auditor rechecks all original-row dual identities, all exact active/slack conditions, the fixed target certificate, the old restricted edge certificates and path continuity. It still works when every LP, rank/elimination and discovery entry point is disabled. It is not a formally verified JSON parser.

## What changes about the progress question

For a combinatorial cube, its least common face fixes every coordinate bit already equal to the target. Any edge remaining in that face flips one of the differing bits, so the Hamming distance falls by one. Adaptive locking therefore produces a shortest path in every combinatorial cube, regardless of which allowed edge it selects. This is a classical combinatorial consequence; the general Lean packet above does not separately formalize a cube face-lattice classification.

The deterministic #248 backend is tested on the usual Klee--Minty original inequalities, from (0,...,0,1) to (1,...,1,0) in lower/upper facet bits. Its measured unmodified lengths in dimensions3,4,6,8,10 are5,8,18,32,50. Adaptive locking returns3,4,6,8,10 respectively; dimension12 returns12 with the independent Hamming lower bound. No asymptotic formula for the default backend is inferred from those measurements.

A concurrent #249 proved an exponential canonical normalized-height path on a capped Klee--Minty family whose INITIAL minimal common face is full-dimensional. Its theorem and source remain unchanged and are cited rather than duplicated. Adaptive recomputation is different from restricting only the initial face. The accompanying new capped-family test compares these policies with the same target objective and validates the entire returned paths with the unchanged #248 auditor. Its exact counts, and the separate actual-default-backend counts, are recorded outside this frozen proof packet.

## Limits that are not hidden by face locking

At most the image dimension many STRICT face inclusions can occur. That is NOT a bound on the number of steps: many successive vertices can retain the same common face. The polygons conv{(i,i^2):0<=i<=q} supply an explicit phase control. From (1,1) toward (q,q^2) with a horizontal increasing objective, the only improving path follows q-1 lower-chain edges, even though the undirected distance is two. The common face remains the full polygon until the last edge. This rules out charging every step to a dimension decrease, not polynomial bounds depending on the actual facet count q+1.

There is also no dimension/facet-only positive fraction of objective gap closed by each old step. On the SAME unit square, scale its four rows to -eps^2*x<=0, -y<=0, eps*x<=eps, y<=1. The default target objective is (eps,1), the initial height is (eps^2,1), and the chosen first edge is horizontal. It closes exactly eps/(1+eps) of the objective gap. This tends to zero while the graph and four genuine facets remain unchanged. Both old and locked algorithms nevertheless finish in two steps, so this is not a route-length lower bound.

Neither example disproves Polynomial Hirsch. No universal polynomial constant-face phase bound, useful decomposition for arbitrary carriers, shortestness outside the identified classes, polynomial simplex pivot bound, or uniform bit-complexity claim is made. The core-walk concatenation remains #244's separately owned task.

## Verification boundary

The prepared standalone source has400 lines and ten explicit axiom prints. Its public type is extracted exactly into problem.json, with a Mathlib-only preamble and the fixed Lean4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f environment. There are no new axioms or proof admissions. An actual pinned compile/axiom/publication gate must establish those claims before acceptance is recorded.

This runtime has no Lean/Lake executable, and direct toolchain DNS failed. Exact rational tests and source inspection are NOT Lean compilation. The prepared source and all raw/derived verification records must remain distinct. Existing accepted packets, workflows, pins, permissions and secret isolation are unchanged.
