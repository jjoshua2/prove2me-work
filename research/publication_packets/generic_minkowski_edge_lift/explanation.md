# Derive an exposed core-edge bridge, rather than assume its certificate

## Mathematical contribution and relation to existing work

For finitely many nonempty finite point sets, this theorem starts from an explicitly exposed edge in one core hull and constructs an exposed edge in their Minkowski sum with exactly those core endpoint components. It constructs the new objective, all finite-factor maximizing endpoints, their nonnegative parallel lengths, and the entire supporting slice. No normal-fan genericity, edge-surjectivity, supporting-slice equality of the sum, or diameter theorem is supplied as a premise.

The edge-surjectivity fact is classical: Deza--Pournin, arXiv:1806.07643v1, Lemma3.8 (DOI10.4153/S0008439518000668). This packet formalizes the forward exposed-core-edge case with explicit simultaneous component data. It does not claim historical novelty. The active #239 packet handles the different affine-envelope counting step while its section3 leaves core-edge bridge existence as written mathematics. This proof closes that specific geometric existence gap. #239, #238, pending #208 and retired #210 are not modified or triggered.

## Proof

Put e=v-u and take the finite set D of all within-component ordered point differences. Pass to E/span(e). Every member of D not parallel to e has a nonzero quotient image. Mathlib's finite simultaneous-dual-separation theorem produces a quotient functional nonzero on every such image. Pull it back to q, which annihilates e. This use does not assume a generic normal exists on the desired face; it derives it from the actual finite differences. The pinned source is Mathlib/Algebra/Module/Submodule/Union.lean, Module.exists_dual_forall_apply_ne_zero.

Choose epsilon as half the minimum of one and the positive ratios |f0(d)|/(|q(d)|+1) over original nonzero comparisons. Then f=f0+epsilon*q annihilates e, preserves all originally strict signs, and vanishes on a listed difference exactly when it lies in span(e). In particular all strict core comparisons remain strict, so the original core face stays exactly [u,v]. This includes the case where f0 exposes a higher-dimensional face in the whole sum: no use is made of such a face being an edge.

Choose a linear coordinate tau with tau(e)=1. For each other factor select a maximizer of f, then minimize and maximize tau over the whole finite set of f-maximizers. All those points differ along e, so the extrema a_i,b_i satisfy b_i=a_i+eta_i*e with eta_i>=0, and every maximizing point lies on their segment. Convex-hull support propagation proves the ENTIRE maximizing slice is this segment, including redundant/collinear listed points and point factors. The core endpoints are retained as u,v with eta_c=1.

Equality of a total support bound forces equality in every summand. The supporting slice of the sum is therefore the sum of the parallel intervals, exactly the interval between the sums of the endpoints. Since sum eta_i>=eta_c=1 and e is nonzero, that interval is nondegenerate. The existing finite-support extreme-slice argument then proves actual IsExtreme adjacency. The support/hull/parallel-interval helper proofs are adapted from the already integrated PolynomialMinkowskiExposedEdges module; the new content is generic existence and the endpoint construction, not a duplicate certificate assembler.

## Scope

No finite-dimensionality, topology, full-dimensionality, simplicity, independence, boundedness oracle, rank oracle or vertex-graph oracle is assumed. The finite hulls themselves provide polytopal data. The core index implies at least one factor; each factor is nonempty and the core endpoints are distinct. The formal inputs are Finsets, so duplicate literal entries identify the same point; the rational verifier nevertheless checks every listed input point and never drops an unchecked point. Empty factors are not allowed.

An explicitly exposed core edge is required. The theorem does not formalize the independent fact that every abstract edge of a finite polytope is exposed, nor the generic path through a fibre needed for the full #239 diameter statement. It does not provide a small factor presentation for arbitrary carriers. Endpoints have the declared core components; no separately formalized unique-decomposition map is assumed. Ordinary adjacency here is the project's definition: distinct endpoints and an extreme segment.

## Rational construction and checks

The standard-library producer uses an annihilator basis and a moment-curve integer grid. Each nonparallel difference gives a nonzero univariate comparison polynomial. Trying integers from zero through the sum of their degrees must find one outside all roots; a rational perturbation then preserves strict core comparisons. The checker independently verifies all component points, full support segments, original core conditions, global endpoints and nondegeneracy; it does not rerun generic search. This deterministic producer's universal program correctness is not a Lean-extraction claim.

Reproduction: python3 scripts/check_generic_minkowski_edge_lift.py --out /tmp/edge-lift.json --fixture /tmp/edge-lift-grid.json; then use --verify /tmp/edge-lift-grid.json. Executed exact tests cover96 bridge instances, with7366 full point-sum tuples checked independently in small/stress cases. The root-grid fixture rejects all eight initial integer parameters and succeeds at8. Three large cases in dimensions16,32,48 avoid product-state enumeration; their possible point-sum tuple counts are111537,9320174703873,595725607493789511249, not asserted distinct vertex counts. Twelve invalid controls are rejected, including an unchanged objective exposing a two-dimensional face and a diagonal misrepresented as a core edge. These numerical tests are not Lean verification.

## Verification provenance

The 443-line self-contained proof has a top-level theorem solution matching problem.json exactly and four transitive-axiom printouts. It preserves Lean4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f. The originating runtime has no Lean/Lake; a narrow compile attempt could not start and toolchain-host DNS failed. Static/type-text/hash checks and exact rational tests are NOT Lean compilation. This is one prepared final PR-comment gate. A failed Lean gate must be preserved as a failure, not followed by speculative hosted edits. Actual compilation, audit, authenticated ACCEPTED and live Proved states belong in the later receipts, not in this explanation.
