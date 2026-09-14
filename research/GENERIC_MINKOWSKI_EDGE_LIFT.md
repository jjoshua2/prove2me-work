# Generic exposed-edge bridges for finite Minkowski sums

## The geometric gap closed by the candidate

The accepted allocation machinery gives exact decompositions. That is not an ordinary-edge route. Active #239 derives additive affine-envelope counts but its formal certificate assumes each global supporting slice is a segment. This continuation proves the core-edge bridge EXISTS for finite-hull components: from one exposed core edge [u,v], it constructs a new objective and a nondegenerate exposed segment of the whole sum with core components u,v. It does not assume normal-fan genericity, edge-surjectivity, or a supporting-slice oracle for the sum.

This is the forward exposed-edge specialization of classical Deza--Pournin, *Diameter, decomposability, and Minkowski sums of polytopes*, arXiv:1806.07643v1, Lemma3.8, DOI10.4153/S0008439518000668. No historical novelty claim. The formal source is `publication_packets/generic_minkowski_edge_lift/solution.lean`; the exact public interface uses only Mathlib symbols.

## Finite quotient genericity, derived not assumed

Let e=v-u. Form D from all within-component ordered differences. In W=E/span(e), each nonparallel d has a nonzero class. The finite simultaneous-dual-separation lemma produces a functional on W nonzero on all such classes, and its pullback q annihilates e. This is valid in any real vector space, since the relevant finite data span a finite subspace; the Lean proof does not need a finite-dimensionality or topology instance.

Set epsilon to half the minimum of 1 and |f0(d)|/(|q(d)|+1) over the nonzero old comparisons. Then f=f0+epsilon*q preserves all old strict signs while tying precisely the listed parallel differences. Old core ties stay tied, because they lie on the core edge; old strict comparisons stay strict. Thus the core support slice remains exactly [u,v]. The initial normal may expose a higher-dimensional face of the full sum; that is precisely why simply reusing it would be wrong.

Choose tau with tau(e)=1. Within each factor's finite f-maximizers, take the minimum and maximum of tau. Tied differences are parallel, so every maximizing listed point lies on the interval between the chosen endpoints a_i,b_i, with b_i=a_i+eta_i*e and eta_i>=0. Convex-hull propagation yields the entire support segment, not just two tied points. In the distinguished core use exactly a_c=u,b_c=v,eta_c=1.

The support value of a sum is the sum of support values. Equality forces each summand into its own support segment. Parallel intervals add by adding their lengths, so the whole support slice is [sum a_i,sum b_i]. Its length parameter is at least1. Thus its endpoints are distinct and it is an extreme subset of the sum: an actual ordinary edge in the repository's adjacency definition.

The support-slice and interval arithmetic reuses/adapts the already integrated PolynomialMinkowskiExposedEdges proofs. This packet's distinct content is the existence of the objective and all required component intervals. The public theorem requires the exposed core-edge certificate, not a pre-existing sum-edge certificate. It is not a proof that every abstract edge is exposed independently of that input.

## Deterministic rational producer

For rational e choose a nonzero pivot e_p. An annihilator basis is h_j(d)=d_j-e_j*d_p/e_p for j!=p. Put q_t=sum_j t^j h_j. Each nonparallel difference produces a nonzero polynomial. The union of roots contains at most the sum of their degrees many real numbers, so testing the first degree_sum+1 nonnegative integers finds a valid objective direction. No random retry budget is needed. A rational epsilon as above then preserves all strict signs. This root-count argument is mathematical justification for the program's finite grid, not an extra Lean-verified imperative implementation theorem.

The independent verifier never reruns the generic search. It checks all original component points, core exposure, all finite comparisons, entire support segments, nonnegative parallel lengths, global endpoints and nondegeneracy. For small cases it separately enumerates ALL point-sum tuples and checks the global support slice. Full product enumeration is only an independent small-case audit, not part of construction.

Run `python3 scripts/check_generic_minkowski_edge_lift.py --out /tmp/check.json --fixture /tmp/grid.json`, then `python3 scripts/check_generic_minkowski_edge_lift.py --verify /tmp/grid.json`. Exact receipt: GENERIC_EDGE_LIFT_CHECK.json. Source SHA-256:33d8412978c880ff00a1427e3267660ad6551e9670e2fda10c3140d5df29347b. The tests cover96 bridge instances:92 small,1 root-grid stress,3 large. There are7366 exhaustive point-sum tuples, not claimed distinct vertices. The stress fixture rejects parameters0 through7 and succeeds at8. Dimensions16/32/48 use no product enumeration, with respectively8/24/40 extra factors. Their possible point-sum counts111537,9320174703873,595725607493789511249 are products of supplied list sizes, not vertex counts. Twelve invalid controls reject diagonals, incomplete/wrong faces, bad normals, missing summands, inexact data and endpoint errors.

## How this advances the diameter route, and what remains

The desired route-lifting strategy uses a core path plus connectors within the fibres over its visited vertices. This proof supplies one real bridge for each EXPOSED core edge, including parallel simultaneous factor changes. #239 supplies a finite affine-envelope counting interface for the fibre portions. The next geometric existence task is a generic objective segment staying inside a core vertex's strict normal region, preserving both requested sum endpoints, and crossing only one-dimensional full support faces. Then instantiate the actual route assembler and count repeated core visits honestly.

Even a completed route lift only gives a useful bound when the ACTUAL carrier has a controlled core/factor decomposition. A supplied finite point presentation is not discovery of that equality from arbitrary original-H inequalities. Accepted #236 can certify a proposed decomposition, but uniform useful-shape selection and routes on nondecomposable/unrecognized high-dimensional carriers remain unsolved here. No unconditional polynomial Hirsch diameter estimate is claimed.

## Execution provenance

Prepared proof head80f533255175a6dc24c3132feaa01b10ec275180, PR240, branchproof/generic-minkowski-edge-lift. Its three original packet blob hashes match local bytes. Actual first command5657668062, bot ack5657669319, run34795161919. The bot resolved the exact proof SHA above, which differs from its trusted workflow-main SHA. The local compile did not start because lake is absent; toolchain-host DNS also failed. Source/Python checks are not Lean verification. Consult the separate handoff/receipts for the last observed gate outcome; this note does not assert ACCEPTED. The original packet is frozen through the gate.

No #239/#238/#208/#210 branch or trigger changed. No accepted theorem was resubmitted. No pin, permission, workflow, allowlist, credential or secret separation changed. The old unsubmitted internal-slack-normal-form candidate is not a dependency and has not been submitted by this continuation.
