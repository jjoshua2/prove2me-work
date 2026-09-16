# Parallel affine levels: accepted finite theorem and continuation boundary

## Current completed result

PR #279 on branch proof/parallel-affine-levels formalizes the finite counting step of research/AFFINE_LEVEL_BARRIER.md from merged #276. Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR heads/comments before choosing subsequent work. Accepted #275 and the protocol0.10.4 refresh had already merged before this turn; neither was resubmitted or modified. Reserved #210 and #270's blocked companion remain untouched.

Public theorem Hirsch.parallel_displacements_force_affine_coordinate_levels is ACCEPTED; theorem7ccd31e6-1b96-4c43-b1c4-f8c180eec7b8, submission0801e679-3429-4cee-9e83-57652530224b. The trusted publisher's authenticated receipt records live Proved. Frozen proof cf8a028018bf90f66f8f9ef8bce743207fa6f79b; run35141854142; new top-level trigger5703449938, acknowledgement5703451925, verdict5703493150. Read publication_packets/parallel_affine_levels/accepted-evidence.md and the unchanged raw receipt. Do not resubmit.

The113-line Mathlib-only proof passed its first compile/axiom gate and first platform submission, without repair. Driver/solution/statement exits0; the scalar helper and root theorem use only standard logical axioms. Three archive hashes and five frozen file hashes were recomputed. Final run and all required jobs completed successfully. Local Lean/Lake was absent; exact tests are not compilation evidence. The current pin remains Lean4.30.0/Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.

## Exact theorem, not an assumed counting certificate

Let V be finite, p_i,q_i in V, q_i-p_i=lambda_i*g, with g nonzero and positive pairwise-distinct lambda_i. For EVERY injective real linear map T into R^r and arbitrary translation, construct a coordinate j where T(g) is nonzero. Let K be its ACTUAL finite image cardinality on V. The result proves 2*card(I)<=K*(K-1).

The scalar helper injects the forward endpoint pairs and their reverses into the off-diagonal of the level set. Both maps are injective. A forward/reverse collision forces (lambda_i+lambda_j)c=0 and is impossible. This proves the factor2 without assuming sorted endpoints or a positive coordinate slope. Injectivity of T produces a detecting coordinate; that coordinate is not an extra hypothesis. Empty index families and arbitrary ambient real vector spaces remain included.

The finite point set need not be a polytope vertex set and no edge adjacency is assumed or concluded. The written Klee--Minty construction from #276 gives the intended family application: N=2^(d-1) implies K(K-1)>=2^d for some coordinate of every injective affine embedding. That family construction, original-edge classification and all-dimensional recurrence remain separate written/computational facts, not extra conclusions of this public Lean type. An exponentially large coordinate inventory is not a graph-diameter lower bound.

## Supporting tests and reproducibility

scripts/test_parallel_affine_levels.py checks88 injective embeddings/196 detecting coordinates. Eighty sharp cases use finite powers-of-two levels (including empty and singleton cases), positive and negative coordinate slopes, translated rectangular embeddings and constant extra coordinates. Eight Klee--Minty cases use dimensions1..8 with exact dense charts. Five countermodels explain the need for positivity, distinctness, nonzero g, injectivity and endpoint membership in this general statement.

The exact raw report is research/verification/parallel-affine-levels/exact-tests.json; SHA2561037e9ee0d55eb794b5e77a9bc73bcadf6b601f30230ed11c03411d4446948d8. A fresh one-script workspace reproduces it byte-for-byte. The test imports SymPy only to check concrete matrix rank. This is not a kernel-certified instance parser or an additional platform proof.

    python3 scripts/test_parallel_affine_levels.py

## Remaining mathematical obligation and handoff discipline

The finite parallel-displacement count is no longer an unverified premise. A complete formal all-affine Klee--Minty corollary would still need the actual vertex recurrence, disjoint-prefix-range cardinality and final-coordinate displacement identities instantiated against this theorem. That is different from solving Polynomial Hirsch. The unrestricted conjecture still requires a polynomial bound on genuine original-edge routes for arbitrary carriers; the already-written adaptive prefix-face comparison works only for its stated family.

Do not restart the disproved universal small global coordinate alphabet or complete forward-stellar-size strategies. Do not transfer this theorem's acceptance to those broader geometric claims. Use accepted results at their exact types and preserve all assumptions. Root STATUS is left unchanged to avoid overwriting concurrent indexing; this handoff and the completion comment provide the new accepted interface. The downloaded bundle includes the original request, verified and publication archives. Raw receipts and derived inspections are distinguished; no separate authenticated root/leaf poll is claimed.
