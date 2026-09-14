# Generic Minkowski core-edge lift: first compile/audit PASS

PR240, branch proof/generic-minkowski-edge-lift. Frozen proof head80f533255175a6dc24c3132feaa01b10ec275180. Actual top-level command5657668062 was read back; bot ack5657669319 resolves run34795161919. The 443-line solution passed its first prepared compile/axiom gate UNCHANGED: driver, solution and statement all exit0; four printed declarations contain only propext, Classical.choice and Quot.sound. No speculative edit or retry occurred. Local Lean/Lake is absent; the successful compile is specifically the pinned hosted result, not Python/source checks.

The publication job was still in progress at this intermediate observation. This is NOT an ACCEPTED or live Proved receipt. Do not duplicate an active publication. Fetch this run's latest comments/jobs/artifacts and preserve its authenticated verdict separately before marking the theorem accepted. The next receipt may supersede this header without changing any proof source.

Verified archive10329616413 has SHA-25604cf2bafa5126b2d6c7173832bf65037a6c77125ae651f1375fd52bf26591de2; its digest and all five frozen file hashes were recomputed. Original solution/problem/explanation are byte-equal to the prepared source. Raw manifest, audit, compile logs, driver and statement are copied beside the packet. The inspection summary is labeled derived, not a fabricated platform response. Solution SHA-256badf57d2b9e493f3030b429df824809f039206d0f1a1fb14086823983ec88651.

## Actual geometric theorem

Target Hirsch.exposed_core_edge_has_minkowski_bridge. Starting with an explicitly exposed edge [u,v] in one nonempty finite-hull component, the proof CONSTRUCTS a new objective and a whole exposed edge in the total finite Minkowski sum, with core components u,v. Each component's exact support segment and nonnegative parallel length are produced. Quotient-space finite separation and a small strict-sign-preserving perturbation derive genericity, rather than assume an edge-lifting or full-slice oracle. Point, parallel, lower-dimensional and redundant-point factors are included. The core edge must be explicitly exposed; the theorem does not independently prove every abstract edge exposed.

This formalizes the forward exposed-edge case of classical Deza--Pournin Lemma3.8 and complements active #239's different affine-envelope counting theorem. No historical novelty claim. The remaining fibre-generic path-existence and full ordinary-edge route assembly are separate; controlled decompositions for arbitrary high-dimensional carriers remain the applicability gap. No new universal polynomial diameter bound is claimed.

## Reproduction

scripts/check_generic_minkowski_edge_lift.py is committed and its readback blob36dc25ed3dd3969d8eb558d58726c57befea49f2 matches tested bytes. SHA-25633d8412978c880ff00a1427e3267660ad6551e9670e2fda10c3140d5df29347b. It deterministically finds a rational generic direction by a finite root-avoidance grid; the checker tests every full component support face without repeating that search. Run with --out /tmp/check.json --fixture /tmp/grid.json, then --verify /tmp/grid.json. The saved regression has96 bridges,7366 independently checked point-sum tuples,12 rejected controls and dimensions up to48 without product-state enumeration. Point-sum products are not vertex counts. The JSON parser/producer are not Lean-extracted.

Read research/GENERIC_MINKOWSKI_EDGE_LIFT.md for the complete argument and precise next geometry. #239/#238/#208/#210 sources and triggers are unchanged. No accepted or pending packet was resubmitted. No pin, workflow, allowlist, permission or secret separation changed. The old unsubmitted internal-normal-form candidate was not chosen or used.
