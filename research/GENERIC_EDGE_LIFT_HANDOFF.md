# Generic core-edge lift: ACCEPTED, live Proved

PR240 on proof/generic-minkowski-edge-lift. Public theorem Hirsch.exposed_core_edge_has_minkowski_bridge, ID9265e218-624c-4c18-86a6-7406004fc14a, submissionc2872155-4d73-4bdd-b9bd-153dab8c619e. The first prepared run34795161919 at frozen proof80f533255175a6dc24c3132feaa01b10ec275180 compiled and audited the443-line candidate UNCHANGED; the first authenticated submission was ACCEPTED and publisher live readback Proved. Do not resubmit. Check current PR integration state, not historical queued notes.

## Evidence and execution

Actual top-level command5657668062, bot acknowledgement5657669319 and verdict5657702465 were read back. Driver, solution and statement exit codes are0; four axiom reports contain only propext, Classical.choice, Quot.sound. Verified artifact10329616413 SHA-25604cf2bafa5126b2d6c7173832bf65037a6c77125ae651f1375fd52bf26591de2; publication artifact10329283379 SHA-256b52e0d058dcd4811ded6f182773e8642a91b5ef6c3095d7634d59e1ac6933648. All five frozen file hashes match, and original solution/problem/explanation are byte-identical. Full raw audits/logs/manifest/publication receipt are preserved beside the packet; derived summaries are explicitly labeled.

The completed jobs were gate=success, verify=success, publish=success, report-verify=skipped. Publish logs were inspected. This is the authenticated publisher's live readback, not a separate direct platform API poll. Local Lean/Lake was absent and the narrow compile could not start; successful Lean evidence comes from the pinned hosted gate. No speculative retry or proof repair occurred.

Solution SHA-256badf57d2b9e493f3030b429df824809f039206d0f1a1fb14086823983ec88651, Git blob884daa33d3890f6d45b8adf8d967aa27eac8f09a. The exact rational producer/checker is committed as scripts/check_generic_minkowski_edge_lift.py, blob36dc25ed3dd3969d8eb558d58726c57befea49f2, SHA-25633d8412978c880ff00a1427e3267660ad6551e9670e2fda10c3140d5df29347b. Its96 cases include7366 exhaustive point-sum tuples, a grid stress needing parameter8,12 invalid controls and dimensions up to48 without product enumeration. These are finite software checks, not Lean extraction or a universal correctness proof of the JSON parser.

## Exact mathematical gain

From a nonempty finite-hull family and a certified exposed core edge [u,v], the theorem derives a quotient-generic objective preserving the core and exposing a line-parallel segment in every factor. Finite endpoint extrema and full convex-hull support propagation give the ENTIRE supporting slice. The total segment has positive length, core components u,v and actual IsExtreme adjacency. Neither genericity nor global slice equality nor edge-surjectivity is an input premise.

The exposed-core certificate stays explicit. This does not separately show that every abstract finite-polytope edge has an exposing functional, nor does it construct an arbitrary carrier decomposition. Lower-dimensional, point, parallel and redundant-point components are included. The classical source is Deza--Pournin Lemma3.8; no historical novelty claim.

## Next useful geometric obligation

#239 is now accepted and merged with its finite affine-envelope count. Reuse its exact theorem and this core-edge existence result; do not republish either. The missing existence step is a generic objective segment INSIDE a fixed core vertex's strict normal region, connecting exposing objectives for the two requested sum vertices while crossing only one-dimensional full supporting faces. This must derive the finite slice witnesses used by #239, not just restate them as hypotheses. Then connect the resulting fibre paths and the actual bridges along every core-walk occurrence, with repeats charged.

The full lift would give L+(L+1)K for a real decomposition and K=sum of factor vertex budgets, as explained in #239's note. Uniform controlled decompositions for arbitrary high-dimensional common faces remain unproved; one must not claim a polynomial Hirsch bound from a supplied factor model. #238 separately owns original-row support-witness existence. Pending #208 and retired #210 remain unchanged and untriggered. The local internal-normal-form draft is not a dependency or submission here.

STATUS is updated without dropping concurrent accepted #239 material. No Lean/Mathlib pin, workflow, permission, allowlist, credential or secret separation is changed. The source tree should retain all concurrent main additions when integrated; proof/statement/explanation stay frozen.
