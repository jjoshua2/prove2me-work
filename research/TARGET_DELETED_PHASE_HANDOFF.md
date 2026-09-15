# Resume from target-deleted phase counts, not another polygon selector

Read live STATUS and open PRs. This work consumes the unchanged #253 selector
and #254 construction helpers; #255 was already independently implementing
same-anchor shortening and is not copied here. #244/#250/#238 remain assigned.
No accepted or pending packet is republished and no workflow/security pin changes.

## Exact completed mathematical argument (written, not Lean)

During a retained h-face phase, delete all unlocked target inequalities and
keep already locked target equalities. All pre-acquisition original vertices
remain vertices: they have h independent active NON-target rows. Only e=m-d
inequalities remain. The original phase basis makes h of them nonnegativity
coordinates. One sufficiently large analysis-only total-slack cap gives an
h-polytope with at most e+1 facets, strict at every counted vertex. UBT bounds
its vertex count by U(e+1,h), the cyclic formula. It need not be simple.

A loop-erased phase of L edges has exactly L pre-acquisition vertices; the
last acquisition endpoint is NOT counted. So L<=U(e+1,h), not U-1. This is
counting original vertices, not projecting a shorter auxiliary path. Different
phases cannot repeat pre-acquisition vertices after target locks increase.
For the actual complete-polygon algorithm, its final polygon tail is shortest:

    L<=floor((e+2)/2)+sum_{h=3}^r U(e+1,h), r>=2.

This gives quadratic four-/five-face tails and a Fibonacci O(phi^e) all-dimension
account. It is still exponential and weaker asymptotically than classical
general quasipolynomial existence estimates. Do not announce a new best diameter
bound. A new formula is not a new route: the actual selector is unchanged.

The target-deleted #255 hidden-family polyhedron is exactly a cube with2^d
vertices and exponentially many target-free square faces. So a POLYNOMIAL
conclusion cannot come merely from bounding the entire relaxed inventory.
The next challenge must exploit which vertices/faces are actually visited.
The family and short-route construction belong to #255, not this contribution.

## Reproduce and verify

Run both stages of scripts/test_target_deleted_phase.py. It imports unchanged
scripts/two_face_acquisition.py, simple_tangent_policy_audit.py,
test_weighted_face_retirement.py and three_dimensional_face_accounting.py.
All source/dependency identities are in TARGET_DELETED_PHASE_SOURCES.json.

The644 tested routes have1826 edges,1574 cap cells and9875 restricted inverse
identities. There are32 independent cap enumerations, four nonsimple caps,
96 extra cap vertices outside original cuts,26 search-disabled audits and
nine malformed controls. All actual routes in this corpus have no loops;
this does NOT strengthen the theorem to arbitrary raw traces. Full receipts
and fixtures regenerate and are bundled; the committed summary is explicitly
derived local evidence, not an authenticated platform verdict.

The test and ledger run no Lean. No new theorem skeleton, hosted compiler,
publication or axiom audit is needed for these research-only files. Preserve
this distinction when updating the frontier. No background monitoring is promised.
