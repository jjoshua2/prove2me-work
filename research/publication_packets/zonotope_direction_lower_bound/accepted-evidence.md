# ACCEPTED: intrinsic selected-direction lower bound

Target: Hirsch.zonotope_selected_direction_lower_bound.
Theorem: 75191fbb-65af-4558-b604-41faefe019f3.
Submission: 93392a4b-67d9-432b-a8ca-eb57f6489164.
Authenticated verdict: ACCEPTED. Trusted publisher live readback: Proved.
Do not resubmit this packet.

## Actual request and first-pass verification

NEW top-level PR #317 comment 5749802849 began
/prove2me publish research/publication_packets/zonotope_direction_lower_bound
and was read back. Bot 5749803732 resolved proof
 ef6b66fdc467b8a01dee0d7c10d31cc9f35bd1f6
and run 35510763090. Authenticated verdict 5749823763 was posted at
2026-09-20T12:33:38Z and read back. Trusted workflow/publisher main was
7b487ef9b0f9e92e5718fb395ed36785b338f4b5, not the proof SHA.

Gate106078154010, verify106078173565 and publish106078437475 completed
successfully; report-verify106078438300 was skipped. Driver, solution and exact
target statement compiled with exit0. All five transitive reports contain only
propext, Classical.choice and Quot.sound. Full proof compiler logs have no
warnings. The target statement's intentional placeholder is not in solution.

This is the FIRST compiler gate and FIRST platform submission, with exactly ONE
new trigger. The653-line/26759-byte source and both metadata files remained
unchanged. Source blob da350f3cc013086fdfd67beeb357bd6b76879e48;
SHA256 d3150b17fd5db0866cbec7c86925084e1af3a86326af62695abd89a12fa69ea1.
Local Lean/Lake was unavailable; compilation is specifically the pinned hosted
evidence, not source comparisons or exact-rational tests.

## Exact new theorem

From arbitrary segment generators and a selected family of r nonzero pairwise
nonparallel generators, construct opposite actual extreme points u,v of the
ORIGINAL coefficient segment sum, with u+v=sum_i w_i. EVERY finite feasible-point
walk from u to v using nondegenerate whole exposed segments has length at least r.
The exposing objective, coefficient representations, change steps and injection
from selected directions to steps are derived. No path-length, graph, change
budget or endpoint-objective oracle is assumed. Other generators may be zero,
parallel, opposite, repeated or rank deficient. The structural selected-direction
hypotheses remain explicit.

The complete424-line accepted Wall prefix is byte-identical to #313. Its
regular_face proof body is also byte-identical under the new namespace. Each
actual edge's exposing functional fixes all nontied coefficients. The accepted
whole-face converse confines changed generators to one direction. Opposite
endpoint saturation forces every selected coefficient to change, so choosing
one changing step per direction gives an injection Fin r -> Fin L.

This is a lower bound, not path existence; accepted #316 supplies routes
separately. The theorem is classical in substance, not a new best diameter bound
or historical first. It is not an original-H facet bound or Polynomial Hirsch
counterexample. The explanation gives a written cube-pair-completion application;
that finite count and translation are not additional Lean theorems in this packet.

## Raw evidence and reproduction

All THREE original archive hashes and all FIVE frozen file hashes were recomputed.
Request10605785407,315bytes:0058eda22e40164b8ac8c1ff532df16b41032247e5db59d55abe9a6b45d46d86.
Verified10605171677,22360bytes:ca177c8baaddc2edfb492e98ec6bf86bdd8909b7d160fa553cf1db0e2f8a22de.
Publication10605716251,911bytes:11d9f1067f463156d7e0ff4f987222094578b986ddb173a09b5ee2b312ce0836.

Raw compiler logs, manifest/audit, driver/statement, resolved request, verified
aggregate and publisher receipt/comment are preserved separately from derived
readbacks. Both job logs were inspected through cleanup. Proved is authenticated
publisher readback, not a second direct platform or mission-root poll. Individual
API response bodies and complete runner logs absent from the export are not
fabricated. Original ZIPs and full test outputs accompany the bundle.

The standalone rational suite checks264 walks/852 edge occurrences across30
complete planar models, including backtracking, empty selected families and zero
generators. It checks2016 whole-face points and360 direction-to-step assignments,
retaining92 repeated changes. Forty-five saved audits run without hull/regular
objective construction; five forgeries fail. Exact cube-pair direction inventories
through d8 are checked without completion-graph enumeration. Full7031-byte report
and29225-byte fixture reproduce byte-for-byte in a clean script-only workspace.
These are supporting tests, not Lean-extracted software or verified JSON.

Pins, strict0.10.6 guard, workflows, allowlist, duplicate safeguards and credential
separation are unchanged. Reserved #210 and other owned proof work were untouched.
