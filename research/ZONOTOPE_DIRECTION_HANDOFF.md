# PR #317: intrinsic direction lower bound — ACCEPTED

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and LIVE exact
PR heads/comments before choosing work. This continuation found #316 already
accepted/merged and did not resubmit it. Coordination on #316:5749751986.
Reserved #210 and other owned proofs were untouched.

## Authoritative receipt and completed obligation

Hirsch.zonotope_selected_direction_lower_bound is ACCEPTED, publisher live Proved.
Theorem75191fbb-65af-4558-b604-41faefe019f3;
submission93392a4b-67d9-432b-a8ca-eb57f6489164.
Proofef6b66fdc467b8a01dee0d7c10d31cc9f35bd1f6;
run35510763090; trigger5749802849; acknowledgement5749803732;
verdict5749823763. All comments were read back. Gate/verify/publish completed
successfully, report-verify skipped. Three compilation exit codes are0 and all
five transitive axiom reports contain only propext, Classical.choice and Quot.sound.
FIRST compiler gate and FIRST platform submission, exactly ONE trigger.
Do not resubmit this accepted packet.

Read publication_packets/zonotope_direction_lower_bound/accepted-evidence.md,
raw publication-receipt.json, packet-audit.json and manifest.json, and
verification/zonotope-directions/publication-readback.json. Source and metadata
are unchanged from the prepared proof. Proved is publisher-authenticated readback,
not a separate direct platform/root poll. Local Lean was unavailable; actual
compilation is pinned hosted evidence. No raw missing API bodies are invented.

## Mathematical result

In Z=sum_i[0,w_i], select r nonzero generators with pairwise distinct unoriented
directions. Derive actual extreme u,v with u+v=sum_i w_i. Every feasible-point
walk between u,v through nondegenerate whole exposed segments has at least r
steps. The selected family is structural input; neither a graph nor a path-length
or one-direction-per-edge oracle is assumed. Unselected generators are unrestricted.

Finite dual avoidance constructs opposite regular endpoint objectives. For an
arbitrary proposed walk choose arbitrary feasible coefficient representations.
Endpoint saturation forces opposite selected coordinate values. On an actual
exposed edge, every changing coordinate must be tied by its exposing objective;
accepted whole-face geometry makes all such generators collinear. Choose one
changing step per selected direction. Two different selected directions cannot
choose the same step, proving the cardinal bound. Backtracking is allowed.
The424-line accepted Wall prefix and relocated regular_face proof are unchanged.

The intrinsic lower-bound interface is CLOSED. Accepted #316 already gives
all-endpoint upper routes. Do not re-create either as another conditional child.
When all m generators are nonzero/pairwise nonparallel, the two results yield
the classical matching m bound. A formal exact-diameter wrapper is not a new
mathematical advance by itself and was not submitted here.

## Consequence for the current canonical completion: written, not a second Lean theorem

For the d-cube's full Boolean vertex list, #311 uses all ordered segments [a,b].
After a fixed translation, their generator family is all differences b-a. Every
ternary vector in {-1,0,1}^d occurs: choose (a_j,b_j)=(0,1),(1,0),(0,0) for entries
1,-1,0 respectively. Two nonzero ternary vectors are scalar multiples only when
they are equal or opposite after fixing the first nonzero coordinate. There are
therefore (3^d-1)/2 distinct unoriented directions. Translation preserves genuine
exposed-edge walks. Applying the accepted lower theorem shows that some opposite
completion vertices require at least this many steps.

This count/application is a written argument plus exact finite tests, NOT a new
Lean formalization of cube facets, ternary counts or translated completion here.
At d8 the checked count is3280 while the original cube has16 coordinate facets.
Thus a better algorithm cannot make the GLOBAL diameter of this PARTICULAR
completion polynomial in the original cube's facet count. Duplicate slot removal
alone does not help: the count is distinct directions, not4^d ordered slots.

This does NOT obstruct every completion: the cube itself has d generators. It
also does NOT transfer a lower bound to the original summand; contraction can
delete many steps. It is not a Polynomial Hirsch counterexample. The useful next
quantitative task is a genuinely smaller structured completion, or endpoint/fibre-
sensitive routing that avoids paying for the entire completion's global diameter.
Do not assert the all-pairs point-list construction has a polynomial original-row
budget merely because its size is quadratic in a potentially exponential list.

## Reproduction and immutable evidence

Three original ZIP hashes and five frozen file hashes match. Raw compiler logs,
request, audit/manifest and publisher receipt are separate from derived summaries.
Full ZIPs/report/fixtures are in the export and regenerate from the standalone
script; complete runner logs are not claimed committed.

    python3 scripts/test_zonotope_direction_lower.py --out /tmp/zonotope-directions

Tests:30 planar models,154 vertices,264 walks,852 edge occurrences,2016 full-face
checks,360 selected-direction assignments and92 repeated changes. Forty-five saved
audits with constructors disabled and five forgery controls pass. Cube-pair
inventories d1..8 are counted without enumerating completion graphs.
Report7031bytes:ad5632b762ba200b94d26e7ae2d96aff1b63e768649fcb164f4c01130d2ab8f3.
Fixture29225bytes:869b7d7d3dae0ec0f4574af34dafc54269244bd18d2a5df442513f08acbc6405.
Both reproduce exactly in a clean script-only workspace, separately from Lean.

Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.6,
workflows, allowlist, duplicate safeguards and verification/publication credential
isolation are unchanged. Consult live PR metadata for the evidence/merge commits.
