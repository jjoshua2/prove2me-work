# PR336: source-sensitive original-edge rank — internal proof clean, wrapper failed

Read STATUS.md, AGENTS.md, CLOUD_AGENT.md, SKILL.md and CONTINUE_HIRSCH.md, then
LIVE heads, comments and assignments before resuming. Do not repeat accepted
#335 or other targets. #336 remains OPEN/DRAFT; no actual platform submission.

## Identity and actual gate

Repository jjoshua2/prove2me-work; PR336.
Branch proof/source-rank-original-routes.
Target Hirsch.source_rank_reoptimized_original_routes.
Packet research/publication_packets/source_rank_routes.
Frozen tested proof e0dda913902528901bafb5b2c3049cef4dcb142b.
Base/trusted main952c00ef150bedc0b114f7cd428ea90e36daf021.
Source1067 lines/45630 bytes; blob39ab5cec2a687fdf40386c4571fb94278c5cf407,
SHA25645e9676e473e3ff1c61f4ec37b8044971ef2e5f86e94fb4baf1e2edc738c3fc8.
Coordination5784729457; actual request5784984308; acknowledgement5784987737;
run35790637527. All relevant comment identities were read back.

Gate106957989213 succeeded; verifier106958053993 failed driver compilation with
one error at1059:19. The standalone solution and statement were not reached.
Publish106958349197 and report-verify106958348832 skipped. No theorem/submission
IDs, registration, submission, ACCEPTED, Proved or receipt exists from the run.
All6 internal named reports, including the full ranked_route, are standard-only;
public solution still has failed-elaboration sorryAx. No admission was written.
Do not call the complete packet verified based on those helper reports.

## Saved, UNAPPLIED and UNCOMPILED repair

The final per-edge wrapper simplification must connect natural route indices
t.val+1/t.val with t.succ.val/t.castSucc.val while exposing local finite filters.
The proposed one-site replacement is:

    have hs : t.succ.val=t.val+1 := rfl
    have hc : t.castSucc.val=t.val := rfl
    exact ⟨ht.1,by simpa only [hR,R,F,V,hs,hc] using ht.2⟩

All helpers, declaration signatures, public type, other root proof code,
problem.json and explanation.md remain identical. Proposed complete source:
1069 lines/45724 bytes; blob47af41dbdda528862c585c522c2452de918e1af3;
SHA2560ec12af9c127caf4d28df32997ad5607aa8cdb98c69722bf2613ce48f7372853.
The repository stores the exact patch and proposal record; the export also
contains proposal/solution.lean. Apply/check/reverse passes, not compilation.
Further errors can appear. The publication source remains the failed source.

Next proof action: recheck pending jobs/ownership, apply the narrow patch on
THIS PR, review the exact diff, compile locally when possible, then use one
prepared complete final gate with the SAME target. Preserve the first failure.
Do not weaken any hypothesis or change environment/protocol to compile.

## Positive mathematical content and limits

Derive a fixed strictly target-exposing linear h. At each actual vertex x,
F(x) is the COMPLETE actual vertex set satisfying all original rows tight at
both x and target v. Among all affine q_D(z)=1+D(z-v)>0 on F(x), minimize the
number of DISTINCT h(z-v)/q_D(z) values below the CURRENT value at x. Let rho(x)
be that minimum. The internal theorem derives an original neighbor lowering
rho at EVERY edge, including steps acquiring no new target row, then assembles
a route of length<=rho(u) with rho(v)=0.

Old-ratio improvement preserves target locks, gives F(y) subset F(x), and
strictly removes the new neighbor's old ratio from the lower-value set. The old
normalizer remains feasible at y, so reoptimization cannot reset the potential.
Original whole nondegenerate IsExtreme segments and actual vertices are proved.
Exposure, positive normalizers, attained minima and route are outputs.

The public explicit comparison is with anchored slopes; positive rescaling
extends it to arbitrary affine intercepts in the written interpretation.
The numerator is fixed, not jointly optimized at every vertex. Exact finite
H/hull equality and actual endpoints remain. Redundancy, nonsimple/lower-
dimensional cases, dimension0 and coincident endpoints remain. No uniform
polynomial bound on rho, efficient H-to-V, shortestness, or dominance of #335's
different rowwise phase budget is claimed. The mission still needs original-
input control of this potential or a different ordinary-edge invariant.

## Exact computations and code-write limitation

The eight-model suite checks159 routes/180 original edges and6346 order cells,
with6220 rational infeasibility certificates. Source rank beats the minimum FULL
normalized spectrum minus1 in33 states for the SAME numerator and face. Six
nonacquiring edges still lower rho. Nine malformed controls fail. All small
routes happen shortest and no strict extra benefit of reoptimization was
observed; this is not a theorem of shortestness. The extra seven-vertex stress
attempt timed out before a complete result and is explicitly marked incomplete.

The exact solver enumerates ordered ratio partitions, solves linear equality,
strict-order and positivity systems, and certifies every lower-rank exclusion.
The independent consumer reenumerates the exact prefix and verifies nullspaces,
duals and original edges with solver/route producers disabled. This finite-cell
construction is written and executed, not formal extraction or parser verification.

OpenAI blocked the create_blob call staging scripts/source_rank_search.py because
it could not determine the safety status. No blob was returned and no retry or
alternate upload was attempted. Both NEW scripts are retained ONLY in the local
export, alongside three unchanged dependencies. Do not claim them committed or
try to route around that blocked write. The Lean packet does not depend on them.

From the EXTRACTED EXPORT (not the current repository), reproduce with:

    python3 -m pip install -r requirements.txt
    python3 scripts/test_source_rank_routes.py --out /tmp/source-rank-tests

Clean five-script replay reproduced report4317 bytes and fixtures5674989 bytes.
Full JSON is exported, not reconstructed from summary counts. The raw request
ZIP and resolved.json match SHA256db513b8440f3acf910eea14ff604edeb9219311e5c77f8f3e60d3c2db7213ca7.
Only that request artifact exists. No verified packet or publication is invented.
Full compiler error and reports are extracted; runner excerpts are selected,
not full raw logs. Source/fixture consistency checks do not execute Lean.

Local lean/lake/elan and checked caches were absent; toolchain-host DNS failed.
Keep Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
allowed actors, pending/duplicate guards and secret-free verifier/trusted
publisher isolation unchanged. Respect #326,#282,reserved #210 and other owners.
