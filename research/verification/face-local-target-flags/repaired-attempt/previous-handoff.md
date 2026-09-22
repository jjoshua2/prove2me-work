# PR #332: face-local target flags — first gate failed at public wrapper

Read STATUS.md, AGENTS.md, CLOUD_AGENT.md, SKILL.md, CONTINUE_HIRSCH.md and LIVE
heads/comments before resuming. #320 and #330 are already accepted/merged.
This is the distinct face-local continuation, not another submission of either.
Keep #332 OPEN/DRAFT. The internal construction has seven clean named helper
reports, but the public solution failed elaboration. No complete passing packet,
Prove2Me registration, submission, ACCEPTED or Proved result exists from this run.

## Exact tested identity

Repository jjoshua2/prove2me-work; PR #332.
Branch proof/face-local-target-flags.
Target Hirsch.face_local_ordered_target_routes.
Packet research/publication_packets/face_local_target_flags.
Tested proof2758b9d7b9ad8a393a270b9c2c93b356ecae772f.
Base/trusted main28d247b919c156696f4b87e1c295f0d86727cd81.
Source1297 lines/55795 bytes; blobe044971a320c27c5b899a961063ae99a2b4cdc6c;
SHA256095a943e655a507455037404f750f96e52f671cb3fe68f20432bf09342f9b620.
Problem772e66d49494e0cdc1b0b073b7d883b0cfc107ca;
explanation4267c14b072d46e0c1b56eecbb9eaba8a5e5a1f0.
Later evidence commits do not replace this tested proof identity.

Coordination5778505922 on #330; actual NEW top-level request5778888834;
bot acknowledgement5778891809; run35744801081. All posted/read back as applicable.
Gate106803499029 succeeded; verify106803568293 failed driver compilation, exit1.
Publish106804105425 and report-verify106804105917 were skipped. Standalone solution
and separate statement compiles were NOT reached. One hosted attempt, zero
platform proof submissions. No post-gate proof/metadata edit or further trigger.

## Actual diagnostics and single-site proposal

The only reported error is driver1265:78, inside the public solution's local
hl equality converting faceLevels to the inline Finset filter/image expression.
After unfold and rw [hV], the goal displays two identical Finset.image expressions.
Do not infer full verification from that display or from clean earlier reports.
The two other diagnostics are unused simp arguments at1136:46/1136:58.

All seven named helpers are standard-only: small_completion, face_vertices_exact,
acquire_on_face, eligible_exists, route_for_flag, charges_le_global and
optimal_flag_routes. The last is the entire internal optimal-order route theorem.
The public solution's report still includes sorryAx from FAILED ELABORATION;
no admission was written in the source. The full packet therefore failed.

Saved repair, UNAPPLIED to publication source and UNCOMPILED:
research/verification/face-local-target-flags/first-attempt/proposed-local-repair.patch.
It replaces only the local hl proof with ext a and explicit membership simp:

    ext a
    simp only [Hirsch.FaceLocal.faceLevels,Hirsch.FaceLocal.faceVertices,
      Finset.mem_image,Finset.mem_filter,hV]

All mathematical helpers, definitions, declaration signatures, public type, other
proof code, problem.json and explanation.md remain unchanged. Apply/check/reverse
round trips pass. The proposed1298-line/55847-byte complete source has Git blob
7cea8154a7fb8647105e4420b8fef167fac324c5, SHA256
0ff21754450c5ab02cf83504d00a3a5832bf88fa7ba06d14413c06a2de316690.
Its complete bytes accompany the export; the repository holds the exact patch.
This is a proposed tactic repair, not a compiler success. Further errors may appear.

Next: recheck live ownership/pending jobs, apply that patch to THIS source and
review the narrow diff. Compile locally where available, then use one complete
prepared final gate on this SAME PR and target. Never weaken the statement or
resubmit accepted dependencies. No second gate was requested in this continuation.

## Mathematical result being completed

For exact P=conv(C)=the ORIGINAL m halfspaces in ambient d and actual vertices
u,v, derive a duplicate-free ordered list J of initially missing target rows,
length<=min(d,m-d), completing the target equations shared by the endpoints.
Before each selected row, restrict actual original vertices to the shared
rows and the earlier SELECTED prefix; charge its distinct values there minus1.
Construct whole genuine original-edge acquisition phases inside those faces,
and minimize the conditional sum over eligible orders. The same route satisfies
K*min(d,m-d) when all returned local charges are<=K.

The order, rank/determining property, complete phase and original-edge route are
derived, not supplied as an oracle. Each step preserves ALL acquired target
rows, including unselected rows. The planned face can be larger than the actual
lock face due incidental acquisitions; its charge is not claimed an exact
current-state minimum. Zero-edge phases for incidentally acquired rows remain.
The helper charges_le_global proves local cost no greater than charging the
SAME list globally. Minimum budget is not shortest-path optimality.

Exact finite H/hull equality and actual endpoints remain explicit. Redundant,
nonsimple/lower-dimensional, zero-dimensional and equal-endpoint cases remain.
No universal small conditional sum is proved. Its K implication retains the
local-charge condition, so this does NOT solve uniform Polynomial Hirsch.
No all-facet nonrevisiting, global objective or efficient H-to-V/flag search claim.

## Executed arithmetic and preserved evidence

18 exact small hulls:650 routes/733 original edges versus726 shortest edges;
7 nonshortest routes,36 multiedge phases and18 nonacquiring steps are retained.
184 cases improve on the OPTIMAL GLOBAL determining-row budget. The independent
consumer checks30238 eligible orders, all prefix faces/levels and whole original
edges. Nine malformed controls fail. Saved replay disables flag/route/edge
production. These are exact tests, not kernel-verified Python/JSON.

Five known triangular stress cases through64D check124 further original edges
and reject4 controls. At64D:128 original rows, global determining cost2^64-1,
local cost64 and a checked64-edge route. Only4D/8D corner spectra are enumerated;
larger counts use the written recurrence. This is a known-family written/exact
application, NOT another Lean instance or #282's owned all-vertex classification.
The adaptive two-level observation from #276 is credited, not claimed novel.

Clean FOUR-script replay reproduces all FIVE complete output files byte-for-byte.
Both new scripts are committed with two unchanged imports. Full JSON reports,
fixtures and controls accompany the export and regenerate; repository summaries
are labelled derived. Commands from the repository root:

    python3 scripts/test_face_local_flags.py --out /tmp/face-local-small
    python3 scripts/test_face_local_triangular.py --out /tmp/face-local-large

Only request artifact10701287910 was produced:307 bytes, SHA256
b6c7b873285f5cba5e745482b6282a684d139dc1177e30c0e3d1a385c5fb93dd.
It was downloaded/rehashed and its exact resolved.json preserved. No verified or
publication archive, complete passing audit or receipt is fabricated. The whole
error context and all eight reports are extracted from the decoded verifier log;
timestamps/linter suggestion bodies are omitted. The separate runner excerpt is
explicitly selected, not a full raw runner archive. The full log was read through
cleanup. The original failed inputs are copied under first-attempt/tested/.

Retained932-line/38243-byte accepted dependency blocks are unchanged; all five
source manifest hashes were checked and the public type matches metadata.
Local lean/lake/elan and checked caches were absent, toolchain-host DNS failed.
Hosted Lean4.30.0 was observed; retain Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f
and strict protocol0.10.8. No pin, workflow, allowlist, duplicate guard or
verifier/publisher credential isolation changed. #326,#282,reserved #210 and
other owners remain untouched. Preserve the first failure when resuming.
