# PR #294: active-square candidate, compilation blocked

## Live boundary: attempted, not accepted

This continuation starts at main c869bba4af34e6912d043293bff128edc4717801.
Branch: proof/cut-vertex-active-square. PR #294 must remain OPEN and DRAFT.
Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR
heads/comments before more work. Coordination comment5717971751 on #291 was
posted and read back. The chosen obligation is that accepted result's exact
active-row extraction step, not the already accepted catalogue/compactness/
moment-vertex work in #289/#292/#293.

The user-requested NEW top-level publication comments were actually posted:
5718126699 and5718184958, each starting with

    /prove2me publish research/publication_packets/cut_vertex_active_square

Their bot acknowledgements5718128869 and5718187455 resolved runs35249408324
and35249850308 respectively. BOTH driver compilations failed. Publication was
skipped in both; each run has only its resolved-request artifact. There is NO
new verified packet, passing target axiom audit, theorem/submission ID,
authenticated ACCEPTED verdict or live Proved readback. The dependency's old
acceptance is not transferred to this target. No third trigger was posted.

## Mathematical candidate and exact assumptions

Target: Hirsch.cut_vertex_selected_active_square_system.
Take an actual extreme point x of convexHull(S) intersected with finitely many
original linear halfspaces. Reuse accepted #291 to construct a positive,
affinely independent n-point support in S, n<=d+1. The new intended conclusion
selects exactly n-1 cuts actually active at x, retaining the mass equation.
The selected square system has a unique real solution for EVERY signed mass
and vector of selected values, and the actual selected right sides recover the
original weights. No support, row basis, inverse, determinant or rank oracle
is an input. S need not be finite or compact. The base support points may
individually violate cuts. A singleton support selects no cuts.

The written argument starts independent row extension with the nonzero mass
row. Independence bounds selected rows+mass by n. Annihilation of the selected
span implies annihilation of every active row; the accepted column independence
makes its kernel zero. Finite-dimensional rank gives the reverse inequality,
then surjectivity and unique signed-data recovery. Classical basis extension
is credited without a historical novelty claim. It proves existence, not a
kernel-verified executable greedy selector or uniqueness of the chosen support.

Read CUT_ACTIVE_SQUARE_PROOF.md for the written proof. The formal candidate
has not yet passed Lean; no statement here should be reported as an accepted
new theorem. The remaining unrestricted issue is still the quantitative size
of a complete image/support catalogue or a different original-edge routing
argument, not merely local square-system recovery.

## The two observed failures and proposed next local check

First proof4305d3e6837a7879b92a74a73d355a824adedc25, run35249408324,
verify job105297780538: at line404 the auxiliary linear functional's map_smul
proof left (RingHom.id ℝ) c unreduced, so ring failed. The single submitted
repair added RingHom.id_apply to the existing simp list. All helper/public
signatures, hypotheses, bounds and problem/explanation bytes stayed unchanged.

Second proof590764458d8d21659d66363d302f270fd662dcd9, run35249850308,
verify job105299281458: the earlier scalar diagnostic disappeared, but line415
now failed because simp only left the bundled linear map applied to the mass
row unreduced. The displayed goal is the dot functional applied to (fun _=>1),
while the hypothesis is sum_i u_i=0. The generated sorryAx in the new helper
and root is FAILED elaboration output, not a passing audit. Further downstream
success has not been established merely because this is the reported location.

The separately stored proposed-local-repair.patch replaces that none branch
with an explicit change to sum_i u_i*1=0 and simplification of mul_one. It is
NOT applied to submitted solution.lean and is NOT Lean-tested. No further
hosted run was used as an edit/compile loop. The next step is a pinned LOCAL
compile/audit of this proposal and the full source, then a prepared new comment
only after checking live ownership and newer run/submission state. Keep the
previous two failures and do not claim that the proposal is already sufficient.

Latest submitted source blob bb49b04ab2b71b0973b3f288d61d70b8646f71d0,
SHA256 213b0ce24bc95656287a042e8e6fd1f76cb498555a23110c7beded6a0f20b613.
First failed source blob1cffe837e66e46c5491b671d11cb9cb76d7ca63f is preserved.
The first applied one-line diff, both exact source snapshots, selected diagnostic
excerpts and raw resolved requests are separate files under
research/verification/cut-active-square/. Excerpts are labelled as excerpts,
not full runner logs. No successful packet-audit.json or publication receipt
has been fabricated.

## Artifact and dependency provenance

First request10509011859, SHA256
813f4a746f22f8ac99d79fab5941c0cb9474fc08e7240d8479c7729f9d310e85.
Second request10509167266, SHA256
83bc686544c51656d371bd73ba84c6850d1e00b699f58f0ae7927c8633a6656b.
Both original ZIPs were downloaded and hashed; their complete resolved.json
files are retained. The second run's last observed state is completed/failure:
gate success, verify failure, publish skipped, report-verify skipped.

Accepted #291 source at64b73e31cdf368e36e6bd76f1710f4fc97760ebb was reused
in full with only its old root/print name changed. Its archive10491146791
SHA2567595b41fcca904270cb8c192d7c6d960fbcf3a74c9a10787bb8fbe6904cd1d00
and all five frozen file hashes were checked. Its public target was not
resubmitted. The new submission's source manifest is a derived local identity
record, NOT an artifact of a successful Lean gate.

## Executed exact tests, separate from Lean

The standalone Fraction script tests96 augmented row systems,288 arbitrary
signed recoveries,2448 inverse-product identities and1332 small candidate row
subsets. Seven actual simplex-cut vertices through dimension16 include74
original active rows and redundant cuts. Positive support points outside the
cut body are deliberately retained; dimension0 gives singleton support with
an empty selected-cut set.

Five adverse controls include a rank-deficient support, explicit loss of the
mass equation, and three forged row/inverse certificates. The mass omission
is a mathematical rank example, not a claim that five JSON inputs were parsed
and rejected. Four stored in-memory inverse records replay with selection,
rank elimination and inverse discovery disabled; these are not serialized
large-instance fixtures or a verified runtime selector.

A separate one-script workspace reproduces the full report byte-for-byte.
Source SHA25663af7f3832d5a183c151eaac41320e5469d9fe25fa43beece1c5d4c946b4496f;
Git blobb8de11ea698e43de24ab31aec47c90cd7c32d66b.
Report SHA256eac78aaed169461a35d3544dcaf063e2b65363c2aa145830247602171acd453c.

    python3 scripts/test_cut_active_square.py --out /tmp/cut-active-square-tests.json

Root STATUS and all other existing files are left unchanged. This handoff and
PR comments record the current failed attempt without overwriting another
agent's index. No local Lean/Lake exists in this runtime; Python is not a Lean
substitute. No fresh authenticated root/leaf mission poll is claimed. Reserved
#210, #270's blocked companion, other owned branches, Lean4.30.0/Mathlib pin,
protocol0.10.4, allowlist, duplicate safeguards and trusted credential isolation
are unchanged. Do not merge this PR as a verified or accepted result.
