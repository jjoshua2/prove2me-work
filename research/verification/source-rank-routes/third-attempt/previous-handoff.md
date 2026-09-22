# PR #336: second wrapper gate failed; explicit extensional repair proposed

Read the five project instruction files and live heads/comments before resuming.
Continue this same PR and target. Do not reapply the first repair or resubmit
accepted dependencies. #326, #282 and reserved #210 remain separate assignments.

## Exact current state

Repository jjoshua2/prove2me-work; PR #336, OPEN/DRAFT and unmerged.
Branch proof/source-rank-original-routes.
Packet research/publication_packets/source_rank_routes.
Target Hirsch.source_rank_reoptimized_original_routes.
Tested proof b144922b8ca5e4f7fad71aaa0c948892753657c7.
Trusted main 952c00ef150bedc0b114f7cd428ea90e36daf021.
Source 1069 lines / 45724 bytes; blob 47af41dbdda528862c585c522c2452de918e1af3;
SHA256 0ec12af9c127caf4d28df32997ad5607aa8cdb98c69722bf2613ce48f7372853.
The evidence commit does not replace this tested identity or modify its inputs.

Coordination 5785931947, actual new request 5786002661, acknowledgement
5786005146, run 35797243242. Gate 106979273223 succeeded; verifier 106979325443
failed driver compilation, exit 1. Separate solution/statement were not reached.
Publish 106979866989 and report-verify 106979867272 were skipped. Two hosted
compiler attempts overall, one new trigger in this continuation, zero actual
platform registrations or proof submissions. No IDs, receipt, ACCEPTED or Proved.
No third trigger and no post-gate proof/metadata edit.

## Applied first patch and remaining error

The first saved patch was applied exactly: three lines replaced one at the last
public step. Explicit Fin successor and castSucc projection equalities now put
both printed sides at t.val+1 and t.val. The sole error remains at 1061:19:
Lean rejects the final inequality between displayed filter/image cardinalities.
Do not treat alpha-equivalent printing as definitional equality or infer an
exact hidden-instance cause from this log.

Six internal reports remain standard-only, including ranked_route. Public
solution retains failed-elaboration sorryAx. No admission was written. Neither
the wrapper nor the complete public packet has passed.

## New one-site proposal, UNAPPLIED and UNCOMPILED

Retain hs and hc, then use:

    refine ⟨ht.1, ?_⟩
    convert ht.2 using 1 <;> congr 1 <;> ext a <;>
      simp only [Hirsch.SourceRank.lower,Hirsch.SourceRank.ratio,
        Hirsch.SourceRank.face,Hirsch.TargetRows.vertexSet,
        Hirsch.TargetRows.body,R,F,V,Finset.mem_filter,Finset.mem_image,hs,hc]

This attempts explicit cardinality congruence and finite-set membership equality
rather than another whole-expression simplification. Exact patch:
research/verification/source-rank-routes/second-attempt/proposed-extensional-repair.patch.
Proposed full source 1073 lines / 45943 bytes; computed blob
6617ad6d6c02ee0f2fa2cbb4b66c6993b42b375d; SHA256
3e366e4f2472806d216e6024978b7efd2014e9b6d12c03136d779f50a865b85d.
All helper bodies/signatures, public type, other root code and metadata stay
unchanged. Apply/check/reverse passes. This is not compilation; further errors
may appear. The proposed full file is export-only, while the exact patch and
proposal identity are in the repository.

Next: recheck live ownership/pending state, apply this narrow proposal on this
same source, compile locally when available, and use one complete prepared
final gate. Do not weaken the public statement or start an Actions edit loop.

## Mathematical scope retained

The fixed target-exposing numerator h and positive local normalizers are derived.
At current x, the complete actual face F(x) retains every original equation
tight at both x and v. Minimize the number of distinct normalized values below
the current value. Original ratio-improving edges preserve locks; the old lower
set strictly shrinks, and reoptimization cannot reset its rank. Strong induction
constructs the internal route with L<=rho(u), rho(v)=0 and strict rank descent
on every delivered edge, including constant-face/nonacquiring steps.

Exact finite H/hull equality and actual endpoint extremality remain explicit.
No uniform polynomial bound on rho, shortestness, efficient H-to-V/order-cell
search, or dominance over #335's different rowwise budget is proved. Anchored
normalizers are the public comparison class; general intercepts by rescaling
remain written interpretation. The mission still needs original-input control
of the optimum or another positive ordinary-edge argument.

## Evidence and reproducibility

second-attempt/ preserves the tested inputs, old complete handoff, exact request,
full displayed diagnostic/all seven reports, selected runner lines and labelled
derived failure/repair/source/replay records. first-attempt/ is unchanged.
Packet second-gate-evidence.md is current; first-gate-evidence.md is historical.
The raw second request ZIP was rehashed: artifact10724096862, 307 bytes,
SHA25679621ab6cff62cefd32e72db42c59cc168343886580daa1bfe04255e0bf9a477.
Only a request artifact exists. No missing verified/publication archive is invented.
Full decoded runner logs were read; stored extracts are not full raw archives.

The five export scripts reran unchanged and reproduced both complete outputs:
159 routes/180 original edges,6346 cells/6220 exclusions,33 same-numerator savings,
six nonacquiring steps and nine rejected controls. The seven-vertex timeout is
still incomplete, not rerun, and excluded. The small shortestness observation
is not universal. Python/JSON and offline consistency checks are not Lean proofs.

The previously blocked supporting solver upload was not retried or routed around.
Both new scripts remain ONLY in the export with three unchanged dependencies.
Do not claim them committed. Reproduction from the EXTRACTED EXPORT:

    python3 scripts/test_source_rank_routes.py --out /tmp/source-rank-tests

Local Lean/Lake/Elan and checked installations/caches are absent; release/raw
hosts failed DNS. Preserve Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f,
strict0.10.8, allowed actors, duplicate guards and verifier/publisher separation.
