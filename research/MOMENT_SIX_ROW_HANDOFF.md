# PR304: proof compiles; publication awaits protocol refresh

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR
heads/comments before continuing. Do not duplicate any pending/accepted packet.
#300 separated-pair routes, #302 parity work and reserved #210 remain untouched.

## Current formal state

Hirsch.moment_six_row_no_uniform_local_contraction now fully compiles and passes
all five transitive standard-axiom reports. Driver/solution/statement exit0 in
run35386824182, proof e991bc9b85bc60381f1b5fea283f4538dfaaa228. Actual new command
5735218437, resolved acknowledgement5735220244. Gate105735567490 and
verify105735611880 succeeded. All source, original formulas, hypotheses and
accepted dependency bodies are fixed; no further Lean repair is indicated by
this completed gate.

The publisher FAILED before theorem registration because its version check
requires0.10.4 while the official upstream skill advertises0.10.5. Exact error:
Platform skill version changed; refresh the skill before publishing.
Publisher105736124723, fallback comment5735240652, both inspected. No platform
receipt, theorem/submission ID, ACCEPTED verdict or live Proved was obtained.
Do not label a compile as a platform acceptance. The run's overall result is
failure; report-verify105736126638 is skipped.

Read publication_packets/moment_six_row_small_gain/compile-evidence.md and
verification/moment-small-gain/final-run-readback.json. Raw audit/manifest/complete
successful compiler logs are in the packet, separate from derived status records.
Original request/verification ZIPs accompany the export. All five frozen file
hashes and both new archives match. No fabricated raw platform API bodies.

## What is mathematically established by this Lean proof

For every delta>0 construct e=min(1/8,delta/4),0<e<1/4, and the original2D
mean-centered moment inequalities at six nodes(-1,0,e,2e,3e,1). Explicit u,v
are actual extreme points. The COMPLETE exposed-segment neighbor set of u is
{l,r}; both positive target-score gains are below delta*(f(v)-f(u)). A three-edge
original route u,l,b,v is constructed. The two gain fractions are
2e^2/(1+2e^2) and2e^2(1-2e^2)/((1+2e^2)(1+10e^2)).

The proof does not assume a vertex graph, neighbor classification, edge oracle
or short route. It uses the accepted moment vertex/common-row proof, explicit
full slack tables and a positive source-cone/exposing-functional argument.
This refutes a uniform positive per-edge fraction for this particular numerical
objective at fixed dimension and row count. It is NOT a diameter lower bound,
shortestness assertion, or Polynomial Hirsch proof/counterexample. General
routing needs coefficient-independent control of actual edge transitions or
appropriate multi-step progress, not this disproved local-contraction premise.

## Exact repair and history

Source1001 lines, blob6a26ad84c3d9b84f16a597ef87e27e41a110d9f7,
SHA2562e48c94e404ad7c006ec8442d10766195327413d5923afd58878582908609fe7.
It matches the previously saved two-helper patch byte-for-byte. slack_spec now
eliminates impossible finite memberships exactly and exposes the scalar positive
cases. score_values supplies the equivalent reordered denominator to field_simp.
The public theorem AND its full assembly, all definitions/signatures, accepted
544-line prefix and problem/explanation bytes are unchanged. This was the third
compiler gate overall, first passing complete gate, one new trigger this turn.
No speculative further compiler iteration was performed.

The first two runs35380332439 and35384230220 stopped in compilation before any
registration. They remain failed histories, not retroactively successful. The
previous detached evidence commit0429f55bc30d4a9fd2a6b578aa624bb2aecfcd3c was not
made the PR head, and its blocked ref move was not retried. Current proof changes
and current successful verification evidence are separate from that old move.

## Publication prerequisite, not another mathematical decomposition

The remaining immediate task is reviewed trusted-main compatibility with the
actual current platform release. Official source:
prove2me/prove2me_workspace commit a0677c0c4738f16e386545640ceafef4a731cf87,
SKILL.md blob3b64e0d72acd92c8e052b65624c059978ca66748. Its documented0.10.5
change concerns moderator review reports/status/item flags in mission_captain.md.
The exact authenticated response version was not logged and is not invented.
See PROTOCOL_REFRESH_REQUIRED.md. Keep exact-version rejection, duplicate checks,
API host restrictions and the trusted verify/publish secret split. Do not disable
those checks, request a key in chat, or use untrusted PR Python with secrets.

After a reviewed protocol refresh, resume this SAME compiled packet only after
checking live receipts again; no reproof or renamed target is needed. The observed
version-failed run never registered/submitted it, but another agent may since
have done so. Keep this PR draft until authenticated publication is preserved.
No new protocol/guard/workflow/allowlist change is made in this continuation.

## Reproducibility

The unchanged59-model exact Fraction suite was rerun. Both complete outputs match
the prior bytes: report05114a9296c14bd680d1c14279c4cad0262789a9c861e152d6ba053bfd81a2b7;
fixturef72f0b9698aa24f254ce0af05cb4f2fed97dffa1c370106015c08ce514a7ea44.
The test covers885 systems,354 vertices/edges,1770 full row values,177 route edges,
59 saved constructor-disabled replays and five forgeries. This is not Lean
verification of the test code. Local Lean/Lake and compiler-host DNS remained
unavailable; actual compilation is the pinned hosted gate.

    python3 scripts/test_moment_six_row_small_gain.py --out /tmp/six-row-checks

Do not repeat the prior local-repair todo: the two helpers now pass. Preserve
this successful artifact separately from the absent platform verdict.
