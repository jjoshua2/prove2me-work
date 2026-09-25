# Six-row gain obstruction: ACCEPTED; publication blocker resolved

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and LIVE open
heads/comments before further work. #304's packet is now ACCEPTED. Do not
resubmit it, rename it or repeat its decomposition. #300/#302 and reserved #210
remain their owners' work. No source or run there was changed.

## Exact authenticated outcome

Hirsch.moment_six_row_no_uniform_local_contraction:
- theorem9771bc05-8eb9-4606-a21e-79715873624e;
- submission07282fd9-6960-4e2e-bb91-c94a4d994362;
- publisher verdict ACCEPTED and authenticated live status Proved;
- accepted request SHAac447cd1aa424a3ec0300ca237e32c20a76bbdda;
- run35391838355, new top-level command5735814901;
- resolved acknowledgement5735817052, verdict5735894829.

The 1001-line solution is blob6a26ad84c3d9b84f16a597ef87e27e41a110d9f7,
SHA2562e48c94e404ad7c006ec8442d10766195327413d5923afd58878582908609fe7.
The complete public signature, original definitions/formulas, explanation and
accepted dependency prefix remain unchanged. All three compile modes exit0;
all five proof reports use only propext, Classical.choice and Quot.sound.
Final gate/verify/publish jobs completed successfully; report-verify was skipped.

Read packet accepted-evidence.md and the RAW publication-receipt.json. The three
new ZIP digests and all five frozen file hashes were recomputed. Source files
match the prior successful compile byte-for-byte. Latest raw manifest/audit/request
and separate derived readback are preserved. The publisher's Proved readback is
not a new direct API poll from this chat; missing raw API bodies are not invented.
Local Lean was unavailable; pinned hosted compilation is the actual evidence.

## Preserve history and compatibility boundaries

The first two compiler gates35380332439 and35384230220 failed. Third gate
35386824182 compiled and audited successfully, but the old0.10.4 compatibility
check stopped publication before registration. This continuation changed NO
mathematical source. It reviewed official0.10.5 release a0677c0c4738f16e386545640ceafef4a731cf87
and merged separate maintenance #305 at ec1f9940496d8cb0ed9308ede632d0ec3b62de67.
Only the exact expected-version literal changes at runtime; the guard remains
strict. The skill matches official upstream bytes. Eight offline tests pass.

The fourth compiler gate rechecked the already passing proof, then its FIRST
actual platform submission was accepted. One new trigger this continuation;
no second attempt after acceptance. Earlier failed sources, logs, requests,
blocked detached evidence history and protocol-failure note are historical,
not current blockers. The earlier original manifest remains in the packet;
the current publication-resume manifest separately records the accepted SHA.
Neither manifest entails a proof change. No workflow, API host, allowlist,
duplicate guard, credential split or Lean4.30.0/Mathlib pin changed.

## What is proved, and what is not

For each delta>0, take0<e<1/4 and nodes(-1,0,e,2e,3e,1), using all original
mean-centered inequalities in dimension2. The constructed source u has exactly
two incident exposed-segment neighbors l,r. Both have strictly positive gain
for f=A_0+A_5, but each gain is below delta times f(v)-f(u). Actual vertex
status, complete neighbor classification and a three-original-edge path to v
are proved, not oracle assumptions. The score fractions are

    2e^2/(1+2e^2),
    2e^2(1-2e^2)/((1+2e^2)(1+10e^2)).

This is a counterexample to uniform local score contraction, NOT to polynomial
graph distance. A short route is explicitly retained. Classical geometry and
older written contraction examples are credited; no historical-priority claim.

## New written two-step extension (NOT a new Lean theorem)

MOMENT_TWO_STEP_GAIN_NOTE.md derives the full six-cycle b-l-u-r-c-v-b. The second
outward vertices b,c also have normalized gains below5e and3e respectively.
Together with l,r this shows every non-source vertex reachable in at most two
edges has positive relative gain below5e. Choosing e=min(1/8,delta/10) makes
ALL such gains below delta, while v is exactly three edges away.

The note provides exact c coordinates/slacks, root-sign classification of all
six vertices, exclusion of extra edges, both gain formulas and a universal
inequality proof. Nine symbolic identities and41 exact full-graph references
(164 radius-two endpoints) were checked. This extends the written obstruction;
it is NOT included in the accepted target or separately Lean-audited. Do not
label it Prove2Me Proved or infer a theorem for arbitrary lookahead horizons.

This observation prevents replacing one-step numerical contraction by a fixed
two-step version without further reasoning. It still does not obstruct longer
lookahead, different objectives, or coefficient-independent combinatorial route
control. The unrestricted Polynomial Hirsch upper-bound problem remains open
in this project. Further useful work must control actual legal original-edge
moves rather than repeat these already settled local-score reductions.

## Reproduction

Original regression:59 models,885 square systems,354 vertices/edges,1770 point-row
checks,177 route edges; complete report and fixture reproduced byte-for-byte.
This continuation's supplementary checks are independently reproducible:

    python3 scripts/test_moment_six_row_small_gain.py --out /tmp/six-row
    python3 scripts/test_moment_two_step_gain.py --out /tmp/two-step.json

The supplementary script uses SymPy only for symbolic identities; its finite
reference uses exact Fraction arithmetic and the existing full-graph constructor.
These are supporting checks, not verified Python/JSON or all-real proofs by
sampling. The download preserves original artifacts and the maintenance patch.
Root STATUS was not overwritten beneath concurrent work; this handoff and the
completion cross-reference record the acceptance and remaining exact scope.
