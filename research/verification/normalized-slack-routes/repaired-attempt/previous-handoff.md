# PR #333: normalized slack routes — two first-gate elaboration errors

Read STATUS.md, AGENTS.md, CLOUD_AGENT.md, SKILL.md, CONTINUE_HIRSCH.md and LIVE
heads/comments before resuming. #332 is already accepted and merged; do not
resubmit it. This is the distinct row-specific normalized-slack continuation.
Keep #333 OPEN/DRAFT until the complete public packet and actual publication pass.
No complete verified route packet, registration, submission, ACCEPTED or Proved
exists from this first run. The clean one-edge lemma is not a passing full phase.

## Frozen identity and actual command

Repository jjoshua2/prove2me-work; PR #333.
Branch proof/normalized-slack-routes.
Target Hirsch.normalized_slack_determining_routes.
Packet research/publication_packets/normalized_slack_routes.
Tested proof68a18b866c9a3e2cd3ea8a3f2b9f127d46e312ca.
Base/trusted main e6b1ce3a6868ed6a25419d756de6b4ba0d58b49f.
Source1255 lines/54761 bytes, blobcec73e910f915bb2eca51f5e93564e48c39fdc2d,
SHA2565c2fee6a2a2d3c2db51061a3b69251937b1dafd4b7ea068a6973a7d01a1a80ff.
Problemf19a813e28ceb881030d5b904084bb181382f6df;
explanation8ded29786b83409a7e181d13fbd1730ce9d3e17c.
Evidence-only commits do not replace this tested proof identity.

Coordination5779859675 on #332; NEW top-level publish request5780200661;
acknowledgement5780204159; run35754815283. These were posted/read back.
Gate106837780560 succeeded; verify106837878319 failed driver compilation, exit1.
Publish106838418507 and report-verify106838419615 skipped. Separate solution and
statement compiles were not reached. One hosted attempt, zero actual platform
proof submissions. No post-gate source/metadata change or second trigger.

## Exact errors, clean reports and proposed repair

1034:23: acquire_row's last omega call did not equate the local S.card with the
explicit spectrum.card. Its displayed atoms distinguish them. Replace only its
last return with a named intermediate length bound in terms of S.card, then
return that bound. This follows the previously accepted explicit-bound pattern.

1219:75: the public wrapper's hw simplification leaves Finset.image of the
partially applied ratio function versus Finset.image of the explicit lambda.
Add a local function equality proved pointwise with funext/rfl; use it in the
same simplification rather than expecting simp to unfold the partial function.
The unused-simp warning1222:6 records the unsuccessful ratio unfolding.

The exact TWO-SITE repair is stored under
research/verification/normalized-slack-routes/first-attempt/proposed-local-repair.patch.
It is UNAPPLIED to publication source and UNCOMPILED. Proposed complete source:
1261 lines/54933 bytes, blobf0a56f9af96ab0cb19a6cdc14bc84f388923e9d7,
SHA25606243abca39cde66c3491ab7ba95248f74de5ca78993b9b9538525c90568746d.
Apply/check/reverse round trips pass and the full public type is unchanged.
No hypotheses, helper signatures, accepted prefix, metadata or explanation are
altered. The two proofs change only expression conversion, not a new route premise.
Further errors may appear; the proposal is not a compiler success.

Four named reports contain only propext, Classical.choice and Quot.sound:
small_completion, improve_ratio, minimum_completion, weight_uniform.
acquire_row, selected_routes and solution contain failed-elaboration sorryAx.
No admission was written, but the COMPLETE phase/route/public target is unverified.
Preserve these failure reports even after a later success.

Next: recheck live PR ownership, heads and pending/accepted jobs. Apply the saved
patch to THIS same source, inspect its two-site diff and compile locally where
available. Then request one complete prepared final gate on this SAME PR/target,
without renamed replacements, weakened assumptions or duplicate pending runs.
No second gate was requested in the current continuation.

## Actual mathematical work

For exact finite H/hull equality and actual extreme endpoints, supply row-specific
affine denominators a_i+D_i*x strictly positive at all actual vertices. Denominators
need not arise from a common projective chart. Count DISTINCT normalized original
slacks (b_i-A_i*x)/(a_i+D_i*x). Derive a small determining completion among initially
missing target rows, minimum normalized-spectrum weight, and full original-edge
acquisition phases. The same-route conclusion is K*min(d,m-d) when selected weights
are at most K. No graph, supplied basis/selection, short phase or path is assumed.

The new one-edge lemma actually passed its axiom report. At ratio r it uses
f=A_j+r*D_j. The target is better since f(v)-f(x)=r*(a_j+D_j*v)>0. A genuinely
improving original edge decreases the ratio; f changes after each step. Finite
spectrum descent is intended to bound the whole phase without a numerical gain
assumption. All acquired target rows stay locked, including unselected rows.

Exact H/hull equality, actual endpoints and denominator positivity remain public
premises. No automatic good-denominator choice, universally small spectrum,
shortestness, all-facet nonrevisiting, globally monotone objective or polynomial-
time H-to-V/selection is proved. This packet uses GLOBAL normalized spectra;
it does not universally dominate #332's face-local RAW measure on every input.

## New written barrier: do not try to bound #332's raw measure universally

Read research/PROJECTIVE_CUBE_LOCAL_BARRIER.md. It gives a complete WRITTEN proof
for P_d={x_i>=0, x_i+sum_j2^j*x_j<=1}, with exactly2d irredundant genuine facets.
The positive affine q=1-sum_j2^j*x_j and inverse y=x/q yield the unit cube. The
finite H/hull identity, all vertices, facet witnesses and whole original edge
slices are derived. No extra expensive redundant inequality is used.

For all-upper source and zero target, every eligible #332 determining flag uses
all d lower coordinate rows. With k remaining coordinates, the next raw charge
is2^(k-1) for EVERY order, by binary subset-sum uniqueness. Thus the optimized
raw face-local charge is EXACTLY2^d-1. A uniform polynomial bound on that particular
measure is false, even though the original polytope has explicit d-edge routes.
This does not refute #332's valid conditional theorem or Polynomial Hirsch.

Normalize all original slacks by q: they become binary. The normalized routing
statement, once its full proof passes, gives <=d original edges for any pair.
The written family proof already supplies independent original bit-edge routes.
At64D:128 genuine facets, raw minimum2^64-1, normalized budget64 and64 edges.
The all-dimensional barrier/application is NOT a second Lean instance theorem;
exact finite checks support, rather than replace, the written proof.

#203 projective transport and #256 normalized slack SHARE/contraction work are
credited prior work, not superseded. This finite-spectrum descent assumes no
uniform fraction of a numerical gap, and the denominator is positive at target
rather than vanishing total target slack. Those previous barriers remain intact.
#326,#282,reserved #210 and other owned work stay untouched.

## Evidence and reproduction

first-attempt/ preserves exact resolved request, failed inputs, selected actual
compiler diagnostics, all seven reports, selected runner lines, failure record,
unapplied patch and proposal hashes. The complete native verifier log was read
through cleanup; the committed excerpts are not a full raw runner archive.
Only request artifact10707054177 exists:309 bytes, rehashed SHA256
5840375030bcb352618e479e0130a47156202cee5f03357072d84f054bfa68a6.
No verified-packet archive or publication receipt is fabricated.

The23-model exact suite retains564 routes/700 original edges against694 shortest
edges;3 nonshortest,57 multiedge phases,24 nonacquiring steps and53 within-phase
objective changes.724 determining candidates and complete ratios/linearizations
are independently checked. Denominator minima include2^-30. Eight forged controls
fail. Saved replay disables selection/route/edge producers.

Eight projective-cube cases through64D check130 further original edges and260
singleton facet witnesses; d1..4 solve98 row systems,30 vertices and33 orders.
Six malformed family controls fail. Large counts use the written formula, not
full large-graph enumeration. Clean FOUR-script replay reproduces all FOUR full
JSON reports/fixtures byte-for-byte. Python and JSON are not kernel-verified.

    python3 scripts/test_normalized_slack_routes.py --out /tmp/normalized-small
    python3 scripts/test_projective_cube_spectra.py --out /tmp/projective-cubes

The two new scripts import only the two unchanged geometric/reference scripts.
Full outputs, raw request archive and proposed source are in the export and
regenerate; repository test/replay summaries are clearly labelled derived.

Local lean/lake/elan and checked installations/caches were absent; toolchain-host
DNS failed. Hosted Lean4.30.0 and Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f
were retained. Source/patch/Python checks are not Lean compilation. Preserve
strict0.10.8, allowed actors, duplicate guards and verifier/publisher isolation.
The uniform original-edge mission still needs a universally useful derived cost
bound or different invariant, not an assumed small normalized spectrum.
