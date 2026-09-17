# ACCEPTED: explicit barycentric incompatibility of original moment rows

`Hirsch.moment_curve_barycentric_nonfaces` is ACCEPTED. The trusted publisher's
authenticated readback is Proved. This supersedes the prepared/pending and
compile-only records for this packet. Do not resubmit it.

- PR: https://github.com/jjoshua2/prove2me-work/pull/286
- Theorem: e37928aa-132f-4b32-ba91-47b4a1f75fa4
- Submission: 7fe04fd6-07d9-4ffc-83d0-bc44f67374a6
- Accepted proof SHA: 5b44ad2795b85acb693e6e9f44039e9d9c425e85
- Successful run: https://github.com/jjoshua2/prove2me-work/actions/runs/35173820765
- Actual corrected trigger: https://github.com/jjoshua2/prove2me-work/pull/286#issuecomment-5707435094
- Bot verdict: https://github.com/jjoshua2/prove2me-work/pull/286#issuecomment-5707465522
- Verdict time: 2026-09-17T02:20:20Z (September16,22:20:20 America/New_York)
- Accepted solution SHA256: 5f5799763c8754777e3b227865a4eb7faf1c4670cfc697288c37dec09f5b3ace

## Exact new formal result

Let a be ANY injective real parameter map on m labels, d any natural dimension,
and s any selected set with |s|>=d+2. Define

    w_i = inverse(product_{j in s minus {i}}(a_i-a_j)),
    row_i(x) = sum_{j=1}^d (a_i^j-average_l a_l^j)*x_j.

The theorem derives all selected weights nonzero and

    sum_{i in s} w_i*a_i^r=0, for every0<=r<=d.

For EVERY feasible point satisfying ALL original inequalities row_i(x)<=1,
it produces both a negative-weight selected row and a positive-weight selected
row that are strictly slack. Neither full sign class can therefore be tight
simultaneously. Applying the statement to x=0 also proves both classes nonempty.
No affine-dependence relation, rank oracle, optimizer, sign ordering or support
witness is supplied. The target contains the explicit weight and row formulas.

The proof takes the coefficient of degree|s|-1 in Lagrange interpolation,
derives positive polynomial values on both weight signs, and applies that fact
to the actual slack polynomial. Its average over ALL original labels is1, so
it is nonzero. The original mean is not replaced by the selected-set mean.
The valid zero-dimensional case is included. No separate boundedness or
polytopality premise is needed for this inequality statement.

## Relation to the earlier accepted work

The live read found #285's small-face witness result already ACCEPTED, so it
was not edited or retriggered. The new result is its complementary exclusion
mechanism. #281's stellar count and #284's protected-state count are separate
accepted results, not republished by this packet.

For the intended odd-label (k+1)-families, even separators yield an alternating
weight sign pattern. The present theorem then supplies whole-set incompatibility,
while #285 supplies proper-subset feasibility. That general parity identification,
minimal-nonface catalogue/cardinality, geometric realization and assembly with
#281 are NOT newly formalized here. Numerical checks of the application do not
upgrade those interfaces to accepted Lean theorems. This is not a solution of
Polynomial Hirsch, a new route-length bound or a historical-priority claim.

## Actual compiler and publication history

The first224-line source reached Lean in run35173425528. Its single error was
an unreduced coefficient-extraction lambda before a finite-sum coefficient
rewrite. That run never published or registered a platform theorem. The first
source, selected diagnostic and exact diff remain under
research/verification/moment-barycentric/.

The sole correction inserted `dsimp only at hc`. No public type, hypothesis,
problem.json, explanation or other proof body changed. The corrected225-line
solution, driver and target statement all compiled with exit0. All FIVE
transitive proof audits use only propext, Classical.choice and Quot.sound.
Harmless deprecated-push_neg and unused-ring warnings remain visible in the
raw driver log. They were not suppressed or edited after verification.
The expected target placeholder is not imported into the actual solution.

Its first ACTUAL Prove2Me submission was accepted. Both requests were real new
top-level PR comments through the existing workflow; no workflow_dispatch,
new token, pin, workflow, permission or secret-split change was used. Local
Lean/Lake was unavailable. The compiler evidence is the pinned hosted run,
not the exact-rational or source-string checks.

## Raw evidence and independent checks

The verified artifact10478225583 archive digest was independently recomputed:
b94ddaddb0cf4d06cf5ce5a467d4625c3c7f5ec7617a4b37d79ae9f01688fcad.
The publication artifact10477164872 archive digest was independently recomputed:
208981ffe1e52ec2d751dd60a91d51ad6e8f0e73de5fd508d15894b6d65eca13.
Both original ZIPs are in the conversation bundle. All five frozen source,
driver, target, metadata and explanation hashes match the verified manifest.
The solution/problem/explanation are byte-identical to the corrected candidate.
Both resolved-request ZIPs also have independently verified digests and exact
source-head readbacks.

packet-audit.json, driver-compile.log, verified-artifact.json and
publication-receipt.json are exact raw artifact files. The readback JSON and
accepted-source marker are explicitly derived local records. The publication
ZIP contains an aggregate receipt and the generated comment, not individual
raw API response objects. Proved is the trusted publisher's authenticated
observation, not a separate fresh direct Prove2Me API query from this chat.
No missing raw response or new mission-root status is invented.

The standalone rational/signature suite covers1125 cases,6577 moment equations,
11261 original-row checks and8647 inverse weights;76 small odd-set applications
and354 proper-face checks; three selected larger cases in dimensions16/32/64.
Nine invalid controls fail and15 witness audits pass with producers disabled.
Corrected clean replay matches the full report and35838-byte fixture exactly.
Those tests support interpretation but are not a formally verified Python program.
Post-verification evidence additions do not alter any accepted proof/target bytes.

## Reuse and next obligation

Reuse this accepted theorem and #285 rather than duplicate either packet. A
next formal geometric assembly must derive the sign partition and finite family
before applying #281. A conjecture solution still needs a universal polynomial
upper bound on genuine original-edge routes. The accepted incompatibility
mechanism alone neither supplies nor assumes that bound. Other agents' owned
branches and accepted/pending submissions remain unchanged.
