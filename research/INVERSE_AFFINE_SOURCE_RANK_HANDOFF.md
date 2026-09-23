# PR #337: inverse-affine source-rank reduction — first gate failed

Read all five instruction files and live heads/comments before resuming. Continue
THIS same PR and target. Respect original-row-supported numerator re-selection
claimed in #336 comment5786607495, #326, #282 and reserved #210. Do not duplicate
or resubmit #336. Our coordination is5788446473.

Branch proof/inverse-affine-source-rank; target
Hirsch.inverse_affine_source_rank_reduction; packet
research/publication_packets/inverse_affine_source_rank.
Tested proof631ad17d13be459c7007e2124cc4cbe61ef3299f on main
fdcfc2aaa487a999ba52b6242dc9c8f01b2e0ec4.
Source281 lines/12504 bytes, blob5c63e222a3212882708c26962afba5cfef98ac36,
SHA256ccd8c31d835030f2bc6616dd11f05ff51d39dc5234d1a9aba95895a6252ee29e.
Evidence commits do not replace this exact tested identity.

Actual request5788616533; acknowledgement5788619152; run35815653977.
Gate107036499017 succeeded, verifier107036536235 failed driver compilation.
Separate solution/statement not reached, publish107036826620 and report-verify
107036826426 skipped. One compiler attempt, zero registrations/submissions.
No theorem/submission ID, verified archive, receipt, ACCEPTED or Proved exists.

## Exact next repair

Two errors at59:45 and150:49 pass an image-membership ha to mem_filter. Both follow
an obtain using the same a,ha names as the outer context. At each site replace

    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hai,hal⟩ := Finset.mem_filter.mp ha

with fresh names

    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hai,hal⟩ := Finset.mem_filter.mp hb

Exact patch: research/verification/inverse-affine-source-rank/first-attempt/
proposed-membership-repair.patch. Four lines replace four; every statement,
hypothesis and other line remains. UNAPPLIED to publication source, UNCOMPILED.
Proposed source281 lines/12504 bytes, computed blob
4d696ef44dbf24d528af1ff80d2d027bbf286153, SHA256
49ae6b96e113f033df19d195e60f9a96bf3a3ff994de0885eb6140692a4e4083.
Patch round trip passes. Further compiler errors may appear. The named reports
for global_positive_shift and normalized_direction are standard-only, but
upper_shift, lower_card, optimum and public solution contain failed-elaboration
sorryAx. No admission was written; do not promote clean helpers to acceptance.

After checking live ownership and pending status, apply the exact narrow patch,
compile locally where available, and use one complete prepared gate on this PR.
No second gate was triggered in the initial continuation. Do not modify metadata,
rename the target or loosen hypotheses to obtain compilation.

## Result being completed

For fixed strict h on finite global C and source x!=v in local S subset C,
inverse heights ell_D(z)=(1+D(z-v))/h(z-v) are affine in D. A common shift D+c*h
translates all non-target heights and preserves source-relative upper counts,
while a derived large c makes q_D positive on all C. Positive ratios below the
source are target zero plus reciprocals of upper inverse heights. Thus the
source rank is1+min over ALL D of the upper count, with an attaining globally
positive denominator optimal even against local-positive competitors. Normalized
pair differences lie in ker(h). The public theorem has finite-data hypotheses;
original-route application retains #336's complete vertex/common-face geometry.
No uniform polynomial bound on that minimum is proved. Fixed-numerator scope
must not be silently extended to a row slack vanishing at other vertices.

The new planar algorithm writes D=t*(-h1,h0)+c*h and exhausts pair crossings plus
open intervals. Its written real-parameter completeness and exact implementation
are not a separate Lean theorem. This cost reformulation does not reprove routes,
optimize changing numerators or assert all-dimensional shortestness.

## Reproduction and limits

    python3 scripts/test_inverse_rank_reduction.py --out /tmp/inverse-small
    python3 scripts/test_inverse_rank_reduction.py --large --only rational_circle24 --out /tmp/inverse-24
    python3 scripts/test_inverse_rank_reduction.py --large --only rational_circle64 --target-count 1 --out /tmp/inverse-64-one

The seven COMPLETED configurations contain526 routes/2792 original edges and
9600 cells. The prior exact heptagon input completes49 pairs/84 edges. The24-point
polygon has eight targets; the64-point polygon has ONE, not eight. A separate
64-point/eight-target run timed out and remains incomplete/excluded. These are
planar tests, not64D original routes. Ten malformed controls fail and all six
full outputs reproduce byte-for-byte in a clean two-script workspace. Python,
JSON and an offline consistency checker are not kernel-verified.

The new files inverse_rank_planar.py and test_inverse_rank_reduction.py implement
only the new breakpoint method and original support-line checks. Neither old
blocked supporting script is reuploaded or used by that solver. Full fixtures,
exact prior-state comparison and raw request ZIP accompany the export; committed
summaries are labelled derived.

Only request artifact10731426787 exists:312 bytes, SHA256
f63d8738854a4eb1d8708b67236fad57871a28d91e7dfdead72d33580c7738f2.
All displayed errors/six reports and selected runner lines are preserved. The
full decoded log was read, but excerpts are not full raw archives. No unavailable
artifact is invented. Local Lean/cache unavailable, toolchain DNS failed.
Retain Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
allowed actors, duplicate guards and verifier/publisher credential isolation.
