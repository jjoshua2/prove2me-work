# First gate: global shift and kernel clean; two image-membership binders need repair

PR #337 remains OPEN/DRAFT and unmerged. Target:
Hirsch.inverse_affine_source_rank_reduction.
Frozen tested proof631ad17d13be459c7007e2124cc4cbe61ef3299f; main
fdcfc2aaa487a999ba52b6242dc9c8f01b2e0ec4. Source281 lines/12504 bytes,
blob5c63e222a3212882708c26962afba5cfef98ac36, SHA256
ccd8c31d835030f2bc6616dd11f05ff51d39dc5234d1a9aba95895a6252ee29e.
No publication source or metadata changed after this gate.

## Actual compilation and publication boundary

Request5788616533 and acknowledgement5788619152 resolve run35815653977 to the
exact tested proof. Gate107036499017 succeeded. Verifier107036536235 failed
driver compilation with two reported application-type errors at59:45 and150:49.
Standalone solution and target statement compiles were not reached. Publisher
107036826620 and report-verify107036826426 were skipped. No registration,
submission, IDs, publisher receipt, ACCEPTED or Proved exists from this run.
This was the first complete hosted attempt; no second trigger was posted.

The named reports for global_positive_shift and normalized_direction contain
only propext, Classical.choice and Quot.sound. upper_shift, lower_card, optimum
and public solution retain failed-elaboration sorryAx. No admission was written;
the full theorem is NOT verified. One harmless sequencing warning is preserved.

Both errors occur after obtaining an image preimage with reused names a,ha and
rfl. The next mem_filter.mp ha receives the outer IMAGE membership rather than
the needed preimage FILTER membership. The diagnostic gives those actual types.
The saved proposal uses fresh b,hb and applies mem_filter.mp hb at exactly those
two sites. All statements, hypotheses, other proof lines and metadata remain.

Patch: research/verification/inverse-affine-source-rank/first-attempt/
proposed-membership-repair.patch. It is UNAPPLIED and UNCOMPILED. Four lines
replace four; complete proposed source remains281 lines/12504 bytes, computed
blob4d696ef44dbf24d528af1ff80d2d027bbf286153, SHA256
49ae6b96e113f033df19d195e60f9a96bf3a3ff994de0885eb6140692a4e4083.
Apply/check/reverse and unchanged public-type checks pass, not compilation.
Further errors may appear. Resume this same PR after fresh pending/ownership
checks, with local compilation where available and one prepared complete gate.

## Mathematical progress and remaining assumptions

The complete written argument identifies fixed-strict-numerator source rank as
ONE plus an unconstrained inverse-affine upper-level count. A common shift along
h enforces denominator positivity on ALL finite global points while preserving
every inverse-height order and coincidence. Positive reciprocal order, exact
target-zero accounting and finite minimization yield an attaining global-positive
optimum even against local-positive competitors. Normalized differences lie in
ker(h); the written effective parameter count is at most d-1.

The finite public statement assumes S subset C, x!=v with x,v in S, and fixed
linear h strictly positive off v on C. No H system or vertex hypothesis is needed
for that algebra. Applying it to #336 requires COMPLETE actual vertex/common-face
sets and #336's strict exposure. No universal polynomial rank bound, general
diameter theorem, numerator re-selection or dominance over #335 is asserted.
The planar breakpoint algorithm and its completeness proof are written/executable,
not separately Lean-verified. Do not call this failed full packet accepted.

## Reproduction and evidence

Only request artifact10731426787 was produced,312 bytes, SHA256
f63d8738854a4eb1d8708b67236fad57871a28d91e7dfdead72d33580c7738f2.
Its original ZIP and exact resolved.json were downloaded/rehashed. The full
decoded verifier log was read through cleanup. All displayed errors and six
reports are extracted with timestamps removed; selected exact runner lines are
not a complete raw archive. No absent verification or publication archive is
invented. The tested inputs are also preserved under first-attempt/tested/.

The genuinely new standard-library planar sweep and independent consumer checked
seven completed polygon configurations:526 routes/2792 original edges,9600 cells,
4844 crossing pairs,1912 nonacquiring steps and194 initially nonpositive witnesses
made globally positive. All observed ranks equal polygon distances, not a universal
shortestness assertion. The exact prior seven-vertex input completes49 pairs/84
edges with236 cells. The24-vertex case has eight targets; the64-vertex case has
ONE target. A separate64-vertex/eight-target run timed out and remains excluded.
Ten malformed controls fail. Six finite algebra dimensions include64; those are
not high-dimensional route instances. Seventy-seven preserved #336 states match
for the same fixed numerator and face. Clean two-script replay reproduces all
six full output files. These tests do not verify Python/JSON or prove all-real
geometry by sampling.

Both new scripts are separate breakpoint/support-line algorithms, not the
previously blocked source-rank scripts. Their exact blob uploads succeeded;
no old blocked file was uploaded or invoked by the new solver. Full fixtures
are exported and regenerate; repository test summaries are explicitly derived.
Local Lean/Lake/Elan and checked caches were absent and toolchain-host DNS failed.
Keep Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
all security guards and the other agent's claim5786607495 unchanged.
