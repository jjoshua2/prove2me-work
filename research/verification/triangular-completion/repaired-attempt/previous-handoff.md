# PR #320: explicit triangular completion lower bound — repair required

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and LIVE exact
PR heads/comments before continuing. Baseline main was
 d3d722007211c6fbb9d28417ef7a1c1b5a47c585.
Branch: proof/triangular-all-completion-exponential.
Packet: research/publication_packets/triangular_completion_lower_bound.
Target: Hirsch.triangular_all_zonotope_completions_exponential.
Coordination5750522099 on #319 was posted/read back before work. #282's separate
positive route/classification packet remains its owner's work. Reserved #210,
other owned branches, and accepted targets were not modified or triggered.

## Actual current status: OPEN/DRAFT, not accepted

NEW top-level command5750632491 began the normal publish command on #320.
It was read back. Bot5750633628 resolved proof
9c4c8c1e046759df90e02115d9cc3847273118fb and run35518652354.
Trusted workflow main was the baseline SHA above. The run completed/failure:
gate106098795378 succeeded; verify106098819456 failed driver compilation with
exit1; publish106098946181 and report-verify106098946536 were skipped.
This was ONE comment-triggered gate and ONE actual Lean compilation.

There is NO passing complete packet audit, verified-packet archive, platform
registration/submission ID, ACCEPTED verdict or live Proved result. The actual
compiler reports for hull_eq_body and directions_separate use only propext,
Classical.choice and Quot.sound. exposed_line, minimal_eq_body,
exponential_completion and solution contain sorryAx from failed elaboration.
Do not mistake those four dependent reports for passing verification.

## Exact errors and unapplied repair

Two sites failed: line1403 attempted Subsingleton.elim for Fin(0+1) in the base
case of supporting_line; line1548 left Fin.last n's value opaque to omega in
minimal_eq_body. The saved proposal replaces both implicit index equalities by
Fin.ext followed by explicit natural-value goals. The first uses i.isLt and
omega to prove i.val=0; the second exposes i.val=n before omega. No hypothesis,
signature, complete public root proof or accepted body changes.

The proposal is UNAPPLIED to the publication source and UNCOMPILED. It applies
and reverses byte-for-byte in an isolated Git workspace. Proposed1649-line,
68361-byte source: blob d601bb6d8c223609a9b9b269385421f4e0bbc39b;
SHA256 0d66d238760cd88b933429d49c0d421a04af8c4c66f13c6ad532feff625b4fb2.
Further errors may remain. Do not infer complete verification from the patch.
No source or metadata edit and no second trigger followed the compiler failure.

The submitted1642-line/68245-byte source remains blob
21b9482d09b3abb5d22ee1a80b6b2561952b4540, SHA256
e6142ce4aca2189943bac4f865c1b6370546f8c4193d7f6b2ead7f9759b5dde3.
Its inherited unused-simp warning is preserved, not cleaned up. Before the first
gate, one blank separator and one leading declaration space differed during
upload; exact source reconstruction reconciled them without proof-token changes.
The exact916-line accepted #319 prefix and203-line #280 namespace are unchanged;
all ten dependency manifest checks passed. Old public targets are not resubmitted.
Local Lean/Lake and compiler-host DNS were unavailable. Source and Python checks
are not Lean compilation.

## New mathematical interface, including its limits

For every0<e<1/2 and dimension n+1, the ORIGINAL body uses exactly2(n+1) displayed
inequalities: 0<=x_n<=1 and e*x_(i+1)<=x_i<=1-e*x_(i+1), i<n. The candidate derives
the entire finite-hull representation, then constructs2^n selected nondegenerate
whole exposed edges by fixing the first n boundary choices and freeing x_n.
Their last-normalized displacements satisfy signed multiplication by e, so
parallelism recovers every bit. The direction-separation and full-hull helpers
have standard-only reports, but the complete exposed-edge application is not yet
verified because of the two sites above.

The intended final theorem applies accepted #319 to ANY nonempty compact Q with
actual equality P+Q=sum_i[0,w_i]. It concludes2^n<=m and constructs opposite actual
completion vertices requiring at least2^n steps on every genuine exposed-edge
walk. No finite-hull, edge-family, direction-count or matching oracle is supplied.
Q need not be convex. Compactness/nonemptiness,0<e<1/2 and whole-set sum equality
remain actual hypotheses. It does not prove a large diameter for the original P.

The sufficient count is2^n, not the stronger full2^(n+1)-1 direction count. No
formal facet-lattice count, exact original shortest diameter, asymptotic domination
lemma or translation extension is included. This is not a Polynomial Hirsch
counterexample. A completed proof would certify a concrete obstruction to
uniformly cheap GLOBAL zonotope completions, without excluding charging surviving
contracted steps, non-zonotopal constructions or other original-edge arguments.

## Evidence and reproduction

The only run artifact is the original318-byte request ZIP10607707101. Its SHA256
was independently recomputed:
202fa6f377f7763368c5df032cb5808758c426ad53c960687735b18793408b59.
Raw resolved.json and the full compiler warning/error/axiom block are preserved.
The whole verification log was read through cleanup, but the committed diagnostic
file is explicitly an excerpt excluding setup/cache/cleanup. No absent API bodies,
verified artifact or publication receipt are invented.

The new177-line exact-rational script ran twice, including a clean two-script
workspace. Eighteen small H models use3822 independent square systems,378 vertices,
189 selected edges and8190 whole-reference support checks. Fifty-four hull records
use1134 convex-combination terms;1092 strict-other-row checks support the written
facet interpretation only. Thirty-two selected larger edges reach dimension64
without full graphs. Sixty-two serialized edge records and54 hull records audit
with producers disabled; six forged inputs fail. These are not extra Lean theorems,
extracted software or a formally verified arbitrary-input parser.

Full report4361bytes SHA256
d562c74a919b67aa0a235646a6210d23ed6690d033834a109e581bcf8c3f1623;
fixture479933bytes SHA256
69d1e0585f2fed7405dfa0b5fe57dedda6692575b71031225ed12ccb3d7eb0d2.
Both runs reproduce these bytes. Full files and the original request ZIP are in
the export and regenerate; repository compact summaries are labelled separately.
The existing #319 reference script is reused unchanged, not overwritten.

    python3 scripts/test_triangular_completion_family.py --out /tmp/triangular-completion

Next is complete pinned compilation/auditing of the saved repair after a fresh
ownership and duplicate check, not a new assumed-family child. Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.6, workflows, allowlist,
duplicate controls and verification/publication credential isolation are unchanged.
Use live PR metadata for the later evidence commit; it differs from the failed
proof SHA. Root STATUS and other existing main files remain untouched.
