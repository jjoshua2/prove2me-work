# First gate diagnostic: public-wrapper matching only

This is a derived record of actual GitHub job-log readback, not a platform
verdict. Run35249570081, verify job105298337438, checked proof
84821b392da2c393b895f1539a4d92e1aeb0f079 with pinned Lean4.30.0. The gate and
cache restoration succeeded. The verifier failed at the public solution wrapper,
driver.lean line582, at 2026-09-17T16:56:53Z. Publish was SKIPPED: this attempt
created no platform theorem registration or submission.

The sole compiler error was a rewrite-pattern match:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ∑ i ∈ ?m.360, Hirsch.MomentBarycentric.row a z i = ↑(Finset.card ?m.360)
in the target expression
  [the same original rows and active sets, expanded in the public target]
```

Every substantive new helper compiled in this first run. Its four helper
printouts list only propext, Classical.choice and Quot.sound:

- Hirsch.MomentEdges.common_is_erase
- Hirsch.MomentEdges.common_slice_eq_segment
- Hirsch.MomentEdges.interior_tight_rows
- Hirsch.MomentEdges.exposed_edge

The public solution reported sorryAx as Lean recovered from that failed rewrite;
it was NOT verified or publishable. The source contained no proof admission.
The accepted dependency's harmless linter warnings are unrelated to this failure.

The targeted correction first uses `change` to express the inlined public target
with the already-defined original `row` and `active` names, then supplies the
explicit common-row set to `sum_rows_eq_iff`. No mathematical lemma, public
signature, assumption, conclusion, problem.json or explanation.md changes.
All new helper bodies and the complete accepted dependency prefix are byte-
identical before and after. This is one diagnosed elaboration correction, not
a new speculative proof design or a weaker statement.

Initial source SHA256:
efd2a11cc57bff285ef97f8aa326747bbfb57aed6a56f84c0c014fd5a656760f.
Corrected596-line source SHA256:
a0e6bb32eca92681ed7e526f68c66d75348421f9863a11aa0ccbc11016bfcc34.
The exact-rational/source suite passed again, but does not prove Lean compilation.
Local Lean remains unavailable; the corrected final gate must establish the
whole packet's compiler, axiom and separate publication status.
