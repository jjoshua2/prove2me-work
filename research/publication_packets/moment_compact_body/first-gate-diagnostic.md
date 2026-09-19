# First compiler gate: local coefficient simplification errors

This is a derived record of the ACTUAL GitHub job log, not a compiler transcript
invented from source inspection. Run35208275882, verify job105159366079, checked
proof566103676a5d5a855c6c3f8395fe0662d4857d8e. The pinned Lean4.30.0 environment
restored successfully. At2026-09-17T10:02:49Z compilation failed inside the new
coeff_slack lemma. Publication and verified-packet upload were SKIPPED. This
first run registered and submitted no theorem.

The first diagnostic at driver.lean408 was the remaining off-diagonal goal:

```
j l : Fin d
h : not (l = j)
hv : j.val + 1 != l.val + 1
|- j.val = l.val -> x l = 0
```

The simplifier had reduced successor equality to value equality, so the supplied
successor-inequality fact did not match. The correction proves j.val != l.val
directly from h, using Fin.ext on the reversed equality, and supplies that fact
to simp. This is an elaboration repair of the same off-diagonal zero coefficient.

The second diagnostic at driver.lean416 was `simp made no progress` on the
positive-degree coefficient of the constant polynomial one. The correction
uses Polynomial.coeff_eq_zero_of_natDegree_lt with natDegree_one=0 and the
positive index j.val+1 instead of relying on that simplification.

An equivalent convexity estimate is additionally spelled as two component
inequalities rather than one combined add_le_add application. This small proof-
spelling change is disclosed; it does not change any statement, assumption or
argument. All changes remain inside the new MomentCompact namespace. Every
accepted dependency body, the public theorem signature, problem.json and
explanation.md are unchanged from the first gate.

The corrected600-line source has SHA256
0391b4850867227cb6ba3f09be7ea0f510f5162bdbe22099de21b5c4b64f73e1.
Its Git blob is6b384a357508e9b00cb2462cd982039b9f7a8baa. The exact source diff is
included in the local bundle. The rational/signature suite passes again but is
NOT a local Lean compile. The local runtime still has no Lean/Lake executable.

The failed run's zero_interior audit used only standard logical axioms; the
coefficient-dependent theorem audits included sorryAx from Lean's recovery after
the failed lemma. No admission was present in the source. Those declarations
were NOT verified by the failed run; the corrected gate must audit them afresh.
The first request artifact10491560073 recorded the exact first proof SHA.

This is one targeted correction round following real diagnostics, not a changed
public target or an exploratory proof redesign. No workflow, permissions, pins,
credentials or trusted-publisher separation changed. Read the later run/receipt
before claiming compiled, ACCEPTED, or Proved.
