# First gate: one diagnosed rewrite error, no publication

This is a derived record of actual GitHub run/job-log readback, not an invented
platform receipt. Run 35154274683, verify job 104989890881, compiled proof head
720e34812a045f54cf4adabfd36335a56ca1815a under Lean4.30.0 and the unchanged
committed Mathlib pin. The gate and pinned environment restoration succeeded.
The compile/audit step failed at driver.lean line255. Publish and verified-
artifact upload were skipped; no theorem registration or submission was made.

The sole Lean diagnostic at 2026-09-16T21:48:24Z was:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Nat.succ ?n
in the target expression
  (V (i + 1)).card = (V 0).card + (i + 1)
```

The target already used i+1. Correction commit6e3d2108a7255e46af9db8df2b265e5b3547ef92
removes only the redundant Nat.succ_eq_add_one from that rewrite list:

```diff
-      rw [Nat.succ_eq_add_one, hV i hit]
+      rw [hV i hit]
```

The public theorem signature, problem.json, explanation, all hypotheses and the
mathematical argument are unchanged. The source remains295 lines. Corrected
solution SHA256: 2b579f45c887c6ccc44b1caaf2a0686c90c9634fd080cb4010af36da18f83959.
The independent finite regression and exact target-signature comparison pass
again; those checks are not compilation.

The first run printed standard-only transitive axiom lists for
minimal_descendant, born_minimal and step_growth. The final sequence theorem
and solution printed sorryAx because Lean recovered from the compilation error.
Those final declarations were NOT successfully audited and are not claimed
verified. No proof admission was present in the source. A corrected final gate
must compile and audit the entire packet independently before publication.

Local Lean/Lake remains unavailable. This is one targeted correction to an
actual observed diagnostic, not a changed statement or speculative proof redesign.
The next publication command uses the same existing open-PR comment workflow;
no workflow, permissions, credentials, toolchain or trusted secret split changes.
