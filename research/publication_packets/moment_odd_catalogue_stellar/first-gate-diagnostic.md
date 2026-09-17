# First gate: one equality-normalization issue, no platform submission

This is a derived record of the actual complete GitHub job-log readback, not a
raw platform response. Run35178680553, verification job105065975944, checked
proof b5b6086f23046dcfec1dde23fcef400d5407e491. The trusted gate and pinned
Lean4.30.0 environment succeeded. The driver compile failed; artifact upload
and publication were skipped. No theorem registration or submission was made.

At 2026-09-17T03:36:12Z the compiler reported two errors, both inside
image_odd_injective, at driver.lean lines815 and821. They have the same cause:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (fun S => Finset.image oddLabel S) T
in the target expression
  oddLabel a ∈ Finset.image oddLabel T
```

The symmetric branch had `(fun S => Finset.image oddLabel S) S` in the equality
and `oddLabel a ∈ Finset.image oddLabel S` in the goal. The equality supplied
by Function.Injective retained its lambda application while the membership
expression was already reduced. The correction adds exactly one line after
introducing S,T,h:

```diff
   intro S T h
+  change S.image oddLabel = T.image oddLabel at h
   apply Finset.Subset.antisymm
```

This exposes a definitionally equal equality to the existing rewrites. No
statement, premise, definition, conclusion, dependency proof, problem.json or
explanation.md is changed. The source grows from993 to994 lines. Corrected
SHA256: abc6478c79e19c9010da6b80ad3c278e504b7cf1a5b87ef03136ba0a6f0fcc2c.
Corrected Git blob:8b9717e907d18bd979b9c13a3e29f2722f077574.

The first run already printed standard-only transitive axiom lists for
odd_subset_not_face and catalogue_minimal. It printed sorryAx for catalogue_card,
stellar_bound and solution because Lean recovered from the failed helper. Those
final declarations were NOT verified. The source contained no proof admission;
a corrected full gate is required before publication or an acceptance claim.

The complete exact-rational and public-signature regression passes again. It
is NOT Lean compilation. The local runtime still lacks Lean/Lake; this is one
targeted repair of a real compiler diagnostic, not speculative redesign or
weakening of the theorem. A second prepared comment uses the unchanged trusted
workflow. Do not repeat a request while it is pending, and preserve its outcome.
