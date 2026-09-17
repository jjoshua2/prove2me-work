# First actual gate: one coefficient-lambda rewrite error

Derived record of actual GitHub job-log readback, not a platform receipt.
Run35173425528, verify job105049833927, exact proof
29b326b349a71c81990032a43e061a295b084deb. The gate and pinned Lean4.30.0 cache
restoration succeeded. Driver compilation failed and verified-artifact upload
and publication were SKIPPED. No theorem registration or submission occurred.

The sole error was at driver.lean33:34, at 2026-09-17T02:12:29Z:

```text
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (∑ b ∈ ?s, ?f b).coeff ?n
in the target expression
  (fun q => q.coeff (s.card - 1)) p =
    (fun q => q.coeff (s.card - 1))
      (∑ i ∈ s, Polynomial.C (Polynomial.eval (a i) p) * Lagrange.basis s a i)
```

The coefficient lambda produced by congrArg had not reduced before the
finite-sum coefficient rewrite. The correction inserts exactly one line,
`dsimp only at hc`, before the existing rewrite. It changes no theorem
statement, assumption, target metadata, explanation, mathematical argument or
other proof body. See one-site-correction.diff and first-failed-solution.lean.
The source grows from224 to225 lines. New source SHA256:
5f5799763c8754777e3b227865a4eb7faf1c4670cfc697288c37dec09f5b3ace.

The first job printed standard-only axioms for slack_ne_zero. Its four other
requested transitive reports included sorryAx because compilation recovered
from the error. These are NOT successful proof/audit evidence. No admission
was present in the source. The later corrected gate must independently compile
and audit the complete packet.

The resolved request artifact10477322378 was downloaded and hashed independently:
fb7ccd08360dbfb6a9a5a8cef23db27c82a5507a7b10a7a4c68859ba828ce2fe.
It records actor jjoshua2, action publish, PR286, and the exact first proof SHA.
Its original archive is included in the conversation bundle. The diagnostic
above is a selected verbatim compiler excerpt, not the entire job log.

The corrected exact-rational and public-signature regression passes again;
those checks remain distinct from Lean compilation. Local Lean is unavailable.
This is a targeted correction to one observed elaboration issue, not a new
proof design or a weakened goal. No workflow, pin, permissions or secret split
was changed, and no other branch or accepted/pending theorem was retriggered.
