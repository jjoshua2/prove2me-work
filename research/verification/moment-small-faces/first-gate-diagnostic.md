# First gate: two diagnosed polynomial-helper errors; publication skipped

This record quotes selected diagnostics from the actual GitHub verify-job log,
not a separate Prove2Me response or a complete raw log export.

- PR: 285
- Run: 35166526941
- Verify job: 105028788874
- Resolved proof: 612c7278ef785e649b3b9eb137b15e2c3e861e2d
- Original solution SHA256: 7f721731a92f63e9299fd5b63ebcb991e8a992f6089c0d3a40298543c8ac2bee
- Compiler output time: 2026-09-17T00:27:13Z
- Toolchain restored: Lean4.30.0 / unchanged committed Mathlib pin

The actual errors were confined to the evaluation and degree helpers:

```text
_verified/packets/moment_small_face_witnesses/driver.lean:11:57: error: unsolved goals
ι : Type u_1
a : ι → ℝ
S : Finset ι
t : ℝ
⊢ Polynomial.eval t (∏ s ∈ S, (Polynomial.X - Polynomial.C (a s)) ^ 2) = ∏ s ∈ S, (t - a s) ^ 2

_verified/packets/moment_small_face_witnesses/driver.lean:40:6: error: Type mismatch
  Polynomial.natDegree_prod_of_monic S (fun s => (Polynomial.X - Polynomial.C (a s)) ^ 2) fun s x =>
    Polynomial.Monic.pow (Polynomial.monic_X_sub_C (a s)) 2
has type
  (∏ i ∈ S, (Polynomial.X - Polynomial.C (a i)) ^ 2).natDegree =
    ∑ i ∈ S, ((Polynomial.X - Polynomial.C (a i)) ^ 2).natDegree
but is expected to have type
  (squareRoots a S).natDegree = ∑ s ∈ S, ?m.22
```

At the committed Mathlib pin, Polynomial.eval_prod is not tagged simp. The
repair invokes it explicitly. The degree helper now unfolds the product with
an explicit Polynomial ℝ type before rewriting by the same monic degree lemma.
The exact two-site diff and the complete original source are preserved beside
this record. All theorem statements, hypotheses, problem.json and explanation.md
are BYTE-IDENTICAL. The main witness construction is unchanged. Both versions
have210 lines; corrected source SHA256:
95341bb2cfb6aff23e8ba0f5017b6b894818330aca4c1c97b16946535b4c50a0.

The first run printed standard-only axioms for average_split and centered_eval.
It printed sorryAx for the failed degree helper and dependent final declarations
because Lean recovered from compilation errors. Those declarations were NOT
verified. No proof admission occurs in the original source. Harmless push_neg
deprecation and unnecessary-sequence warnings are retained, not silenced.

The gate job succeeded, verification failed, and verified-packet upload and
publication were SKIPPED. No target registration, proof submission, acceptance
or authenticated platform verdict resulted. Thus a corrected final attempt
does not duplicate a pending platform submission.

The first resolved-request artifact10474838833 was downloaded. Its archive hash
was independently recomputed as
ad2b2faa7a8180732c16d24e106da2758a9b533e7b0023c36d386604bed7b9ef.
The exact extracted resolved.json is preserved as first-resolved-request.json.
The complete corrected-source arithmetic/signature test and a fresh isolated
replay pass, with byte-identical report and fixture. This is supporting evidence,
not local Lean compilation. No local compiler is available; the next check is
one corrected final comment gate, not a new workflow or changed mathematical target.
