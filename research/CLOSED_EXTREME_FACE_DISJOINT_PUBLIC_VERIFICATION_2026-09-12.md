# Standalone closed extreme-face disjointness verification

Date: 2026-09-12.

Frozen theorem head: `fb1594e865b723ea2e6bf63baf46beeba7025027`.

Hosted verification:
- run `34699009349`
- job `103567342255`
- artifact `10299840991`
- artifact digest `sha256:636e6debba1e09e8c1add30e864c8fb5876cb2fff2bc38f3ccf8d5754c904e36`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The first and only hosted gate built `Solutions.PolynomialClosedExtremeFacesDisjointPublic`, ran the standalone source directly through Lean, and transitive-axiom-audited
`Hirsch.closed_extreme_faces_disjoint_of_no_shared_parent_extreme`.

Its axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`; the strict checker reports: `Axiom audit passed: 1 required declarations; 1 reports checked; only standard logical axioms.`

The theorem source imports only Mathlib and `Mathlib.Analysis.Convex.KreinMilman`; it imports no private `Solutions.*` module. Formal content: two closed extreme subsets of a compact parent that share no parent extreme point are disjoint. The proof is direct: a common point makes their intersection a nonempty compact extreme subset of the parent; Krein–Milman supplies an extreme point of that intersection, which is also an extreme point of the parent and lies in both faces.

This is suitable for a separate credentialed Prove2Me registration/proof gate. No credentials or Prove2Me mutation were used in this verification run. The one-shot verifier is removed before integration.
