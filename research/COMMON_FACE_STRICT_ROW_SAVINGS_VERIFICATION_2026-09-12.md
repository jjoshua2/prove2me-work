# Common-face strict-row savings verification

Date: 2026-09-12.

Frozen theorem head: `7896d786797b67ff3f60957fe6dea37a1ef7ebff`.

Hosted verification:
- run `34697559250`
- job `103563545980`
- artifact `10299296580`
- artifact digest `sha256:97b0a239a0c3e7eff33109cd1813fa92e9a0b0ab105519f993238ac7c386c0fb`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The first and only hosted gate built `Solutions.PolynomialCommonFaceStrictRowSavings`, ran the source file directly through Lean, and transitive-axiom-audited:
- `HirschCircuitLocalization.irredundant_commonFace_rows_disjoint_strict_rows`
- `HirschCircuitLocalization.commonFace_minExcess_add_strictRows_le`
- `HirschCircuitLocalization.commonFace_minExcess_le_of_strictRows_card`

All three reports contain only `propext`, `Classical.choice`, and `Quot.sound`; the strict checker reports: `Axiom audit passed: 3 required declarations; 3 reports checked; only standard logical axioms.` No `sorryAx` is accepted.

## Formal contribution

For a bounded `n`-row H-polyhedron in dimension `d` and two parent vertices `u,v`, let `M_min` be the minimum equivalent original-row presentation count of their common carrier and let `h` be its intrinsic common-face dimension. If `J` is any set of original describing rows which is strictly slack at every point of that carrier, then

`(M_min - h) + J.card <= n - d`.

Equivalently, if the strict rows account for all but `r` units of ambient row excess, then the common carrier has minimum-presentation excess at most `r`.

The proof uses the already-verified globally-minimal strictly-feasible irredundant carrier presentation. Every selected indispensable row has a feasible coordinate point where exactly that row is tight; mapping that witness to the ambient common face rules out selection of a row that is strict everywhere there. These excluded rows are disjoint both from the selected presentation rows and from the common-source rows that vanish on the carrier. Rank-nullity on the common-source row evaluation supplies the remaining `d-h` charge.

## Strategic role

This is the first theorem in the current target-cone line that turns unused/strict ambient rows into a quantitatively smaller recursive carrier resource rather than only counting support labels. The intended next application is to choose a shortest/chordless mixed repair-region path: nonneighboring used cut faces should then be disjoint, making their rows strict throughout an actual portal-pair carrier on the current cut face. In the maximum-support case this is expected to force every local carrier into the already-verified excess-at-most-three routing regime.

This result is an ordinary-edge resource input, not a global Polynomial Hirsch theorem. No Prove2Me credentials or mutation were used in this verification gate. The one-shot verifier is removed before integration.
