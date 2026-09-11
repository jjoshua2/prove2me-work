# Excess-two normalized support geometry verification — 2026-09-10

Clean receipt for the normalized two-moment slice source verified on branch `chatgpt/excess-two-portals-kernel`.

- exact source commit: `51f4e7695428927bac8b072eeb1ccc2f1dc7861c`
- Lean: `v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Actions run: `34556417064`
- job: `103129930851`
- artifact: `10182735780`
- artifact digest: `sha256:43a4344f9f956f066c8cc72603f3539cd68cd31f2db092fbc56620d8d07b775b`

The gate compiled exactly:

- `Solutions.PolynomialExcessTwoMomentSlice`
- `Solutions.PolynomialExcessTwoPairVertices`
- `Solutions.PolynomialExcessTwoSupportFaces`

and freshly audited the following declarations:

- `HirschExcessTwo.zeroFace_isExtreme`
- `HirschExcessTwo.sum_eq_add_of_zero_off_pair`
- `HirschExcessTwo.pairPoint_mem`
- `HirschExcessTwo.eq_pairPoint_of_mem_of_zero_off_pair`
- `HirschExcessTwo.pairPoint_mem_extremePoints`
- `HirschExcessTwo.supportFace_isExtreme`

Every report contained only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or other transitive axiom occurred.

Mathematical content:

1. The normalized excess-two slack model is the nonnegative slice with total mass one and a single moment equation.
2. Every coordinate-zero face, and more generally every finite support carrier obtained by forcing all coordinates outside a set `S` to zero, is an extreme face.
3. For every low/high pair `t i < mu < t j`, the explicit two-supported `pairPoint t mu i j` is feasible and an extreme vertex.
4. Any feasible point supported only on that low/high pair is equal to the explicit pair point.
5. A pair point lies in every support carrier containing its two indices.

This is a source/kernel receipt only. It is not a Prove2Me publication and does not claim Polynomial Hirsch. The next local formal target is shared-index adjacency: a three-index support carrier with one low and two high indices (or the symmetric case) should equal the segment between the two corresponding pair vertices. That will turn the verified support-face geometry into a two-edge compatible portal construction.
