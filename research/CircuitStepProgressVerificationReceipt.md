# Maximal circuit-step carrier progress — verification receipt

Date: 2026-09-10/11 (America/New_York / UTC boundary).

## Verified source

The mathematical file `Solutions/PolynomialCircuitStepProgress.lean` was
verified at commit `4ce691860d983c164f3088f6e69bd875d25d2d55` on the temporary verification
branch. The first gate exposed only an incorrect use of the already-negated
existential hypothesis in the blocking-row proof; the repaired source uses the
resulting nonpositive directional inequality directly.

## Kernel gate

- GitHub Actions run: `34551429080`
- job: `103114973158`
- artifact: `10180991168` (`circuit-step-progress-audit`)
- artifact ZIP SHA-256 reported by Actions:
  `a41327a570b8f4f0c0d75c811bf06ba5a8f40d3c86a76cd776df9809e51f8aa2`
- Lean: `4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The build completed successfully and all five requested declarations produced
fresh transitive axiom reports containing only `propext`, `Classical.choice`,
and `Quot.sound`:

1. `HirschCircuitLocalization.rowCircuitStep_exists_target_blocking_row`
2. `HirschCircuitLocalization.commonDirection_target_self_lt_of_rowCircuitStep`
3. `HirschCircuitLocalization.rowCircuitStep_target_commonFaceDim_lt`
4. `HirschCircuitLocalization.rowCircuitStep_commonFaceDim_source_bound`
5. `HirschCircuitLocalization.rowCircuitStep_target_commonFaceDim_progress`

No `sorryAx` or other nonstandard proof axiom occurs.

## Mathematical content

For every maximal feasible row-circuit step `x -> y`:

- some nonzero row is tight at `y` and has strictly positive derivative along
  `y-x`;
- consequently the self common-direction space at `y` is a strict subspace of
  the common-direction carrier of `x,y`;
- hence `commonFaceDim a b y y < commonFaceDim a b x y`.

Combining that strict drop with the separately kernel-checked nonvertex circuit
checkpoint-localization theorem yields, whenever the same H-polyhedron has a
reference extreme vertex `z`, the sharper maximal-step inequalities

```text
commonFaceDim a b x y + d <= n + commonFaceDim a b x x
commonFaceDim a b y y + d + 1 <= n + commonFaceDim a b x x
```

The endpoints `x,y` themselves need not be vertices.

These are structural progress lemmas only. They do not supply graph routes or
solve the remaining `d >= 4` circuit-to-edge refinement theorem. No Prove2Me
publication or acceptance is claimed by this receipt.
