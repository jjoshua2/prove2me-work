# Full normalized excess-two slice verification — 2026-09-11

Mission: **The Polynomial Hirsch Conjecture**  
Repository: `jjoshua2/prove2me-work`  
Lean: **4.30.0**  
Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

## Kernel/source result

The normalized two-moment slice is now kernel-verified through complete vertex
classification and intrinsic graph diameter two.

Frozen proof source commit:

`e9b89ee3f02fbaed5c379e35ef1c824ab3b85186`

Verification gate:

- GitHub Actions run: `34605987684`
- standalone solution SHA-256:
  `45e96aecc53c63bfd394ebc11a2ee196b958534cd93fe1f648c281dad8072317`
- every audited declaration, including the flattened standalone `solution`,
  depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Formal results

For arbitrary `t : Fin n → ℝ` and `mu : ℝ`, define the normalized slice

```text
P(t,mu) = { s ≥ 0 : Σ s_i = 1, Σ t_i s_i = mu }.
```

There is no genericity assumption on the moments; repeated moments, empty
slices, singleton slices, and lower-dimensional cases are covered.

### Complete vertex classification

`HirschExcessTwo.momentSlice_extremePoints_iff` proves that every extreme point
is exactly one of:

1. an equal-moment singleton `e_k` with `t_k = mu`; or
2. a low/high pair point `p_ij` with `t_i < mu < t_j`.

The key reusable lemma is `extreme_eq_of_support_contained`: an extreme feasible
point equals every feasible point whose support is contained in its support.

### Missing singleton edges

The source proves exact support-face segment descriptions and hence actual graph
adjacency for:

- distinct equal-moment singleton vertices;
- any equal-moment singleton and any low/high pair vertex.

Combined with the previously verified shared-index pair adjacency, this closes
all vertex-type combinations.

### Support-preserving two-step routing

`HirschExcessTwo.momentSlice_two_step_route_preserving_zeros` proves that for
any two extreme points `x,y`, there is an extreme point `z` with

```text
x = z or Adj P x z,
z = y or Adj P z y,
```

and additionally

```text
x_r = 0 and y_r = 0  ->  z_r = 0.
```

Thus the intermediate vertex introduces no coordinate outside the union of the
endpoint supports.

Consequently:

- `HirschExcessTwo.momentSlice_diamLE_two` proves `DiamLE P 2`;
- `HirschExcessTwo.supportFace_diamLE_two` proves every coordinate support face
  has **intrinsic** graph diameter at most two using edges of that face.

## Independently flattened public proof

`scripts/build_excess_two_completion_standalone.py` flattens the complete fixed
source chain from `Mathlib` and `Definitions.Def_Hirsch_model` through the new
diameter theorem. The generated public-facing theorem has no custom
`momentSlice` definition in its type:

```lean
theorem solution {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) :
    Hirsch.DiamLE
      {s : EuclideanSpace ℝ (Fin n) |
        (∀ i, 0 ≤ s i) ∧
        (∑ i, s i) = 1 ∧
        (∑ i, t i * s i) = mu} 2 := by
  exact HirschExcessTwo.momentSlice_diamLE_two t mu
```

The generated source compiled independently and its axiom audit was clean.

## Exact finite evidence

The earlier dependency-free exact-rational regression packet remains separate
finite evidence, not part of the kernel proof. Its recorded PASS includes:

- 2,560 normalized models, 1,001 empty;
- 5,140 extreme-point certificates;
- 70,693 exact support-rank checks;
- 22,844 ordered vertex routes;
- 292,163 support-face route incidences;
- 23,210 exact convex decompositions;
- 18,070 explicit nonvertex midpoint certificates;
- 23 full-dimensional slack models with 176 exact forward/inverse roundtrips;
- negative controls: normalized 3-cube and 4-cube graph diameters exactly 3 and 4.

Receipt: `research/EXCESS_TWO_COMPLETION_EXACT_CHECKS_2026-09-11.json`.

## Scope boundary and next bridge

This is a theorem about the normalized **two-affine-equation** slice. It is not
by itself a theorem about arbitrary circuit carriers or arbitrary
H-polyhedra. In particular, small support or circuit status does not imply the
rank-two slice structure.

The next bridge to formalize is the standard slack normalization for bounded,
strictly feasible `d`-dimensional presentations with at most `d+2` rows. The
ordinary argument gives an affine equivalence to a normalized two-moment slice;
together with the presentation-independent row count from PR83, the useful
common-face interface is expected to be:

```text
coordinate dimension h and minimal irredundant strict row count M_min ≤ h+2
    ==> intrinsic graph diameter ≤ 2.
```

That normalization/transport bridge is not claimed formalized by this receipt.
The main Polynomial-Hirsch edge-refinement theorem therefore remains Open.
