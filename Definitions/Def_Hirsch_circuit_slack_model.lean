import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
open scoped RealInnerProductSpace

namespace HirschCircuit

/-- Linear row-evaluation map. Under boundedness of a nonempty H-polytope this
is injective; its range is the slack-direction space. -/
noncomputable def rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) :=
  { toFun := fun g i => ⟪a i, g⟫
    map_add' := by
      intro x y
      funext i
      simp only [inner_add_right, Pi.add_apply]
    map_smul' := by
      intro c x
      funext i
      simp [inner_smul_right, smul_eq_mul] }

/-- Slack coordinates for an H-presentation. -/
noncomputable def slack {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Fin n → ℝ :=
  fun i => b i - ⟪a i, x⟫

/-- Support-minimal nonzero vector inside a fixed linear subspace. This is the
coordinate-free form of Natura's elementary vectors in a matrix kernel. -/
def IsElementaryIn {n : ℕ} (K : Submodule ℝ (Fin n → ℝ))
    (z : Fin n → ℝ) : Prop :=
  z ≠ 0 ∧ z ∈ K ∧
    ∀ w : Fin n → ℝ, w ≠ 0 → w ∈ K →
      Function.support w ⊆ Function.support z →
      Function.support z ⊆ Function.support w

/-- The nonnegative affine slack image of an H-polytope. -/
def SlackPoly {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {s | (∃ x : EuclideanSpace ℝ (Fin d), s = slack a b x) ∧
    ∀ i, 0 ≤ s i}

/-- Natura-style maximal elementary augmentation in slack coordinates. The
support-minimal direction is written with the opposite sign `sx - sy`; support
minimality is sign invariant, and this choice makes it literally `rowMap (y-x)`. -/
def SlackCircuitStep {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (sx sy : Fin n → ℝ) : Prop :=
  sx ∈ SlackPoly a b ∧ sy ∈ SlackPoly a b ∧
    IsElementaryIn (LinearMap.range (rowMap a)) (sx - sy) ∧
    ∀ t : ℝ, 1 < t → sx + t • (sy - sx) ∉ SlackPoly a b

/-- Padded slack-coordinate circuit walk, directly parallel to `RowCircuitWalk`. -/
def SlackCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (L : ℕ) (su sv : Fin n → ℝ) : Prop :=
  ∃ s : ℕ → (Fin n → ℝ),
    s 0 = su ∧ s L = sv ∧
    (∀ j ≤ L, s j ∈ SlackPoly a b) ∧
    ∀ j < L, s j = s (j + 1) ∨ SlackCircuitStep a b (s j) (s (j + 1))

end HirschCircuit
