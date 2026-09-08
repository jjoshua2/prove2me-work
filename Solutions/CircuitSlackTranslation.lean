import Solutions.CircuitIrredundantModel

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Linear row-evaluation map.  Under boundedness of a nonempty H-polytope this
is injective; its range is the slack-direction space. -/
def rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) :=
  { toFun := fun g i => ⟪a i, g⟫
    map_add' := by
      intro x y
      funext i
      simp
    map_smul' := by
      intro c x
      funext i
      simp }

/-- Slack coordinates for an H-presentation. -/
def slack {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Fin n → ℝ :=
  fun i => b i - ⟪a i, x⟫

/-- Support-minimal nonzero vector inside a fixed linear subspace.  This is the
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

/-- Natura-style maximal elementary augmentation in slack coordinates.  The
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

theorem circuitRowSupport_eq_support_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) :
    circuitRowSupport a g = Function.support (rowMap a g) := by
  ext i
  rfl

theorem slack_nonneg_iff_mem_Hpoly {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    (∀ i, 0 ≤ slack a b x i) ↔ x ∈ Hpoly a b := by
  constructor
  · intro h i
    have hi := h i
    dsimp [slack] at hi
    linarith
  · intro h i
    have hi := h i
    dsimp [slack]
    linarith

theorem slack_mem_SlackPoly_iff {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slack a b x ∈ SlackPoly a b ↔ x ∈ Hpoly a b := by
  constructor
  · intro h
    exact (slack_nonneg_iff_mem_Hpoly a b x).mp h.2
  · intro hx
    refine ⟨⟨x, rfl⟩, ?_⟩
    exact (slack_nonneg_iff_mem_Hpoly a b x).mpr hx

theorem slack_sub_slack_eq_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    slack a b x - slack a b y = rowMap a (y - x) := by
  funext i
  simp only [Pi.sub_apply, slack, rowMap, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_right]
  ring

theorem slack_line {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    slack a b (x + t • (y - x)) =
      slack a b x + t • (slack a b y - slack a b x) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, slack,
    inner_add_right, inner_smul_right, inner_sub_right]
  ring

theorem slack_injective_of_rowMap_injective {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a)) :
    Function.Injective (slack a b) := by
  intro x y hxy
  apply hinj
  funext i
  have hi := congrFun hxy i
  simp only [slack] at hi
  change ⟪a i, x⟫ = ⟪a i, y⟫
  linarith

theorem isRowCircuit_iff_elementary_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (rowMap a))
    (g : EuclideanSpace ℝ (Fin d)) :
    IsRowCircuit a g ↔
      IsElementaryIn (LinearMap.range (rowMap a)) (rowMap a g) := by
  constructor
  · rintro ⟨hg0, hmin⟩
    refine ⟨?_, ⟨g, rfl⟩, ?_⟩
    · intro hz
      apply hg0
      apply hinj
      simpa using hz
    · intro w hw0 hwRange hsub
      rcases hwRange with ⟨h, rfl⟩
      have hh0 : h ≠ 0 := by
        intro hh
        subst h
        simp at hw0
      have hsub' : circuitRowSupport a h ⊆ circuitRowSupport a g := by
        simpa [circuitRowSupport_eq_support_rowMap] using hsub
      have hout := hmin h hh0 hsub'
      simpa [circuitRowSupport_eq_support_rowMap] using hout
  · rintro ⟨hmap0, _hRange, hmin⟩
    refine ⟨?_, ?_⟩
    · intro hg0
      subst g
      exact hmap0 (by simp)
    · intro h hh0 hsub
      have hmh0 : rowMap a h ≠ 0 := by
        intro hz
        apply hh0
        apply hinj
        simpa using hz
      have hsub' : Function.support (rowMap a h) ⊆
          Function.support (rowMap a g) := by
        simpa [circuitRowSupport_eq_support_rowMap] using hsub
      have hout := hmin (rowMap a h) hmh0 ⟨h, rfl⟩ hsub'
      simpa [circuitRowSupport_eq_support_rowMap] using hout

theorem rowCircuitStep_iff_slackCircuitStep {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (x y : EuclideanSpace ℝ (Fin d)) :
    RowCircuitStep a b x y ↔
      SlackCircuitStep a b (slack a b x) (slack a b y) := by
  constructor
  · rintro ⟨hx, hy, hcirc, hmax⟩
    refine ⟨(slack_mem_SlackPoly_iff a b x).mpr hx,
      (slack_mem_SlackPoly_iff a b y).mpr hy, ?_, ?_⟩
    · rw [slack_sub_slack_eq_rowMap]
      exact (isRowCircuit_iff_elementary_rowMap a hinj (y - x)).mp hcirc
    · intro t ht hmem
      have hline := slack_line a b x y t
      rw [← hline] at hmem
      exact hmax t ht ((slack_mem_SlackPoly_iff a b _).mp hmem)
  · rintro ⟨hx, hy, hcirc, hmax⟩
    refine ⟨(slack_mem_SlackPoly_iff a b x).mp hx,
      (slack_mem_SlackPoly_iff a b y).mp hy, ?_, ?_⟩
    · rw [slack_sub_slack_eq_rowMap] at hcirc
      exact (isRowCircuit_iff_elementary_rowMap a hinj (y - x)).mpr hcirc
    · intro t ht hfeas
      apply hmax t ht
      have hmem := (slack_mem_SlackPoly_iff a b _).mpr hfeas
      rw [slack_line a b x y t] at hmem
      exact hmem

theorem rowCircuitWalk_to_slackCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    RowCircuitWalk a b L u v →
      SlackCircuitWalk a b L (slack a b u) (slack a b v) := by
  rintro ⟨w, hw0, hwL, hfeas, hstep⟩
  refine ⟨fun j => slack a b (w j), ?_, ?_, ?_, ?_⟩
  · simpa [hw0]
  · simpa [hwL]
  · intro j hj
    exact (slack_mem_SlackPoly_iff a b (w j)).mpr (hfeas j hj)
  · intro j hj
    rcases hstep j hj with hstay | hmove
    · left
      simpa [hstay]
    · right
      exact (rowCircuitStep_iff_slackCircuitStep a b hinj (w j) (w (j + 1))).mp hmove

#print axioms rowCircuitStep_iff_slackCircuitStep
#print axioms rowCircuitWalk_to_slackCircuitWalk

end HirschCircuit
