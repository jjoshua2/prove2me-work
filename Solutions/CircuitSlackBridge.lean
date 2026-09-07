import Mathlib
import Definitions.Def_Hirsch_circuit_model
import Solutions.PolynomialVertexSpan

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschSlack

variable {d n : ℕ}

/-- Linear part of the slack map. The minus sign matters for feasibility. -/
def directionMap (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) where
  toFun g i := -⟪a i, g⟫
  map_add' := by intro x y; funext i; simp [inner_add_right]; ring
  map_smul' := by intro t x; funext i; simp [inner_smul_right]

/-- The actual slacks, in the ordinary finite function space. -/
def slack (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Fin n → ℝ :=
  b + directionMap a x

/-- A standard-form polyhedron specified by its direction subspace. -/
def standardSet (K : Submodule ℝ (Fin n → ℝ)) (b : Fin n → ℝ) :
    Set (Fin n → ℝ) := {s | s - b ∈ K ∧ ∀ i, 0 ≤ s i}

def support (g : Fin n → ℝ) : Set (Fin n) := {i | g i ≠ 0}

/-- Support-minimal nonzero vector of the direction subspace. -/
def Elementary (K : Submodule ℝ (Fin n → ℝ)) (g : Fin n → ℝ) : Prop :=
  g ∈ K ∧ g ≠ 0 ∧ ∀ h ∈ K, h ≠ 0 → support h ⊆ support g → support g ⊆ support h

/-- A maximal standard-form augmentation, normalized to scalar length one. -/
def StandardStep (K : Submodule ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    (x y : Fin n → ℝ) : Prop :=
  x ∈ standardSet K b ∧ y ∈ standardSet K b ∧ Elementary K (y - x) ∧
    ∀ t : ℝ, 1 < t → x + t • (y - x) ∉ standardSet K b

def StandardWalk (K : Submodule ℝ (Fin n → ℝ)) (b : Fin n → ℝ)
    (L : ℕ) (u v : Fin n → ℝ) : Prop :=
  ∃ w : ℕ → (Fin n → ℝ), w 0 = u ∧ w L = v ∧
    (∀ j ≤ L, w j ∈ standardSet K b) ∧
    ∀ j < L, w j = w (j + 1) ∨ StandardStep K b (w j) (w (j + 1))

lemma direction_injective_of_vertex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    Function.Injective (directionMap a) := by
  intro x y hxy
  have horth : ∀ i, ⟪a i, x - y⟫ = 0 := by
    intro i
    have hi : -⟪a i, x⟫ = -⟪a i, y⟫ := congrFun hxy i
    rw [inner_sub_right]
    linarith
  exact sub_eq_zero.mp (HirschPolynomialAccess.vertex_tight_rows_span_checked
    d n a b v hv (x - y) (fun i _ => horth i))

lemma slack_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (directionMap a)) :
    Function.Injective (slack a b) := by
  intro x y h
  apply hinj
  exact add_left_cancel h

lemma slack_mem_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slack a b x ∈ standardSet (directionMap a).range b ↔ x ∈ Hpoly a b := by
  constructor
  · intro hx i
    have hi := hx.2 i
    change 0 ≤ b i + -⟪a i, x⟫ at hi
    linarith
  · intro hx
    refine ⟨?_, ?_⟩
    · refine ⟨x, ?_⟩
      change directionMap a x = b + directionMap a x - b
      abel
    · intro i
      change 0 ≤ b i + -⟪a i, x⟫
      linarith [hx i]

lemma slack_surjOn
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Set.SurjOn (slack a b) (Hpoly a b) (standardSet (directionMap a).range b) := by
  intro s hs
  obtain ⟨x, hx⟩ := hs.1
  have hslack : slack a b x = s := by
    change b + directionMap a x = s
    rw [hx]
    abel
  exact ⟨x, (slack_mem_iff a b x).1 (hslack.symm ▸ hs), hslack⟩

lemma slack_image
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    slack a b '' Hpoly a b = standardSet (directionMap a).range b := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (slack_mem_iff a b x).2 hx
  · exact slack_surjOn a b

lemma slack_affine
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (α β : ℝ) (hab : α + β = 1) (x y : EuclideanSpace ℝ (Fin d)) :
    slack a b (α • x + β • y) = α • slack a b x + β • slack a b y := by
  funext i
  change b i + -⟪a i, α • x + β • y⟫ =
    α * (b i + -⟪a i, x⟫) + β * (b i + -⟪a i, y⟫)
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith [congrArg (fun t : ℝ => t * b i) hab]

lemma slack_sub
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    slack a b y - slack a b x = directionMap a (y - x) := by
  simp only [slack, map_sub]
  abel

lemma slack_line
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    slack a b (x + t • (y - x)) =
      slack a b x + t • (slack a b y - slack a b x) := by
  rw [slack_sub]
  simp only [slack, map_add, map_smul]
  abel

lemma support_direction
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (g : EuclideanSpace ℝ (Fin d)) :
    support (directionMap a g) = circuitRowSupport a g := by
  ext i
  change (-⟪a i, g⟫ ≠ 0) ↔ (⟪a i, g⟫ ≠ 0)
  exact neg_ne_zero

lemma elementary_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (directionMap a)) (g : EuclideanSpace ℝ (Fin d)) :
    Elementary (directionMap a).range (directionMap a g) ↔ IsRowCircuit a g := by
  constructor
  · rintro ⟨_, hne, hmin⟩
    refine ⟨?_, ?_⟩
    · intro hg
      exact hne (hg ▸ (directionMap a).map_zero)
    · intro h hh hsub
      have hh' : directionMap a h ≠ 0 := by
        intro heq
        apply hh
        apply hinj
        simpa only [map_zero] using heq
      have hm := hmin (directionMap a h) ⟨h, rfl⟩ hh'
        (by simpa only [support_direction] using hsub)
      simpa only [support_direction] using hm
  · rintro ⟨hne, hmin⟩
    refine ⟨⟨g, rfl⟩, ?_, ?_⟩
    · intro hg
      apply hne
      apply hinj
      simpa only [map_zero] using hg
    · intro h hh hne' hsub
      obtain ⟨k, rfl⟩ := hh
      have hk : k ≠ 0 := by
        intro hk
        exact hne' (hk ▸ (directionMap a).map_zero)
      simpa only [support_direction] using
        hmin k hk (by simpa only [support_direction] using hsub)

lemma step_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (directionMap a))
    (x y : EuclideanSpace ℝ (Fin d)) :
    StandardStep (directionMap a).range b (slack a b x) (slack a b y) ↔
      RowCircuitStep a b x y := by
  unfold StandardStep RowCircuitStep
  rw [slack_mem_iff, slack_mem_iff, slack_sub, elementary_iff a hinj]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor <;> intro h t ht
  · intro hx
    apply h t ht
    rw [← slack_sub a b x y, ← slack_line]
    exact (slack_mem_iff a b _).2 hx
  · intro hx
    apply h t ht
    apply (slack_mem_iff a b _).1
    simpa only [slack_line, slack_sub] using hx

/-- No length or maximality is lost in either direction. Intermediate
points remain feasible but are not asserted to be vertices. -/
theorem walk_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (directionMap a))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    StandardWalk (directionMap a).range b L (slack a b u) (slack a b v) ↔
      RowCircuitWalk a b L u v := by
  classical
  have hsinj := slack_injective a b hinj
  constructor
  · rintro ⟨w, hw0, hwL, hwmem, hwstep⟩
    have hex : ∀ j : ℕ, ∃ x : EuclideanSpace ℝ (Fin d),
        j ≤ L → slack a b x = w j := by
      intro j
      by_cases hj : j ≤ L
      · obtain ⟨x, _, hx⟩ := slack_surjOn a b (hwmem j hj)
        exact ⟨x, fun _ => hx⟩
      · exact ⟨u, fun h => False.elim (hj h)⟩
    choose p hp using hex
    refine ⟨p, hsinj ((hp 0 (Nat.zero_le L)).trans hw0),
      hsinj ((hp L le_rfl).trans hwL), ?_, ?_⟩
    · intro j hj
      apply (slack_mem_iff a b _).1
      rw [hp j hj]
      exact hwmem j hj
    · intro j hj
      have hj0 : j ≤ L := by omega
      have hj1 : j + 1 ≤ L := by omega
      rcases hwstep j hj with heq | he
      · exact Or.inl (hsinj ((hp j hj0).trans (heq.trans (hp (j + 1) hj1).symm)))
      · apply Or.inr
        apply (step_iff a b hinj _ _).1
        simpa only [hp j hj0, hp (j + 1) hj1] using he
  · rintro ⟨w, hw0, hwL, hwmem, hwstep⟩
    refine ⟨fun j => slack a b (w j), congrArg (slack a b) hw0,
      congrArg (slack a b) hwL, ?_, ?_⟩
    · intro j hj
      exact (slack_mem_iff a b _).2 (hwmem j hj)
    · intro j hj
      rcases hwstep j hj with heq | he
      · exact Or.inl (congrArg (slack a b) heq)
      · exact Or.inr ((step_iff a b hinj _ _).2 he)

/-- Slack coordinates preserve and reflect extreme points. -/
theorem extreme_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (directionMap a))
    (x : EuclideanSpace ℝ (Fin d)) :
    slack a b x ∈ extremePoints ℝ (standardSet (directionMap a).range b) ↔
      x ∈ extremePoints ℝ (Hpoly a b) := by
  have hsinj := slack_injective a b hinj
  constructor
  · intro hx
    refine ⟨(slack_mem_iff a b _).1 hx.1, ?_⟩
    intro p hp q hq hop
    apply hsinj
    apply hx.2 ((slack_mem_iff a b _).2 hp) ((slack_mem_iff a b _).2 hq)
    obtain ⟨α, β, hα, hβ, hab, hcomb⟩ := hop
    refine ⟨α, β, hα, hβ, hab, ?_⟩
    rw [← slack_affine a b α β hab, hcomb]
  · intro hx
    refine ⟨(slack_mem_iff a b _).2 hx.1, ?_⟩
    intro p hp q hq hop
    obtain ⟨px, hpx, hsp⟩ := slack_surjOn a b hp
    obtain ⟨qx, hqx, hsq⟩ := slack_surjOn a b hq
    have hop' : x ∈ openSegment ℝ px qx := by
      obtain ⟨α, β, hα, hβ, hab, hcomb⟩ := hop
      refine ⟨α, β, hα, hβ, hab, ?_⟩
      apply hsinj
      rw [slack_affine a b α β hab, hsp, hsq]
      exact hcomb
    have heq : px = x := hx.2 hpx hqx hop'
    exact hsp.symm.trans (congrArg (slack a b) heq)

#print axioms walk_iff
#print axioms extreme_iff

end HirschSlack
