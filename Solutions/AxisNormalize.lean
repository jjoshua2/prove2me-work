import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.AxisActive

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisNormalize

variable {d n : ℕ}

noncomputable def normA
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Fin n → EuclideanSpace ℝ (Fin d) :=
  fun i => (b i)⁻¹ • a i

lemma inner_neg_right (x y : EuclideanSpace ℝ (Fin d)) :
    ⟪x, -y⟫ = -⟪x, y⟫ := by simp

/-- For antipodal feasible spindle apices, every RHS is strictly positive.
If one endpoint is tight, the other evaluates to the negative RHS; equality
at both endpoints is excluded by the spindle XOR. -/
lemma rhs_pos
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hvneg : v = -u)
    (huP : u ∈ Hpoly a b) (hvP : v ∈ Hpoly a b)
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i) :
    ∀ i, 0 < b i := by
  intro i
  by_cases hU : ⟪a i, u⟫ = b i
  · have hVnot : ⟪a i, v⟫ ≠ b i := (hspindle i).1 hU
    have hVval : ⟪a i, v⟫ = -b i := by simp [hvneg, hU]
    have hnonneg : 0 ≤ b i := by
      have := hvP i
      rw [hVval] at this
      linarith
    exact lt_of_le_of_ne hnonneg (by
      intro hb0
      apply hVnot
      rw [hVval]
      linarith)
  · have hV : ⟪a i, v⟫ = b i := by
      by_contra hVnot
      exact hU ((hspindle i).2 hVnot)
    have hUval : ⟪a i, u⟫ = -b i := by
      have h := congrArg (fun z : ℝ => -z) hV
      simpa [hvneg] using h
    have hnonneg : 0 ≤ b i := by
      have := huP i
      rw [hUval] at this
      linarith
    exact lt_of_le_of_ne hnonneg (by
      intro hb0
      apply hU
      rw [hUval]
      linarith)

lemma norm_inner
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪normA a b i, x⟫ = (b i)⁻¹ * ⟪a i, x⟫ := by
  simp [normA, inner_smul_left]

lemma norm_tight_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : ∀ i, 0 < b i) (i : Fin n) (x : EuclideanSpace ℝ (Fin d)) :
    ⟪normA a b i, x⟫ = 1 ↔ ⟪a i, x⟫ = b i := by
  rw [norm_inner]
  constructor
  · intro h
    have hne : b i ≠ 0 := (hb i).ne'
    calc
      ⟪a i, x⟫ = b i * ((b i)⁻¹ * ⟪a i, x⟫) := by field_simp [hne]
      _ = b i := by rw [h, mul_one]
  · intro h
    rw [h]
    field_simp [(hb i).ne']

lemma hpoly_norm
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : ∀ i, 0 < b i) :
    Hpoly (normA a b) (fun _ => (1 : ℝ)) = Hpoly a b := by
  ext x
  constructor
  · intro hx i
    have hi := hx i
    rw [norm_inner] at hi
    have hpos := hb i
    have hmul := mul_le_mul_of_nonneg_left hi hpos.le
    have hne : b i ≠ 0 := hpos.ne'
    have hcancel : b i * ((b i)⁻¹ * ⟪a i, x⟫) = ⟪a i, x⟫ := by
      field_simp [hne]
    simpa [hcancel] using hmul
  · intro hx i
    rw [norm_inner]
    have hpos := hb i
    have hmul := mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.2 hpos.le)
    have hne : b i ≠ 0 := hpos.ne'
    have hcancel : (b i)⁻¹ * b i = 1 := inv_mul_cancel₀ hne
    simpa [hcancel] using hmul

lemma norm_spindle
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hb : ∀ i, 0 < b i)
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i) :
    ∀ i, (⟪normA a b i, u⟫ = 1) ↔ ⟪normA a b i, v⟫ ≠ 1 := by
  intro i
  rw [norm_tight_iff a b hb i u]
  constructor
  · intro hU hVnorm
    exact (hspindle i).1 hU ((norm_tight_iff a b hb i v).1 hVnorm)
  · intro hVnorm
    apply (hspindle i).2
    intro hV
    exact hVnorm ((norm_tight_iff a b hb i v).2 hV)

lemma norm_endpoint_values
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hvneg : v = -u)
    (hb : ∀ i, 0 < b i)
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i) :
    ∀ i,
      (⟪normA a b i, u⟫ = 1 ∧ ⟪normA a b i, v⟫ = -1) ∨
      (⟪normA a b i, u⟫ = -1 ∧ ⟪normA a b i, v⟫ = 1) := by
  intro i
  by_cases hU : ⟪a i, u⟫ = b i
  · left
    constructor
    · exact (norm_tight_iff a b hb i u).2 hU
    · have h := inner_neg_right (normA a b i) u
      rw [← hvneg] at h
      rw [(norm_tight_iff a b hb i u).2 hU] at h
      exact h
  · right
    have hV : ⟪a i, v⟫ = b i := by
      by_contra hVnot
      exact hU ((hspindle i).2 hVnot)
    constructor
    · have h := inner_neg_right (normA a b i) u
      rw [← hvneg] at h
      rw [(norm_tight_iff a b hb i v).2 hV] at h
      linarith
    · exact (norm_tight_iff a b hb i v).2 hV

lemma norm_extreme_zero
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hb : ∀ i, 0 < b i)
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪normA a b i, x⟫ = 1 → ⟪normA a b i, y⟫ = 0) → y = 0 := by
  intro y hy
  apply HirschAxisActive.extreme_tight_orthogonal hx
  intro i hi
  have hti : ⟪normA a b i, x⟫ = 1 := (norm_tight_iff a b hb i x).2 hi
  have hz := hy i hti
  rw [norm_inner] at hz
  have hinv : (b i)⁻¹ ≠ 0 := inv_ne_zero (hb i).ne'
  exact (mul_eq_zero.mp hz).resolve_left hinv

/-- In positive ambient dimension every extreme point of a finite H-polytope
has at least one tight row. -/
lemma extreme_has_tight
    (hd : 0 < d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ i, ⟪a i, x⟫ = b i := by
  by_contra h
  push Not at h
  let j : Fin d := ⟨0, hd⟩
  let y : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single j (1 : ℝ)
  have hy : y = 0 := HirschAxisActive.extreme_tight_orthogonal hx (by
    intro i hi
    exact False.elim (h i hi))
  have hj := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z j) hy
  simp [y, j] at hj

end HirschAxisNormalize
