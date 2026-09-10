import Solutions.PolynomialUnboundedCutHpoly

/-! Algebraic recession lemmas for the canonical far-cap functional of a finite
H-polyhedron. These are the finite-row ingredients needed before formalizing
compact far-cap existence. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- Directions which preserve every defining halfspace when followed forward. -/
def RecessionDir (a : Fin n → EuclideanSpace ℝ (Fin d))
    (r : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i, ⟪a i, r⟫ ≤ 0

/-- The canonical cap normal: the negative sum of all H-row normals. -/
def capNormal (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  -∑ i, a i

/-- A recession direction really does generate a feasible forward ray from
any feasible H-polyhedron point. -/
lemma ray_mem_hpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x r : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Hpoly a b) (hr : RecessionDir a r) {t : ℝ} (ht : 0 ≤ t) :
    x + t • r ∈ Hpoly a b := by
  intro i
  change ⟪a i, x + t • r⟫ ≤ b i
  rw [inner_add_right, inner_smul_right]
  have htr : t * ⟪a i, r⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (hr i)
  linarith [hx i]

/-- If a direction and its opposite are both recession directions, every H-row
normal annihilates that direction. -/
lemma recession_and_neg_iff_common_kernel
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (r : EuclideanSpace ℝ (Fin d)) :
    RecessionDir a r ∧ RecessionDir a (-r) ↔ ∀ i, ⟪a i, r⟫ = 0 := by
  constructor
  · rintro ⟨hr, hneg⟩ i
    have h1 := hr i
    have h2 := hneg i
    rw [inner_neg_right] at h2
    linarith
  · intro h
    constructor
    · intro i
      rw [h i]
    · intro i
      rw [inner_neg_right, h i, neg_zero]

/-- The canonical cap functional is nondecreasing along every recession ray. -/
lemma capNormal_nonneg_on_recession
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    {r : EuclideanSpace ℝ (Fin d)} (hr : RecessionDir a r) :
    0 ≤ ⟪capNormal a, r⟫ := by
  have hsum : ∑ i, ⟪a i, r⟫ ≤ 0 := by
    simpa using Finset.sum_nonpos fun i _ => hr i
  have hsumInner : ⟪∑ i, a i, r⟫ = ∑ i, ⟪a i, r⟫ := by
    simpa using (sum_inner (Finset.univ : Finset (Fin n)) a r)
  rw [capNormal, inner_neg_left, hsumInner]
  linarith

/-- Under the no-line/common-kernel condition, the canonical cap functional is
strictly positive on every nonzero recession direction. -/
lemma capNormal_pos_on_nonzero_recession
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, r⟫ = 0) → r = 0)
    {r : EuclideanSpace ℝ (Fin d)} (hr : RecessionDir a r) (hr0 : r ≠ 0) :
    0 < ⟪capNormal a, r⟫ := by
  have hex : ∃ i, ⟪a i, r⟫ < 0 := by
    by_contra h
    push_neg at h
    have hz : ∀ i, ⟪a i, r⟫ = 0 := fun i => le_antisymm (hr i) (h i)
    exact hr0 (hkernel r hz)
  obtain ⟨i, hi⟩ := hex
  have hsum_le : ∑ j, ⟪a j, r⟫ ≤ 0 := by
    simpa using Finset.sum_nonpos fun j _ => hr j
  have hsum_ne : (∑ j, ⟪a j, r⟫) ≠ 0 := by
    intro hzero
    have hall : ∀ j ∈ (Finset.univ : Finset (Fin n)), ⟪a j, r⟫ = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hr j)).mp (by simpa using hzero)
    exact hi.ne (hall i (Finset.mem_univ i))
  have hsum : ∑ j, ⟪a j, r⟫ < 0 := lt_of_le_of_ne hsum_le hsum_ne
  have hsumInner : ⟪∑ j, a j, r⟫ = ∑ j, ⟪a j, r⟫ := by
    simpa using (sum_inner (Finset.univ : Finset (Fin n)) a r)
  rw [capNormal, inner_neg_left, hsumInner]
  linarith

/-- The no-common-kernel condition is equivalent to excluding nonzero line
directions from the finite halfspace recession system. -/
lemma no_common_kernel_iff_no_recession_line
    (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∀ r : EuclideanSpace ℝ (Fin d), (∀ i, ⟪a i, r⟫ = 0) → r = 0) ↔
      ∀ r : EuclideanSpace ℝ (Fin d),
        RecessionDir a r → RecessionDir a (-r) → r = 0 := by
  constructor
  · intro hk r hr hn
    exact hk r ((recession_and_neg_iff_common_kernel a r).mp ⟨hr, hn⟩)
  · intro h r hz
    have hp := (recession_and_neg_iff_common_kernel a r).mpr hz
    exact h r hp.1 hp.2

#print axioms ray_mem_hpoly
#print axioms recession_and_neg_iff_common_kernel
#print axioms capNormal_nonneg_on_recession
#print axioms capNormal_pos_on_nonzero_recession
#print axioms no_common_kernel_iff_no_recession_line

end HirschHpolyCap
