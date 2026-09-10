import Solutions.PolynomialHpolyPointedClipping

/-! Geometric pointedness for finite H-polyhedra.

For a nonempty finite H-polyhedron, containing a nontrivial affine line is
equivalent to the row normals having a nonzero common-kernel direction.  This
turns the algebraic `hkernel` assumption used by the canonical far-cap theorem
into the usual geometric pointedness hypothesis. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- A set contains a nontrivial affine line if some point can be translated by
all real multiples of a nonzero direction while staying in the set. -/
def ContainsAffineLine (Q : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ x r : EuclideanSpace ℝ (Fin d), r ≠ 0 ∧ ∀ t : ℝ, x + t • r ∈ Q

/-- The direction of an affine line contained in an H-polyhedron is annihilated
by every defining row normal. -/
lemma common_kernel_of_affine_line
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x r : EuclideanSpace ℝ (Fin d)}
    (hr0 : r ≠ 0) (hline : ∀ t : ℝ, x + t • r ∈ Hpoly a b) :
    r ≠ 0 ∧ ∀ i, ⟪a i, r⟫ = 0 := by
  refine ⟨hr0, ?_⟩
  intro i
  by_contra hir
  let t : ℝ := (b i - ⟪a i, x⟫ + 1) / ⟪a i, r⟫
  have hineq := hline t i
  change ⟪a i, x + t • r⟫ ≤ b i at hineq
  rw [inner_add_right, inner_smul_right] at hineq
  have hmul : t * ⟪a i, r⟫ = b i - ⟪a i, x⟫ + 1 := by
    dsimp [t]
    exact div_mul_cancel₀ _ hir
  linarith

/-- A nonzero common-kernel direction produces a full affine line through every
feasible base point. -/
lemma affine_line_of_common_kernel
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x r : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Hpoly a b) (hr0 : r ≠ 0)
    (hr : ∀ i, ⟪a i, r⟫ = 0) :
    ContainsAffineLine (Hpoly a b) := by
  refine ⟨x, r, hr0, ?_⟩
  intro t i
  change ⟪a i, x + t • r⟫ ≤ b i
  rw [inner_add_right, inner_smul_right, hr i, mul_zero, add_zero]
  exact hx i

/-- For a nonempty finite H-polyhedron, containing an affine line is exactly the
existence of a nonzero direction in the common kernel of all row normals. -/
theorem containsAffineLine_iff_exists_common_kernel
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) :
    ContainsAffineLine (Hpoly a b) ↔
      ∃ r : EuclideanSpace ℝ (Fin d), r ≠ 0 ∧ ∀ i, ⟪a i, r⟫ = 0 := by
  constructor
  · rintro ⟨x, r, hr0, hline⟩
    exact ⟨r, common_kernel_of_affine_line a b hr0 hline⟩
  · rintro ⟨r, hr0, hr⟩
    obtain ⟨x, hx⟩ := hne
    exact affine_line_of_common_kernel a b hx hr0 hr

/-- Usual geometric pointedness (`Q` contains no affine line) is equivalent to
the common-row-kernel condition used by the canonical cap construction. -/
theorem no_affine_line_iff_no_common_kernel
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) :
    (¬ ContainsAffineLine (Hpoly a b)) ↔
      ∀ r : EuclideanSpace ℝ (Fin d), (∀ i, ⟪a i, r⟫ = 0) → r = 0 := by
  constructor
  · intro hpointed r hr
    by_contra hr0
    exact hpointed ((containsAffineLine_iff_exists_common_kernel a b hne).2
      ⟨r, hr0, hr⟩)
  · intro hkernel hline
    obtain ⟨r, hr0, hr⟩ :=
      (containsAffineLine_iff_exists_common_kernel a b hne).1 hline
    exact hr0 (hkernel r hr)

#print axioms common_kernel_of_affine_line
#print axioms affine_line_of_common_kernel
#print axioms containsAffineLine_iff_exists_common_kernel
#print axioms no_affine_line_iff_no_common_kernel

end HirschHpolyCap
