import Solutions.PolynomialFacePreservingCheckpoints

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public wrapper: one selector can round every feasible point of a compact
parent to a parent vertex while preserving membership in every supplied closed
extreme face, and it fixes vertices already present. -/
theorem solution
    {d : ℕ} {ι : Type*}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) :
    ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x ∈ P, r x ∈ extremePoints ℝ P) ∧
      (∀ x ∈ extremePoints ℝ P, r x = x) ∧
      (∀ i x, x ∈ F i → r x ∈ F i) := by
  exact HirschRegionRoute.face_preserving_vertex_selection P F hP hF hclosed

#print axioms solution
