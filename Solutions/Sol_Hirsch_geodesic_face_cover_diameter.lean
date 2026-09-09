import Solutions.PolynomialGeodesicFaceCover

open scoped RealInnerProductSpace BigOperators
open Set Hirsch

noncomputable section

/-- If every parent vertex lies in at least `q>0` selected extreme faces and
face `i` has intrinsic diameter budget `B i`, then connectivity plus shortest-
path incidence counting gives the explicit parent diameter budget
`(∑ i, (B i + 1)) / q - 1`. -/
theorem solution
    {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ (Finset.univ.filter (fun i => x ∈ F i)).card)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P ((∑ i, (B i + 1)) / q - 1) := by
  apply HirschFaceSplice.diamLE_of_face_cover d q hq P F B hF hFD hcover
  intro u hu v hv
  obtain ⟨L, w, hw0, hwL, hs⟩ := hconnect u hu v hv
  exact ⟨L, w, hw0, hwL, hs⟩

#print axioms solution
