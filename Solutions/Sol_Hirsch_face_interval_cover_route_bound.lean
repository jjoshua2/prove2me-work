import Solutions.PolynomialIntervalRegionRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public-facing wrapper with no local vocabulary in its theorem type.
Prove2Me registration and submission are intentionally deferred. -/
theorem solution {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ extremePoints ℝ P ∧ z ∈ F i ∧ z ∈ F j) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ j < ∑ i, B i, q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  exact HirschRegionRoute.route_of_face_interval_cover P F B hF hD
    s t w L hbound hverts hends hcover hportal

#print axioms solution
