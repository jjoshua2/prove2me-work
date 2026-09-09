import Solutions.PolynomialRepairNetworkCuts

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Public wrapper for the polyhedral repair-network cut theorem, with the
local Route and RegionCutCondition vocabulary expanded from its type. -/
theorem solution {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ k, IsExtreme ℝ P (F k)) (hD : ∀ k, DiamLE (F k) (B k))
    (i j : ι)
    (hcut : ∀ A : Set ι, i ∈ A → j ∉ A →
      ∃ a ∈ A, ∃ b, b ∉ A ∧ ∃ z,
        z ∈ extremePoints ℝ P ∧ z ∈ F a ∧ z ∈ F b)
    (u v : EuclideanSpace ℝ (Fin d))
    (huP : u ∈ extremePoints ℝ P) (huF : u ∈ F i)
    (hvP : v ∈ extremePoints ℝ P) (hvF : v ∈ F j) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (∑ k, B k) = v ∧
      ∀ r < ∑ k, B k, q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by
  have hc : HirschRegionRoute.RegionCutCondition
      (fun k => extremePoints ℝ P ∩ F k) i j := by
    intro A hi hj
    obtain ⟨a, ha, b, hb, z, hzP, hza, hzb⟩ := hcut A hi hj
    exact ⟨a, ha, b, hb, z, ⟨hzP, hza⟩, ⟨hzP, hzb⟩⟩
  exact HirschRegionRoute.route_of_extreme_face_cut_condition
    P F B hF hD i j hc u v ⟨huP, huF⟩ ⟨hvP, hvF⟩

#print axioms solution
