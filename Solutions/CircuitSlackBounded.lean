import Solutions.CircuitSlackTranslation

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- A nonempty bounded H-polytope has no nonzero direction annihilated by every
row.  Equivalently, its row-evaluation map is injective. -/
theorem rowMap_injective_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) :
    Function.Injective (rowMap a) := by
  intro p q hpq
  by_contra hpqne
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr hpqne
  have hnorm : 0 < ‖p - q‖ := norm_pos_iff.mpr hdiff
  have hker : rowMap a (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hline : ∀ t : ℝ, x + t • (p - q) ∈ Hpoly a b := by
    intro t i
    have hki : ⟪a i, p - q⟫ = 0 := by
      have hi := congrFun hker i
      simpa [rowMap] using hi
    have hxi := hx i
    simpa [inner_add_right, inner_smul_right, hki] using hxi
  obtain ⟨r, hr⟩ := hb.subset_closedBall x
  have hr0 : 0 ≤ r := Metric.nonneg_of_mem_closedBall (hr hx)
  let t : ℝ := (r + 1) / ‖p - q‖
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by linarith) hnorm
  have hball := Metric.mem_closedBall.mp (hr (hline t))
  have hdist : dist (x + t • (p - q)) x = r + 1 := by
    rw [dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp [ne_of_gt hnorm]
  rw [hdist] at hball
  linarith

#print axioms rowMap_injective_of_bounded

end HirschCircuit
