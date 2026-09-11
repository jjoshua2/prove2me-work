import Mathlib
import Solutions.PolynomialCircuitCarrierDefect
import Solutions.PolynomialFacePreservingCheckpoints

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

/-! Candidate source; not yet compiled. No platform submission is included.

Reuse the carrier-rank and active-defect declarations already present on the
research branch; do not redeclare them. Only carrier closedness and the
conditional routing specialization are new in this module.
-/
namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Closedness of the common carrier in a compact H-polytope. -/
theorem commonFace_isClosed_of_compact_parent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (hP : IsCompact (Hpoly a b)) :
    IsClosed (commonFace a b x y) := by
  have heq : commonFace a b x y = Hpoly a b ∩
      ⋂ i : Fin n, ⋂ (_ : i ∈ commonSourceRows a b x y),
        {z : EuclideanSpace ℝ (Fin d) | ⟪a i, z⟫ = b i} := by
    ext z
    simp [commonFace]
  rw [heq]
  apply hP.isClosed.inter
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro _
  exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

/-- Any feasible checkpoint sequence with vertex endpoints can be converted
to an edge/stay route when the intrinsic diameters of its common carriers are
supplied. Intermediate checkpoints do not need to be vertices. The output
need not visit them. This specializes the checked feasible-face-cover theorem.

Indexing by `Fin L` charges each occurrence once. For repeated carriers the
underlying face-cover theorem allows indexing by the set of distinct carriers
and charging each distinct face once instead. -/
theorem route_of_feasible_commonFace_carrier_budgets
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hP : IsCompact (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (B : Fin L → ℕ)
    (hB : ∀ i : Fin L,
      DiamLE (commonFace a b (w i.val) (w (i.val + 1))) (B i)) :
    HirschRegionRoute.Route (Adj (Hpoly a b)) (∑ i, B i) (w 0) (w L) := by
  let F : Fin L → Set (EuclideanSpace ℝ (Fin d)) :=
    fun i => commonFace a b (w i.val) (w (i.val + 1))
  apply HirschRegionRoute.route_of_feasible_face_covered_sequence
    (Hpoly a b) F B hP
    (fun i => commonFace_isExtreme a b (w i.val) (w (i.val + 1)))
    (fun i => commonFace_isClosed_of_compact_parent a b (w i.val) (w (i.val + 1)) hP)
    hB w L hfeas h0 hL
  intro k hk
  refine ⟨⟨k, hk⟩, ?_, ?_⟩
  · exact commonFace_u_mem a b (w k) (w (k + 1)) (hfeas k (Nat.le_of_lt hk))
  · exact commonFace_x_mem a b (w k) (w (k + 1)) (hfeas (k + 1) (by omega))

#print axioms commonFace_isClosed_of_compact_parent
#print axioms route_of_feasible_commonFace_carrier_budgets

end HirschPolynomialAccess
