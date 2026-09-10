import Mathlib
import Solutions.PolynomialGeodesicFaceCover

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschFaceSplice

/-- Weighted incidence counting on a shortest graph walk. A zero-weight face
needs no diameter bound, so it cannot hide a bound for the parent itself. -/
theorem shortest_weighted_face_cover_budget
    {ι : Type*} [Fintype ι]
    (d L q : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B weight : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, 0 < weight i → DiamLE (F i) (B i))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P)
    (hcover : ∀ j ≤ L, q ≤ ∑ i, if w j ∈ F i then weight i else 0) :
    q * (L + 1) ≤ ∑ i, weight i * (B i + 1) := by
  classical
  have hcount :
      (∑ j ∈ Finset.range (L + 1), ∑ i, if w j ∈ F i then weight i else 0) =
      ∑ i, weight i * ((Finset.range (L + 1)).filter (fun j => w j ∈ F i)).card := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : w j ∈ F i <;> simp [hj]
  calc
    q * (L + 1) = ∑ _j ∈ Finset.range (L + 1), q := by simp [Nat.mul_comm]
    _ ≤ ∑ j ∈ Finset.range (L + 1), ∑ i, if w j ∈ F i then weight i else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcover j (by have := Finset.mem_range.mp hj; omega)
    _ = ∑ i, weight i * ((Finset.range (L + 1)).filter (fun j => w j ∈ F i)).card := hcount
    _ ≤ ∑ i, weight i * (B i + 1) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : weight i = 0
      · simp [hi]
      · apply Nat.mul_le_mul_left
        exact shortest_face_visit_card_le d L (B i) P (F i) (hF i)
          (hFD i (Nat.pos_of_ne_zero hi)) u v w hw0 hwL hs hmin hverts

/-- Integer-weighted face covers give an explicit graph diameter certificate.
Rational covers can be used after clearing denominators. Existence of a cheap
cover is not asserted. Connectivity, not a diameter bound for P, is assumed. -/
theorem diamLE_of_weighted_face_cover
    {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B weight : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, 0 < weight i → DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ ∑ i, if x ∈ F i then weight i else 0)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L, Walk P L u v) :
    DiamLE P ((∑ i, weight i * (B i + 1)) / q - 1) := by
  classical
  intro u hu v hv
  have hex : ∃ L, Walk P L u v := hconnect u hu v hv
  let L := Nat.find hex
  obtain ⟨w, hw0, hwL, hs⟩ := Nat.find_spec hex
  have hmin : IsShortestLength P u v L := by
    intro K hK
    exact Nat.find_min' hex hK
  have hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P :=
    walk_vertices_extreme P w (by simpa only [hw0] using hu) hs
  have hbudget := shortest_weighted_face_cover_budget d L q P F B weight
    hF hFD u v w hw0 hwL hs hmin hverts
    (fun j hj => hcover (w j) (hverts j hj))
  have hquot : L + 1 ≤ (∑ i, weight i * (B i + 1)) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    simpa only [Nat.mul_comm] using hbudget
  have hL : L ≤ (∑ i, weight i * (B i + 1)) / q - 1 := by omega
  exact HirschProduct.pad_walk (Adj P) hL w hw0 hwL hs

#print axioms shortest_weighted_face_cover_budget
#print axioms diamLE_of_weighted_face_cover

end HirschFaceSplice
