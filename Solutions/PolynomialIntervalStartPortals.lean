import Solutions.PolynomialIntervalRegionRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- Chronological overlap has an automatic region portal when every interval
contains the start point of every later interval that begins before it ends.
The later start itself is the shared point. -/
lemma interval_portal_of_start_containment {V ι : Type*}
    (S : ι → Set V) (s t : ι → ℕ) (w : ℕ → V)
    (hstart : ∀ j, w (s j) ∈ S j)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ S i) :
    ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j := by
  intro i j hij hji
  by_cases hs : s i ≤ s j
  · exact ⟨w (s j), hcontain i j hs hji, hstart j⟩
  · have hjs : s j ≤ s i := Nat.le_of_not_ge hs
    exact ⟨w (s i), hstart i, hcontain j i hjs hij⟩

/-- Generic interval routing with no separate existential portal hypothesis:
start-containment implies the portal condition required by `route_of_interval_cover`. -/
theorem route_of_interval_cover_of_start_containment
    {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (s t : ι → ℕ) (w : ℕ → V) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hends : ∀ i, w (s i) ∈ S i ∧ w (t i) ∈ S i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ S i) :
    Route R (∑ i, C i) (w 0) (w L) := by
  apply route_of_interval_cover R S C hlocal s t w L hbound hends hcover
  exact interval_portal_of_start_containment S s t w (fun j => (hends j).1) hcontain

/-- Extreme-face specialization.  It is enough that each interval's start and
end are parent vertices in its own face, and that a later interval start which
occurs before an earlier interval ends lies in the earlier supporting face.
The later start is then a genuine parent-vertex portal between the two faces. -/
theorem route_of_face_interval_cover_of_start_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover P F B hF hD s t w L hbound hverts hends hcover
  intro i j hij hji
  by_cases hs : s i ≤ s j
  · exact ⟨w (s j), (hverts j).1, hcontain i j hs hji, (hends j).1⟩
  · have hjs : s j ≤ s i := Nat.le_of_not_ge hs
    exact ⟨w (s i), (hverts i).1, (hends i).1, hcontain j i hjs hij⟩

/-- More geometric but stronger sufficient hypothesis: if every checkpoint of
an interval remains in its supporting face throughout that interval, then
start-containment is automatic and the same total face-budget route follows.
This is the form closest to a Case-VII statement that a damaged path segment
lies in one common face. -/
theorem route_of_face_interval_cover_of_active_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_face_interval_cover_of_start_containment
    P F B hF hD s t w L hbound hverts
    (fun i => ⟨hactive i (s i) (Nat.le_refl _) ((hbound i).trans' (Nat.zero_le _)),
      hactive i (t i) (by
        have hs : s i ≤ t i := by
          by_contra h
          have hlt : t i < s i := Nat.lt_of_not_ge h
          have hk := hcover (t i) (lt_of_le_of_lt (hbound i) (Nat.lt_succ_self L))
          obtain ⟨j, hsj, hj⟩ := hk
          omega
        exact hs) (Nat.le_refl _)⟩)
    hcover
  intro i j hs hst
  exact hactive i (s j) hs hst

#print axioms interval_portal_of_start_containment
#print axioms route_of_interval_cover_of_start_containment
#print axioms route_of_face_interval_cover_of_start_containment
#print axioms route_of_face_interval_cover_of_active_containment

end HirschRegionRoute
