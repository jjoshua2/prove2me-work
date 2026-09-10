import Solutions.PolynomialMixedRegionRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A chronological interval cover connects its endpoint regions when every
closed interval overlap is backed by an actual shared point of the regions.
Interior entries of the old sequence are not used as portals. -/
lemma region_walk_of_interval_cover {V ι : Type*}
    (S : ι → Set V) (s t : ι → ℕ)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j)
    (L : ℕ)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (i j : ι) (hi : s i ≤ 0 ∧ 0 ≤ t i)
    (hj : s j ≤ L ∧ L ≤ t j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  induction L generalizing j with
  | zero =>
      obtain ⟨z, hzi, hzj⟩ := hportal i j
        (hi.1.trans hj.2) (hj.1.trans hi.2)
      exact shared_point_walk S hzi hzj
  | succ L ih =>
      obtain ⟨k, hks, hkt⟩ := hcover L (Nat.lt_succ_self L)
      obtain ⟨p⟩ := ih (fun a ha => hcover a (Nat.lt_succ_of_lt ha)) k
        ⟨hks, (Nat.le_succ L).trans hkt⟩
      obtain ⟨z, hzk, hzj⟩ := hportal k j
        (hks.trans ((Nat.le_succ L).trans hj.2)) (hj.1.trans hkt)
      obtain ⟨q⟩ := shared_point_walk S hzk hzj
      exact ⟨p.append q⟩

/-- Unordered endpoint-supported interval repair. The sequence may have invalid
steps and arbitrary interior points. It is enough that intervals cover every
step, each interval's endpoints lie in its routing region, and chronological
overlaps have genuine region portals. Every available region is charged once.

This does not infer geometric intersection from temporal overlap: `hportal`
is the separate geometric hypothesis which makes crossing intervals safe. -/
theorem route_of_interval_cover {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (s t : ι → ℕ) (w : ℕ → V) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hends : ∀ i, w (s i) ∈ S i ∧ w (t i) ∈ S i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ S i ∧ z ∈ S j) :
    Route R (∑ i, C i) (w 0) (w L) := by
  by_cases hL : L = 0
  · subst L
    exact ⟨fun _ => w 0, rfl, rfl, fun _ _ => Or.inl rfl⟩
  · have hpos : 0 < L := Nat.pos_of_ne_zero hL
    obtain ⟨i, hsi, hti⟩ := hcover 0 hpos
    have hsi0 : s i = 0 := Nat.eq_zero_of_le_zero hsi
    obtain ⟨j, hsj, htj⟩ := hcover (L - 1) (by omega)
    have hlast : L - 1 + 1 = L := Nat.sub_add_cancel (by omega : 1 ≤ L)
    rw [hlast] at htj
    have htjL : t j = L := Nat.le_antisymm (hbound j) htj
    have hi : w 0 ∈ S i := by simpa only [hsi0] using (hends i).1
    have hj : w L ∈ S j := by simpa only [htjL] using (hends j).2
    have hreach := region_walk_of_interval_cover S s t hportal L hcover i j
      ⟨hsi, Nat.zero_le _⟩ ⟨hsj.trans (Nat.sub_le _ _), htj⟩
    exact route_of_connected_regions R S C hlocal hreach (w 0) (w L) hi hj

/-- Geometric specialization: a shared parent extreme vertex is a valid portal
between two extreme-face repairs. Only marked interval endpoints must remain
parent vertices; the old sequence's interior entries need not remain feasible.
The conclusion is conditional on the stated portal and face-diameter data. -/
theorem route_of_face_interval_cover {d : ℕ} {ι : Type*} [Fintype ι]
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
    Route (Adj P) (∑ i, B i) (w 0) (w L) := by
  apply route_of_interval_cover (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i)) s t w L hbound
  · intro i
    exact ⟨⟨(hverts i).1, (hends i).1⟩, ⟨(hverts i).2, (hends i).2⟩⟩
  · exact hcover
  · intro i j hij hji
    obtain ⟨z, hz, hzi, hzj⟩ := hportal i j hij hji
    exact ⟨z, ⟨hz, hzi⟩, ⟨hz, hzj⟩⟩

#print axioms region_walk_of_interval_cover
#print axioms route_of_interval_cover
#print axioms route_of_face_interval_cover

end HirschRegionRoute
