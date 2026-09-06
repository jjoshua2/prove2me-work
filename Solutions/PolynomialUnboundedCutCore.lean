import Mathlib
import Solutions.PolynomialClipSplice

open scoped RealInnerProductSpace
open Set Hirsch HirschCut HirschClip

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschUnboundedCut

lemma one_edge_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Walk P 1 u v := by
  refine ⟨fun j => if j = 0 then u else v, by simp, by simp, ?_⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  simpa using Or.inr h

variable {d : ℕ}

/-- If every outer vertex is retained, every outer graph walk is retained.
There is no boundedness or compactness hypothesis on the outer set. -/
lemma retain_outer_walk
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (hall : ∀ y ∈ extremePoints ℝ Q, ⟪c, y⟫ ≤ b)
    {B : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (hw : Walk Q B u v) :
    Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) B u v := by
  obtain ⟨w, h0, hB, hs⟩ := hw
  refine ⟨w, h0, hB, ?_⟩
  intro j hj
  rcases hs j hj with heq | he
  · exact Or.inl heq
  · exact Or.inr (retained_edge Q c b he
      (hall _ (HirschPolynomialAccess.adj_left_extreme Q he))
      (hall _ (HirschPolynomialAccess.adj_right_extreme Q he)))

/-- A clipped walk from a strict vertex to the plane has a last strict edge.
Only existence of the walk is used; its length will subsequently be discarded. -/
lemma first_plane_edge
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {D : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (huc : ⟪c, u⟫ < b) (hvc : ⟪c, v⟫ = b)
    (hw : Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) D u v) :
    ∃ x z : EuclideanSpace ℝ (Fin d),
      x ∈ extremePoints ℝ (Q ∩ {y | ⟪c, y⟫ ≤ b}) ∧
      z ∈ extremePoints ℝ (Q ∩ {y | ⟪c, y⟫ ≤ b}) ∧
      ⟪c, x⟫ < b ∧ ⟪c, z⟫ = b ∧
      Adj (Q ∩ {y | ⟪c, y⟫ ≤ b}) x z := by
  classical
  obtain ⟨w, h0, hD, hs⟩ := hw
  have hex : ∃ k : ℕ, k ≤ D ∧ ⟪c, w k⟫ = b :=
    ⟨D, le_rfl, by simpa only [hD] using hvc⟩
  let k := Nat.find hex
  have hk : k ≤ D ∧ ⟪c, w k⟫ = b := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    have heq : ⟪c, u⟫ = b := by simpa only [h, h0] using hk.2
    exact (ne_of_lt huc) heq
  let j := k - 1
  have hjk : j + 1 = k := by dsimp [j]; omega
  have hjD : j < D := by omega
  have hjnot : ⟪c, w j⟫ ≠ b := by
    intro hjplane
    have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, hjplane⟩
    omega
  have hedge : Adj (Q ∩ {y | ⟪c, y⟫ ≤ b}) (w j) (w k) := by
    rcases hs j hjD with heq | he
    · have hwjk : w j = w k := by simpa only [hjk] using heq
      exact False.elim (hjnot (hwjk ▸ hk.2))
    · simpa only [hjk] using he
  have hx := HirschPolynomialAccess.adj_left_extreme _ hedge
  have hz := HirschPolynomialAccess.adj_right_extreme _ hedge
  exact ⟨w j, w k, hx, hz, lt_of_le_of_ne hx.1.2 hjnot, hk.2, hedge⟩

/-- No exterior outer vertex is needed if a clipped path to the face exists.
The cost is at most one extra edge. If an outer vertex lies on/beyond the
plane, ordinary clipping gives B; otherwise all outer edges survive and a
B-step outer path to the last strict predecessor is followed by one edge. -/
theorem cut_access_of_outer_diameter_and_path
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (B : ℕ)
    (hQ : DiamLE Q B)
    {D : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (hvc : ⟪c, v⟫ = b)
    (hw : Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) D u v) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧
      ⟪c, z⟫ = b ∧ Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + 1) u z := by
  classical
  by_cases huc : ⟪c, u⟫ = b
  · exact ⟨u, hu, huc, ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩⟩
  have hult : ⟪c, u⟫ < b := lt_of_le_of_ne hu.1.2 huc
  have huQ := strict_cut_extreme_to_parent Q hconv c b hu hult
  by_cases hex : ∃ y ∈ extremePoints ℝ Q, b ≤ ⟪c, y⟫
  · obtain ⟨y, hy, hyc⟩ := hex
    obtain ⟨z, hz, hzc, hwz⟩ := outer_cut_walk Q c b B hQ huQ hy hult hyc
    exact ⟨z, hz, hzc, walk_pad (by omega : B ≤ B + 1) hwz⟩
  · have hall : ∀ y ∈ extremePoints ℝ Q, ⟪c, y⟫ ≤ b := by
      intro y hy
      exact (lt_of_not_ge (fun h => hex ⟨y, hy, h⟩)).le
    obtain ⟨x, z, hx, hz, hxc, hzc, hxz⟩ := first_plane_edge Q c b hult hvc hw
    have hxQ := strict_cut_extreme_to_parent Q hconv c b hx hxc
    have hux := retain_outer_walk Q c b hall (hQ u huQ x hxQ)
    exact ⟨z, hz, hzc, walk_append hux (one_edge_walk hxz)⟩

/-- Full clipped diameter with a possibly unbounded outer set. Connectivity
of the clipped graph supplies a crossing witness, not a numerical budget.
Two strict endpoints still share ONE outer walk, by first/last-contact
splicing. Thus the bound is B+C+1, not 2B+C+2. -/
theorem clipped_diameter_of_outer_and_connected_clip
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (B C : ℕ)
    (hQ : DiamLE Q B)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C)
    (hconnect : ∀ u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}),
      ∀ v ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}),
        ∃ D : ℕ, Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) D u v) :
    DiamLE (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + C + 1) := by
  intro u hu v hv
  by_cases huc : ⟪c, u⟫ = b
  · by_cases hvc : ⟪c, v⟫ = b
    · exact walk_pad (by omega : C ≤ B + C + 1)
        (cut_face_walk Q c b C hF hu hv huc hvc)
    · obtain ⟨D, hvu⟩ := hconnect v hv u hu
      obtain ⟨z, hz, hzc, hvz⟩ :=
        cut_access_of_outer_diameter_and_path Q hconv c b B hQ hv huc hvu
      have hzu := cut_face_walk Q c b C hF hz hu hzc huc
      exact walk_pad (by omega : (B + 1) + C ≤ B + C + 1)
        (walk_reverse (walk_append hvz hzu))
  · have hult : ⟪c, u⟫ < b := lt_of_le_of_ne hu.1.2 huc
    have huQ := strict_cut_extreme_to_parent Q hconv c b hu hult
    by_cases hvc : ⟪c, v⟫ = b
    · obtain ⟨D, huv⟩ := hconnect u hu v hv
      obtain ⟨z, hz, hzc, huz⟩ :=
        cut_access_of_outer_diameter_and_path Q hconv c b B hQ hu hvc huv
      exact walk_pad (by omega : (B + 1) + C ≤ B + C + 1)
        (walk_append huz (cut_face_walk Q c b C hF hz hv hzc hvc))
    · have hvlt : ⟪c, v⟫ < b := lt_of_le_of_ne hv.1.2 hvc
      have hvQ := strict_cut_extreme_to_parent Q hconv c b hv hvlt
      obtain ⟨w, h0, hB, hs⟩ := hQ u huQ v hvQ
      have hstart : ⟪c, w 0⟫ < b := by simpa only [h0] using hult
      have hfinish : ⟪c, w B⟫ < b := by simpa only [hB] using hvlt
      have hspliced := splice_outer_walk d B C Q c b hF w hstart hfinish hs
      apply walk_pad (by omega : B + C ≤ B + C + 1)
      simpa only [h0, hB] using hspliced

#print axioms cut_access_of_outer_diameter_and_path
#print axioms clipped_diameter_of_outer_and_connected_clip

end HirschUnboundedCut
