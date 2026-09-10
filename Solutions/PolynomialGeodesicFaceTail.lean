import Solutions.PolynomialGeodesicFaceCover

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschFaceSplice

/-- A shortest walk cannot repeat a vertex. The singleton face at the
repeated vertex has diameter zero, so the face-span lemma applies. -/
lemma shortest_no_repeat_of_le
    (d L s t : ℕ) (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P)
    (hst : s ≤ t) (htL : t ≤ L) (heq : w s = w t) : s = t := by
  have hsL : s ≤ L := hst.trans htL
  have hsext := hverts s hsL
  have hsingle : IsExtreme ℝ P ({w s} : Set (EuclideanSpace ℝ (Fin d))) := by
    refine ⟨?_, ?_⟩
    · intro y hy
      have hy' : y = w s := Set.mem_singleton_iff.mp hy
      rw [hy']
      exact hsext.1
    · intro p hp q hq z hz hseg
      have hz' : z = w s := Set.mem_singleton_iff.mp hz
      rw [hz'] at hseg
      exact Set.mem_singleton_iff.mpr (hsext.2 hp hq hseg)
  have hD : DiamLE ({w s} : Set (EuclideanSpace ℝ (Fin d))) 0 := by
    intro p hp q hq
    have hp' : p = w s := Set.mem_singleton_iff.mp hp.1
    have hq' : q = w s := Set.mem_singleton_iff.mp hq.1
    refine ⟨fun _ => p, rfl, hp'.trans hq'.symm, ?_⟩
    intro j hj
    omega
  have hspan := shortest_face_visit_span_le d L 0 s t P {w s}
    hsingle hD u v w hw0 hwL hs hmin hst htL hsext (hverts t htL)
    (by simp) (by simpa only [Set.mem_singleton_iff] using heq.symm)
  omega

/-- After position B, a shortest path can only visit vertices sharing no
selected face with its start. An explicit finite set T containing those
vertices therefore bounds the entire tail, not just its incidence count. -/
theorem shortest_face_disjoint_tail_budget
    {ι : Type*} (d L B : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P)
    (T : Finset (EuclideanSpace ℝ (Fin d)))
    (htail : ∀ x ∈ extremePoints ℝ P,
      (∀ i, u ∈ F i → x ∉ F i) → x ∈ T) : L ≤ B + T.card := by
  classical
  let I := Finset.Icc (B + 1) L
  have hsub : I.image w ⊆ T := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hjI : B + 1 ≤ j ∧ j ≤ L := Finset.mem_Icc.mp hj
    apply htail (w j) (hverts j hjI.2)
    intro i hui hji
    have hspan := shortest_face_visit_span_le d L B 0 j P (F i)
      (hF i) (hFD i) u v w hw0 hwL hs hmin (Nat.zero_le j) hjI.2
      (hverts 0 (Nat.zero_le L)) (hverts j hjI.2)
      (by simpa only [hw0] using hui) hji
    omega
  have hinj : Set.InjOn w I := by
    intro s hsI t htI heq
    have hsL : s ≤ L := (Finset.mem_Icc.mp hsI).2
    have htL : t ≤ L := (Finset.mem_Icc.mp htI).2
    by_cases hst : s ≤ t
    · exact shortest_no_repeat_of_le d L s t P u v w hw0 hwL hs hmin hverts
        hst htL heq
    · exact (shortest_no_repeat_of_le d L t s P u v w hw0 hwL hs hmin hverts
        (by omega) hsL heq.symm).symm
  have hcount : I.card ≤ T.card := by
    calc
      I.card = (I.image w).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ T.card := Finset.card_le_card hsub
  have hIcard : I.card = L - B := by simp [I]
  rw [hIcard] at hcount
  omega

/-- A uniform B bound for selected face diameters and at most K vertices
sharing no selected face with any start give parent diameter at most B+K.
The face family need not be finite, and no parent diameter is assumed. -/
theorem diamLE_of_disjoint_face_tail_bound
    {ι : Type*} (d B K : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) B)
    (htails : ∀ u ∈ extremePoints ℝ P,
      ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card ≤ K ∧
        ∀ x ∈ extremePoints ℝ P, (∀ i, u ∈ F i → x ∉ F i) → x ∈ T)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L, Walk P L u v) : DiamLE P (B + K) := by
  classical
  intro u hu v hv
  obtain ⟨T, hTcard, hT⟩ := htails u hu
  have hex : ∃ L, Walk P L u v := hconnect u hu v hv
  let L := Nat.find hex
  obtain ⟨w, hw0, hwL, hs⟩ := Nat.find_spec hex
  have hmin : IsShortestLength P u v L := by
    intro A hA
    exact Nat.find_min' hex hA
  have hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P :=
    walk_vertices_extreme P w (by simpa only [hw0] using hu) hs
  have hbound := shortest_face_disjoint_tail_budget d L B P F hF hFD
    u v w hw0 hwL hs hmin hverts T hT
  have hLK : L ≤ B + K := hbound.trans (Nat.add_le_add_left hTcard B)
  exact HirschProduct.pad_walk (Adj P) hLK w hw0 hwL hs

#print axioms shortest_no_repeat_of_le
#print axioms shortest_face_disjoint_tail_budget
#print axioms diamLE_of_disjoint_face_tail_bound

end HirschFaceSplice
