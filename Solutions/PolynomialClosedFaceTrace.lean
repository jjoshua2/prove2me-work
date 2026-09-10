import Solutions.PolynomialFacePreservingCheckpoints

/-! Finite closed-cover connectivity for continuous repair traces.
Verification status is recorded in research/ClippingVerificationProgress.md. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

lemma finite_closed_region_union {V ι : Type*} [TopologicalSpace V]
    (S : ι → Set V) (hclosed : ∀ i, IsClosed (S i)) (s : Finset ι) :
    IsClosed (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isClosed_empty : IsClosed (∅ : Set V))
  | @insert a s ha ih =>
      have heq : (⋃ i ∈ insert a s, S i) = S a ∪ ⋃ i ∈ s, S i := by
        ext x
        simp
      rw [heq]
      exact (hclosed a).union ih

/-- A finite CLOSED cover of a preconnected trace supplies real region
connectivity. The covering sets need not themselves be connected. -/
theorem region_walk_of_preconnected_closed_cover
    {V ι : Type*} [TopologicalSpace V] [Fintype ι]
    (S : ι → Set V) (hclosed : ∀ i, IsClosed (S i))
    (K : Set V) (hK : IsPreconnected K)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ S i)
    {u v : V} (huK : u ∈ K) (hvK : v ∈ K)
    (i j : ι) (hui : u ∈ S i) (hvj : v ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  classical
  by_contra hnot
  let A : Finset ι := Finset.univ.filter
    (fun k => Nonempty ((intersectionGraph S).Walk i k))
  let B : Finset ι := Finset.univ.filter
    (fun k => ¬ Nonempty ((intersectionGraph S).Walk i k))
  let U : Set V := ⋃ k ∈ A, S k
  let W : Set V := ⋃ k ∈ B, S k
  have hiA : i ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨.nil⟩
  have hjB : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
  have hU : IsClosed U := finite_closed_region_union S hclosed A
  have hW : IsClosed W := finite_closed_region_union S hclosed B
  have hKW : K ⊆ U ∪ W := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x hx
    by_cases hr : Nonempty ((intersectionGraph S).Walk i k)
    · have hkA : k ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
      exact Or.inl (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkA, hk⟩⟩)
    · have hkB : k ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
      exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkB, hk⟩⟩)
  have huU : u ∈ U := mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiA, hui⟩⟩
  have hvW : v ∈ W := mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjB, hvj⟩⟩
  obtain ⟨z, _, hzU, hzW⟩ :=
    (isPreconnected_closed_iff.mp hK) U W hU hW hKW ⟨u, huK, huU⟩ ⟨v, hvK, hvW⟩
  obtain ⟨a, haA, hza⟩ := mem_iUnion₂.mp hzU
  obtain ⟨b, hbB, hzb⟩ := mem_iUnion₂.mp hzW
  have ha : Nonempty ((intersectionGraph S).Walk i a) :=
    (Finset.mem_filter.mp haA).2
  have hb : ¬ Nonempty ((intersectionGraph S).Walk i b) :=
    (Finset.mem_filter.mp hbB).2
  obtain ⟨p⟩ := ha
  obtain ⟨q⟩ := shared_point_walk S hza hzb
  exact hb ⟨p.append q⟩

/-- Transfer an actual face-intersection walk to a parent-vertex portal walk. -/
lemma face_walk_to_parent_vertex_walk
    {d : ℕ} {ι : Type*}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    {i j : ι} (p : (intersectionGraph F).Walk i j) :
    Nonempty ((intersectionGraph (fun k => extremePoints ℝ P ∩ F k)).Walk i j) := by
  induction p with
  | nil => exact ⟨.nil⟩
  | @cons i k j hik p ih =>
      obtain ⟨z, hzi, hzk⟩ := hik.2
      obtain ⟨v, hv, hvi, hvk⟩ := compact_faces_shared_point_portal
        P (F i) (F k) hP (hF i) (hF k) (hclosed i) (hclosed k) z hzi hzk
      obtain ⟨q⟩ := ih
      exact ⟨.cons ⟨hik.1, v, ⟨hv, hvi⟩, ⟨hv, hvk⟩⟩ q⟩

/-- A genuine connected trace covered by finitely many closed parent faces
routes with one charge per face. There is no checkpoint partition assumption. -/
theorem route_of_preconnected_face_cover
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsPreconnected K)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ F i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ P) (hv : v ∈ extremePoints ℝ P)
    (huK : u ∈ K) (hvK : v ∈ K) :
    Route (Adj P) (∑ i, B i) u v := by
  obtain ⟨i, hui⟩ := hcover u huK
  obtain ⟨j, hvj⟩ := hcover v hvK
  obtain ⟨p⟩ := region_walk_of_preconnected_closed_cover F hclosed K hK hcover huK hvK i j hui hvj
  exact route_of_connected_regions (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i))
    (face_walk_to_parent_vertex_walk P F hP hF hclosed p) u v ⟨hu, hui⟩ ⟨hv, hvj⟩

#print axioms finite_closed_region_union
#print axioms region_walk_of_preconnected_closed_cover
#print axioms face_walk_to_parent_vertex_walk
#print axioms route_of_preconnected_face_cover

end HirschRegionRoute
