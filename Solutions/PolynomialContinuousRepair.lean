import Solutions.PolynomialRadialClipCells

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A connected trace covered by finitely many closed sets forces its endpoint
labels to be connected in the actual set-intersection graph. -/
theorem region_walk_of_preconnected_closed_cover
    {V ι : Type*} [TopologicalSpace V] [Fintype ι]
    (S : ι → Set V) (hc : ∀ i, IsClosed (S i))
    (T : Set V) (hT : IsPreconnected T)
    (hcover : ∀ x ∈ T, ∃ i, x ∈ S i)
    {i j : ι} {u v : V} (huT : u ∈ T) (hvT : v ∈ T)
    (hu : u ∈ S i) (hv : v ∈ S j) :
    Nonempty ((intersectionGraph S).Walk i j) := by
  classical
  by_contra hn
  let A : Set ι := {k | Nonempty ((intersectionGraph S).Walk i k)}
  let U : Set V := ⋃ k, ⋃ (_ : k ∈ A), S k
  let W : Set V := ⋃ k, ⋃ (_ : k ∉ A), S k
  have hU : IsClosed U :=
    isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hc k
  have hW : IsClosed W :=
    isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hc k
  have hcov : T ⊆ U ∪ W := by
    intro x hx
    obtain ⟨k, hk⟩ := hcover x hx
    by_cases ha : k ∈ A
    · exact Or.inl (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨ha, hk⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨ha, hk⟩⟩)
  have hiA : i ∈ A := ⟨.nil⟩
  have hjA : j ∉ A := hn
  obtain ⟨z, _, hzU, hzW⟩ := isPreconnected_closed_iff.mp hT U W hU hW hcov
    ⟨u, huT, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiA, hu⟩⟩⟩
    ⟨v, hvT, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hjA, hv⟩⟩⟩
  obtain ⟨k, hkA, hzk⟩ := mem_iUnion.mp hzU |>.imp fun k h => mem_iUnion.mp h
  obtain ⟨l, hlA, hzl⟩ := mem_iUnion.mp hzW |>.imp fun l h => mem_iUnion.mp h
  obtain ⟨p⟩ := hkA
  obtain ⟨q⟩ := shared_point_walk S hzk hzl
  exact hlA ⟨p.append q⟩

/-- Closed extreme faces covering a connected feasible trace suffice. Ordinary
intersection points become parent vertices by compactness. -/
theorem route_of_preconnected_closed_face_cover
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hc : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (T : Set (EuclideanSpace ℝ (Fin d))) (hT : IsPreconnected T)
    (hcover : ∀ x ∈ T, ∃ i, x ∈ F i)
    (u v : EuclideanSpace ℝ (Fin d))
    (huT : u ∈ T) (hvT : v ∈ T)
    (huP : u ∈ extremePoints ℝ P) (hvP : v ∈ extremePoints ℝ P) :
    Route (Adj P) (∑ i, B i) u v := by
  obtain ⟨i, hui⟩ := hcover u huT
  obtain ⟨j, hvj⟩ := hcover v hvT
  obtain ⟨p⟩ := region_walk_of_preconnected_closed_cover F hc T hT hcover huT hvT hui hvj
  let S := fun i => extremePoints ℝ P ∩ F i
  have q : Nonempty ((intersectionGraph S).Walk i j) := by
    clear hui hvj
    induction p with
    | nil => exact ⟨.nil⟩
    | @cons a b c hab p ih =>
      obtain ⟨x, hxa, hxb⟩ := hab.2
      obtain ⟨z, hzP, hza, hzb⟩ := compact_faces_shared_point_portal
        P (F a) (F b) hP (hF a) (hF b) (hc a) (hc b) x hxa hxb
      obtain ⟨q⟩ := ih
      exact ⟨.cons ⟨hab.1, z, ⟨hzP, hza⟩, ⟨hzP, hzb⟩⟩ q⟩
  exact route_of_connected_regions (Adj P) S B
    (fun k => extreme_face_region P (F k) (B k) (hF k) (hD k))
    q u v ⟨huP, hui⟩ ⟨hvP, hvj⟩

#print axioms region_walk_of_preconnected_closed_cover
#print axioms route_of_preconnected_closed_face_cover

end HirschRegionRoute

namespace HirschRadial

/-- A finite maximum including the constant one. -/
def gauge {V ι : Type*} : List ι → (ι → V → ℝ) → V → ℝ
  | [], _, _ => 1
  | i :: l, r, x => max (r i x) (gauge l r x)

lemma gauge_ge_one {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V) :
    1 ≤ gauge l r x := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact ih.trans (le_max_right _ _)

lemma le_gauge {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V)
    {i : ι} (hi : i ∈ l) : r i x ≤ gauge l r x := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact le_max_left _ _
    · exact (ih hi).trans (le_max_right _ _)

lemma gauge_attains {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V) :
    gauge l r x = 1 ∨ ∃ i ∈ l, gauge l r x = r i x := by
  induction l with
  | nil => exact Or.inl rfl
  | cons i l ih =>
    by_cases h : r i x ≤ gauge l r x
    · rw [gauge, max_eq_right h]
      rcases ih with h1 | ⟨j, hj, heq⟩
      · exact Or.inl h1
      · exact Or.inr ⟨j, List.mem_cons_of_mem i hj, heq⟩
    · rw [gauge, max_eq_left (le_of_not_ge h)]
      exact Or.inr ⟨i, by simp, rfl⟩

lemma gauge_eq_one {V ι : Type*} (l : List ι) (r : ι → V → ℝ) (x : V)
    (h : ∀ i ∈ l, r i x ≤ 1) : gauge l r x = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [gauge, ih (fun j hj => h j (List.mem_cons_of_mem i hj))]
    exact max_eq_right (h i (by simp))

lemma continuous_gauge {V ι : Type*} [TopologicalSpace V]
    (l : List ι) (r : ι → V → ℝ) (h : ∀ i, Continuous (r i)) :
    Continuous (gauge l r) := by
  induction l with
  | nil => exact continuous_const
  | cons i l ih => exact (h i).max ih

variable {d : ℕ} {ι : Type*} [Fintype ι]

abbrev ClipSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

def finalClip (Q : Set (ClipSpace d)) (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) :=
  Q ∩ {x | ∀ i, f i x ≤ b i}

def normalized (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d)
    (i : ι) (x : ClipSpace d) : ℝ := (f i x - f i o) / (b i - f i o)

def scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) : ℝ :=
  gauge Finset.univ.toList (normalized f b o) x

def retract (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) : ClipSpace d :=
  point o x (scale f b o x)

lemma scale_ge_one (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d) :
    1 ≤ scale f b o x := gauge_ge_one _ _ _

lemma normalized_le_scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (o x : ClipSpace d) (i : ι) : normalized f b o i x ≤ scale f b o x := by
  apply le_gauge
  simp

lemma continuous_scale (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d) :
    Continuous (scale f b o) := by
  apply continuous_gauge
  intro i
  exact ((f i).continuous.sub continuous_const).div_const _

lemma continuous_retract (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o : ClipSpace d) :
    Continuous (retract f b o) := by
  have hi : Continuous (fun x => (scale f b o x)⁻¹) :=
    (continuous_scale f b o).inv₀ fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (scale_ge_one f b o x))
  exact continuous_const.add (hi.smul (continuous_id.sub continuous_const))

lemma retract_mem (Q : Set (ClipSpace d)) (hQ : Convex ℝ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (ho : o ∈ Q) (hx : x ∈ Q) (hs : ∀ i, f i o < b i) :
    retract f b o x ∈ finalClip Q f b :=
  point_mem_final_clip Q hQ (fun i => (f i).toLinearMap) b o x ho hx hs
    (scale_ge_one f b o x) (normalized_le_scale f b o x)

lemma retract_fixes (Q : Set (ClipSpace d))
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (hs : ∀ i, f i o < b i) (hx : x ∈ finalClip Q f b) :
    retract f b o x = x := by
  have hm : scale f b o x = 1 := by
    apply gauge_eq_one
    intro i _
    apply (div_le_iff₀ (sub_pos.mpr (hs i))).mpr
    simpa using sub_le_sub_right (hx.2 i) (f i o)
  change point o x (scale f b o x) = x
  rw [hm, point_at_unit_scale]

lemma retract_eq_self_or_on_cut
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ) (o x : ClipSpace d)
    (hs : ∀ i, f i o < b i) :
    retract f b o x = x ∨ ∃ i, f i (retract f b o x) = b i := by
  rcases gauge_attains Finset.univ.toList (normalized f b o) x with h | ⟨i, _, hi⟩
  · left
    change point o x (scale f b o x) = x
    rw [show scale f b o x = 1 from h, point_at_unit_scale]
  · right
    exact ⟨i, point_mem_active_final_face (f i).toLinearMap (b i) o x (hs i)
      (scale_ge_one f b o x) hi⟩

#print axioms gauge_ge_one
#print axioms le_gauge
#print axioms gauge_attains
#print axioms gauge_eq_one
#print axioms continuous_gauge
#print axioms scale_ge_one
#print axioms normalized_le_scale
#print axioms continuous_scale
#print axioms continuous_retract
#print axioms retract_mem
#print axioms retract_fixes
#print axioms retract_eq_self_or_on_cut

end HirschRadial
