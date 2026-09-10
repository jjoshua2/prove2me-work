import Solutions.PolynomialRegionRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

lemma route_one {V : Type*} (R : V → V → Prop) {u v : V}
    (h : u = v ∨ R u v) : Route R 1 u v := by
  refine ⟨fun k => if k = 0 then u else v, by simp, by simp, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa using h

lemma pair_region {V : Type*} (R : V → V → Prop) (a b : V)
    (hab : R a b) (hba : R b a) :
    ∀ u ∈ ({a, b} : Set V), ∀ v ∈ ({a, b} : Set V), Route R 1 u v := by
  intro u hu v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact route_one R (Or.inl rfl)
  · exact route_one R (Or.inr hab)
  · exact route_one R (Or.inr hba)
  · exact route_one R (Or.inl rfl)

/-- Repeated uses of the same repair region or surviving bridge do not
multiply its charge. Chronological crossing of region visits is allowed. -/
theorem route_of_mixed_step_cover {V ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (a b : κ → V) (hab : ∀ k, R (a k) (b k)) (hba : ∀ k, R (b k) (a k))
    (w : ℕ → V) (L : ℕ)
    (hcover : ∀ k < L,
      (∃ i, w k ∈ S i ∧ w (k + 1) ∈ S i) ∨
      (∃ e, w k ∈ ({a e, b e} : Set V) ∧ w (k + 1) ∈ ({a e, b e} : Set V))) :
    Route R ((∑ i, C i) + Fintype.card κ) (w 0) (w L) := by
  let T : Sum ι κ → Set V := Sum.elim S (fun e => {a e, b e})
  let D : Sum ι κ → ℕ := Sum.elim C (fun _ => 1)
  have hlocalT : ∀ i, ∀ u ∈ T i, ∀ v ∈ T i, Route R (D i) u v := by
    intro i
    cases i with
    | inl i => exact hlocal i
    | inr e => exact pair_region R (a e) (b e) (hab e) (hba e)
  have hcoverT : ∀ k < L, ∃ i, w k ∈ T i ∧ w (k + 1) ∈ T i := by
    intro k hk
    rcases hcover k hk with ⟨i, hi, hi'⟩ | ⟨e, he, he'⟩
    · exact ⟨Sum.inl i, hi, hi'⟩
    · exact ⟨Sum.inr e, he, he'⟩
  have h := route_of_step_cover R T D hlocalT w L hcoverT
  simpa [D, Fintype.sum_sum_type] using h

/-- Unordered face-damage amortization in the parent vertex graph.
The input need not be a valid graph walk. Each consecutive pair must instead
lie in one certified extreme face or on one listed surviving edge. The output
pays each available face once plus one for each listed surviving edge. -/
theorem route_of_faces_and_surviving_edges
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (a b : κ → EuclideanSpace ℝ (Fin d)) (hedge : ∀ e, Adj P (a e) (b e))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ P)
    (hcover : ∀ k < L,
      (∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) ∨
      (∃ e, w k ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))) ∧
        w (k + 1) ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))))) :
    Route (Adj P) ((∑ i, B i) + Fintype.card κ) (w 0) (w L) := by
  have hrev : ∀ e, Adj P (b e) (a e) := by
    intro e
    refine ⟨(hedge e).1.symm, ?_⟩
    rw [segment_symm]
    exact (hedge e).2
  apply route_of_mixed_step_cover (Adj P) (fun i => extremePoints ℝ P ∩ F i) B
    (fun i => extreme_face_region P (F i) (B i) (hF i) (hD i)) a b hedge hrev w L
  intro k hk
  rcases hcover k hk with ⟨i, hi, hi'⟩ | hgood
  · exact Or.inl ⟨i, ⟨hverts k (by omega), hi⟩,
      ⟨hverts (k + 1) (by omega), hi'⟩⟩
  · exact Or.inr hgood

#print axioms route_one
#print axioms pair_region
#print axioms route_of_mixed_step_cover
#print axioms route_of_faces_and_surviving_edges

end HirschRegionRoute
