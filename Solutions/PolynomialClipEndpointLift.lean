import Solutions.PolynomialRadialRetraction
import Solutions.PolynomialHalfspaceVertex

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschClipLift

variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma supporting_equality_extreme
    (Q : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (hbound : ∀ x ∈ Q, ⟪c, x⟫ ≤ b) :
    IsExtreme ℝ Q (Q ∩ {x | ⟪c, x⟫ = b}) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  obtain ⟨α, β, hα, hβ, hsum, heq⟩ := hseg
  have heval := congrArg (fun w : EuclideanSpace ℝ (Fin d) => ⟪c, w⟫) heq
  simp only [inner_add_right, inner_smul_right] at heval
  have hz' : ⟪c, z⟫ = b := hz.2
  have hx' := hbound x hx
  have hy' := hbound y hy
  have htotal : α * b + β * b = b := by rw [← add_mul, hsum, one_mul]
  apply le_antisymm hx'
  by_contra h
  have hlt : ⟪c, x⟫ < b := lt_of_not_ge h
  have hpos := mul_pos hα (sub_pos.mpr hlt)
  have hnonneg := mul_nonneg hβ.le (sub_nonneg.mpr hy')
  nlinarith

lemma exists_extreme_above
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : IsCompact Q)
    (c u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Q) :
    ∃ x, x ∈ extremePoints ℝ Q ∧ ⟪c, u⟫ ≤ ⟪c, x⟫ := by
  obtain ⟨z, hz, hmax⟩ := hQ.exists_isMaxOn ⟨u, hu⟩
    (show Continuous (fun x : EuclideanSpace ℝ (Fin d) => ⟪c, x⟫) by fun_prop).continuousOn
  let F : Set (EuclideanSpace ℝ (Fin d)) := Q ∩ {x | ⟪c, x⟫ = ⟪c, z⟫}
  have hF : IsExtreme ℝ Q F := supporting_equality_extreme Q c ⟪c, z⟫ hmax
  have hFc : IsClosed F := hQ.isClosed.inter (isClosed_eq (by fun_prop) continuous_const)
  obtain ⟨x, hx, hxF⟩ := HirschRegionRoute.compact_face_point_has_parent_vertex
    Q F hQ hF hFc ⟨z, hz, rfl⟩
  exact ⟨x, hx, (hmax hu).trans_eq hxF.2.symm⟩

lemma strict_all_cuts_extreme_to_parent
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (HirschRadial.clipSet Q a b))
    (hstrict : ∀ i, ⟪a i, u⟫ < b i) :
    u ∈ extremePoints ℝ Q := by
  classical
  let T : Finset ι → Set (EuclideanSpace ℝ (Fin d)) :=
    fun s => Q ∩ {x | ∀ i ∈ s, ⟪a i, x⟫ ≤ b i}
  have hconv : ∀ s, Convex ℝ (T s) := by
    intro s x hx y hy α β hα hβ hsum
    refine ⟨hQ hx.1 hy.1 hα hβ hsum, ?_⟩
    intro i hi
    simp only [inner_add_right, inner_smul_right]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 i hi) hα
    have h2 := mul_le_mul_of_nonneg_left (hy.2 i hi) hβ
    have htotal : α * b i + β * b i = b i := by rw [← add_mul, hsum, one_mul]
    linarith
  have hremove : ∀ s, u ∈ extremePoints ℝ (T s) → u ∈ extremePoints ℝ Q := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa [T] using (id : u ∈ extremePoints ℝ Q → u ∈ extremePoints ℝ Q)
    | @insert i s hi ih =>
        intro huT
        have heq : T (insert i s) = T s ∩ {x | ⟪a i, x⟫ ≤ b i} := by
          ext x
          simp only [T, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert]
          aesop
        rw [heq] at huT
        exact ih (HirschCut.strict_cut_extreme_to_parent (T s) (hconv s)
          (a i) (b i) huT (hstrict i))
  apply hremove Finset.univ
  simpa [T, HirschRadial.clipSet] using hu

/-- Lift every final vertex to an old vertex beyond an active cut, unless
it already is an old vertex. No old vertex need survive the final clipping. -/
theorem endpoint_lift_to_outer_vertex
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (HirschRadial.clipSet Q a b)) :
    ∃ x, x ∈ extremePoints ℝ Q ∧
      (u = x ∨ ∃ i, ⟪a i, u⟫ = b i ∧ b i ≤ ⟪a i, x⟫) := by
  classical
  by_cases hold : u ∈ extremePoints ℝ Q
  · exact ⟨u, hold, Or.inl rfl⟩
  have hactive : ∃ i, ⟪a i, u⟫ = b i := by
    by_contra h
    have hne : ∀ i, ⟪a i, u⟫ ≠ b i := by simpa using h
    have hs : ∀ i, ⟪a i, u⟫ < b i := by
      intro i
      rcases (hu.1.2 i).eq_or_lt with heq | hlt
      · exact False.elim (hne i heq)
      · exact hlt
    exact hold (strict_all_cuts_extreme_to_parent Q hQ a b hu hs)
  obtain ⟨i, hi⟩ := hactive
  obtain ⟨x, hx, hux⟩ := exists_extreme_above Q hQc (a i) u hu.1.1
  exact ⟨x, hx, Or.inr ⟨i, hi, by simpa [hi] using hux⟩⟩

#print axioms supporting_equality_extreme
#print axioms exists_extreme_above
#print axioms strict_all_cuts_extreme_to_parent
#print axioms endpoint_lift_to_outer_vertex

end HirschClipLift
