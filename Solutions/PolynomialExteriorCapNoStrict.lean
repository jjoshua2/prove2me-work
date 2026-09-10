import Solutions.PolynomialExteriorCapClipping

/-! Remove the explicit strict-centre hypothesis from the exterior-cap witness
clipping theorem.  If no cut is equality on the whole final polytope, finite
convex averaging produces one point strict for every cut simultaneously. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial HirschRegionRoute

noncomputable section
namespace HirschExterior

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- For finitely many valid linear inequalities on a nonempty convex set,
either one point is strict for every inequality, or one inequality is equality
everywhere on the set. -/
lemma strict_centre_or_universal_final_cut
    (P : Set (ClipSpace d)) (hP : Convex ℝ P) (hne : P.Nonempty)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (hbound : ∀ i, ∀ x ∈ P, f i x ≤ b i) :
    (∃ o ∈ P, ∀ i, f i o < b i) ∨
      (∃ i, ∀ x ∈ P, f i x = b i) := by
  classical
  by_cases huniv : ∃ i, ∀ x ∈ P, f i x = b i
  · exact Or.inr huniv
  have hpoint : ∀ i, ∃ x ∈ P, f i x < b i := by
    intro i
    by_contra h
    push_neg at h
    apply huniv
    exact ⟨i, fun x hx => le_antisymm (hbound i x hx) (h x hx)⟩
  have hfinite : ∀ s : Finset ι, ∃ o ∈ P, ∀ i ∈ s, f i o < b i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨o, ho⟩ := hne
        exact ⟨o, ho, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨o, ho, hs⟩ := ih
        obtain ⟨x, hx, hix⟩ := hpoint i
        refine ⟨(1 / 2 : ℝ) • o + (1 / 2 : ℝ) • x,
          hP ho hx (by norm_num) (by norm_num) (by norm_num), ?_⟩
        intro j hj
        simp only [map_add, map_smul, smul_eq_mul]
        rcases Finset.mem_insert.mp hj with rfl | hj
        · nlinarith [hbound j o ho]
        · nlinarith [hs j hj, hbound j x hx]
  obtain ⟨o, ho, hs⟩ := hfinite Finset.univ
  exact Or.inl ⟨o, ho, fun i => hs i (Finset.mem_univ _)⟩

/-- Exterior-cap clipping without a separately supplied strict centre.
The exterior cap, old-vertex routing, and cap-vertex classification remain
explicit hypotheses; only strict feasibility of one chosen centre is removed. -/
theorem simultaneous_clip_diameter_from_exterior_cap_no_strict
    (Q G V : Set (ClipSpace d)) (hQ : Convex ℝ Q) (hQc : IsCompact Q)
    (hG : Convex ℝ G) (hGQ : G ⊆ Q)
    (f : ι → ClipSpace d →L[ℝ] ℝ) (b : ι → ℝ)
    (hout : ∀ x ∈ G, x ∉ finalClip Q f b)
    (D : ℕ) (hOld : ∀ a ∈ V, ∀ c ∈ V, Route (Adj Q) D a c)
    (hclass : ∀ x ∈ extremePoints ℝ Q,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj Q a x))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE (finalClip Q f b ∩ {x | f i x = b i}) (B i)) :
    DiamLE (finalClip Q f b) (D + 1 + ∑ i, B i) := by
  classical
  let P := finalClip Q f b
  by_cases hne : P.Nonempty
  · rcases strict_centre_or_universal_final_cut P (finalClip_convex Q hQ f b) hne f b
        (fun i x hx => hx.2 i) with ⟨o, ho, hs⟩ | ⟨i, hi⟩
    · exact simultaneous_clip_diameter_from_exterior_cap
        Q G V hQ hQc hG hGQ f b o ho.1 hs hout D hOld hclass B hB
    · have heq : P ∩ {x | f i x = b i} = P := by
        apply inter_eq_left.mpr
        exact fun z hz => hi z hz
      have hPi : DiamLE P (B i) := by
        have h := hB i
        change DiamLE (P ∩ {x | f i x = b i}) (B i) at h
        rw [heq] at h
        exact h
      have hle : B i ≤ D + 1 + ∑ j, B j := by
        have hsum : B i ≤ ∑ j, B j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (B j)) (Finset.mem_univ i)
        omega
      intro u hu v hv
      obtain ⟨w, hw0, hwB, hwstep⟩ := hPi u hu v hv
      exact HirschProduct.pad_walk (Adj P) hle w hw0 hwB hwstep
  · intro u hu v hv
    exact False.elim (hne ⟨u, hu.1⟩)

#print axioms strict_centre_or_universal_final_cut
#print axioms simultaneous_clip_diameter_from_exterior_cap_no_strict

end HirschExterior
