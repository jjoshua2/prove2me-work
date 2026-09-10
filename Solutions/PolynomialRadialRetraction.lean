import Solutions.PolynomialRadialClipCells

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A nonempty finite maximum with a constant-one entry, including empty ι. -/
def scale (r : ι → ℝ) : ℝ :=
  (Finset.univ : Finset (Option ι)).sup'
    ⟨none, Finset.mem_univ _⟩ (fun j => j.elim 1 r)

lemma one_le_scale (r : ι → ℝ) : 1 ≤ scale r := by
  exact Finset.le_sup' (fun j : Option ι => j.elim 1 r) (Finset.mem_univ none)

lemma le_scale (r : ι → ℝ) (i : ι) : r i ≤ scale r := by
  exact Finset.le_sup' (fun j : Option ι => j.elim 1 r) (Finset.mem_univ (some i))

lemma scale_le (r : ι → ℝ) {c : ℝ} (h1 : 1 ≤ c) (hr : ∀ i, r i ≤ c) :
    scale r ≤ c := by
  apply Finset.sup'_le
  intro j _
  cases j with
  | none => exact h1
  | some i => exact hr i

lemma scale_eq_one_or_row (r : ι → ℝ) : scale r = 1 ∨ ∃ i, scale r = r i := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Option ι)))
    ⟨none, Finset.mem_univ _⟩ (fun j => j.elim 1 r)
  cases j with
  | none => exact Or.inl hj
  | some i => exact Or.inr ⟨i, hj⟩

lemma continuous_scale {X : Type*} [TopologicalSpace X]
    (r : ι → X → ℝ) (hr : ∀ i, Continuous (r i)) :
    Continuous (fun x => scale (fun i => r i x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Filter.Tendsto.finset_sup'_nhds_apply
  intro j _
  cases j with
  | none => exact tendsto_const_nhds
  | some i => exact (hr i).continuousAt

def row (a : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ where
  toFun x := ⟪a, x⟫
  map_add' := by intros; simp [inner_add_right]
  map_smul' := by intros; simp [inner_smul_right]

def normalizedRow (a : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (o x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (⟪a, x⟫ - ⟪a, o⟫) / (b - ⟪a, o⟫)

def clipSet (Q : Set (EuclideanSpace ℝ (Fin d)))
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) := Q ∩ {x | ∀ i, ⟪a i, x⟫ ≤ b i}

def retract (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  point o x (scale (fun i => normalizedRow (a i) (b i) o x))

lemma continuous_retract (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) : Continuous (retract a b o) := by
  have hc : Continuous (fun x => scale (fun i => normalizedRow (a i) (b i) o x)) := by
    apply continuous_scale
    intro i
    unfold normalizedRow
    fun_prop
  have hne : ∀ x, scale (fun i => normalizedRow (a i) (b i) o x) ≠ 0 := by
    intro x
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_scale _))
  exact continuous_const.add ((hc.inv₀ hne).smul (continuous_id.sub continuous_const))

lemma retract_mem (Q : Set (EuclideanSpace ℝ (Fin d))) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q) (hx : x ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i) : retract a b o x ∈ clipSet Q a b := by
  apply point_mem_final_clip Q hQ (fun i => row (a i)) b o x ho hx hstrict (one_le_scale _)
  intro i
  change normalizedRow (a i) (b i) o x ≤ scale (fun j => normalizedRow (a j) (b j) o x)
  exact le_scale (fun j => normalizedRow (a j) (b j) o x) i

lemma retract_fixes (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i) (hx : ∀ i, ⟪a i, x⟫ ≤ b i) :
    retract a b o x = x := by
  have hm : scale (fun i => normalizedRow (a i) (b i) o x) = 1 := by
    apply le_antisymm (scale_le _ (le_refl _) ?_) (one_le_scale _)
    intro i
    apply (div_le_iff₀ (sub_pos.mpr (hstrict i))).mpr
    linarith [hx i]
  simp [retract, hm, point_at_unit_scale]

lemma retract_eq_self_or_on_cut
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i) :
    retract a b o x = x ∨ ∃ i, ⟪a i, retract a b o x⟫ = b i := by
  rcases scale_eq_one_or_row (fun i => normalizedRow (a i) (b i) o x) with h | ⟨i, hi⟩
  · exact Or.inl (by simp [retract, h, point_at_unit_scale])
  · exact Or.inr ⟨i, point_mem_active_final_face (row (a i)) (b i) o x
      (hstrict i) (one_le_scale _) hi⟩

lemma retract_on_cut_of_exceeded
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d))
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (j : ι) (hj : b j ≤ ⟪a j, x⟫) :
    ∃ i, ⟪a i, retract a b o x⟫ = b i := by
  rcases scale_eq_one_or_row (fun i => normalizedRow (a i) (b i) o x) with h | ⟨i, hi⟩
  · have hle := le_scale (fun i => normalizedRow (a i) (b i) o x) j
    rw [h] at hle
    have hraw : ⟪a j, x⟫ - ⟪a j, o⟫ ≤ 1 * (b j - ⟪a j, o⟫) :=
      (div_le_iff₀ (sub_pos.mpr (hstrict j))).mp hle
    have heq : ⟪a j, x⟫ = b j := by linarith
    exact ⟨j, by simpa [retract, h, point_at_unit_scale] using heq⟩
  · exact ⟨i, point_mem_active_final_face (row (a i)) (b i) o x
      (hstrict i) (one_le_scale _) hi⟩

#print axioms one_le_scale
#print axioms le_scale
#print axioms scale_le
#print axioms scale_eq_one_or_row
#print axioms continuous_scale
#print axioms continuous_retract
#print axioms retract_mem
#print axioms retract_fixes
#print axioms retract_eq_self_or_on_cut
#print axioms retract_on_cut_of_exceeded

end HirschRadial
