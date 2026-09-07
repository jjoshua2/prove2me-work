import Solutions.SingleCutCubeBasic

open Set Hirsch HirschClip

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschCubeCut

variable {d : ℕ}

lemma positive_common_bound {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    (∀ i ∈ s, 0 < r i) → ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      intro hr
      obtain ⟨δ, hδ, hb⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
      have hri : 0 < r i := hr i (Finset.mem_insert_self i s)
      refine ⟨min δ (r i), lt_min hδ hri, ?_⟩
      intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hb j hj)

/-- A direction annihilating all active box bounds and the active cut row
must vanish at a vertex. Proved by an explicit two-sided feasible perturbation;
no external spanning or polyhedral connectivity theorem is imported. -/
lemma vertex_direction_zero (a : Fin d → ℝ) (β : ℝ)
    {x : Fin d → ℝ} (hx : x ∈ extremePoints ℝ (Clip a β))
    (h : Fin d → ℝ)
    (hb : ∀ i, (x i = 0 ∨ x i = 1) → h i = 0)
    (hc : cost a x = β → cost a h = 0) : h = 0 := by
  classical
  let τ : Fin d → ℝ := fun i =>
    if h i = 0 then 1 else min (x i) (1 - x i) / (|h i| + 1)
  have hτ : ∀ i, 0 < τ i := by
    intro i
    by_cases hhi : h i = 0
    · simp [τ, hhi]
    · have hx0 : x i ≠ 0 := fun he => hhi (hb i (Or.inl he))
      have hx1 : x i ≠ 1 := fun he => hhi (hb i (Or.inr he))
      have hxp : 0 < x i := lt_of_le_of_ne (hx.1.1 i).1 hx0.symm
      have hxm : x i < 1 := lt_of_le_of_ne (hx.1.1 i).2 hx1
      have hm : 0 < min (x i) (1 - x i) := lt_min hxp (by linarith)
      simpa only [τ, if_neg hhi] using div_pos hm (by positivity : 0 < |h i| + 1)
  obtain ⟨δ0, hδ0, hbound⟩ := positive_common_bound Finset.univ τ (fun i _ => hτ i)
  let η : ℝ := if cost a x = β then 1 else (β - cost a x) / (|cost a h| + 1)
  have hη : 0 < η := by
    by_cases heq : cost a x = β
    · simp [η, heq]
    · have hlt : cost a x < β := lt_of_le_of_ne hx.1.2 heq
      simpa only [η, if_neg heq] using div_pos (sub_pos.mpr hlt)
        (by positivity : 0 < |cost a h| + 1)
  let δ : ℝ := min δ0 η
  have hδ : 0 < δ := lt_min hδ0 hη
  have hδτ : ∀ i, δ ≤ τ i := fun i =>
    (min_le_left δ0 η).trans (hbound i (Finset.mem_univ i))
  have hcoords : ∀ i,
      (0 ≤ x i + δ * h i ∧ x i + δ * h i ≤ 1) ∧
      (0 ≤ x i - δ * h i ∧ x i - δ * h i ≤ 1) := by
    intro i
    by_cases hhi : h i = 0
    · simpa only [hhi, mul_zero, add_zero, sub_zero] using
        And.intro (hx.1.1 i) (hx.1.1 i)
    · have hd := hδτ i
      rw [show τ i = min (x i) (1 - x i) / (|h i| + 1) by simp [τ, hhi]] at hd
      have hden : 0 < |h i| + 1 := by positivity
      have hmul : δ * (|h i| + 1) ≤ min (x i) (1 - x i) := (le_div_iff₀ hden).1 hd
      have habs : |δ * h i| ≤ min (x i) (1 - x i) := by
        rw [abs_mul, abs_of_pos hδ]
        nlinarith
      have hbds := abs_le.1 habs
      have hmin0 := min_le_left (x i) (1 - x i)
      have hmin1 := min_le_right (x i) (1 - x i)
      constructor <;> constructor <;> linarith
  have hcuts : cost a x + δ * cost a h ≤ β ∧ cost a x - δ * cost a h ≤ β := by
    by_cases heq : cost a x = β
    · simp [heq, hc heq]
    · have hδη : δ ≤ η := min_le_right δ0 η
      rw [show η = (β - cost a x) / (|cost a h| + 1) by simp [η, heq]] at hδη
      have hden : 0 < |cost a h| + 1 := by positivity
      have hmul : δ * (|cost a h| + 1) ≤ β - cost a x := (le_div_iff₀ hden).1 hδη
      have habs : |δ * cost a h| ≤ β - cost a x := by
        rw [abs_mul, abs_of_pos hδ]
        nlinarith
      have hbds := abs_le.1 habs
      constructor <;> linarith
  let p := x + δ • h
  let q := x - δ • h
  have hp : p ∈ Clip a β := by
    refine ⟨fun i => (hcoords i).1, ?_⟩
    change cost a (x + δ • h) ≤ β
    rw [cost_add, cost_smul]
    exact hcuts.1
  have hq : q ∈ Clip a β := by
    refine ⟨fun i => (hcoords i).2, ?_⟩
    change cost a (x - δ • h) ≤ β
    rw [cost_sub, cost_smul]
    exact hcuts.2
  have hopen : x ∈ openSegment ℝ p q := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    funext i
    change (1 / 2 : ℝ) * (x i + δ * h i) + (1 / 2 : ℝ) * (x i - δ * h i) = x i
    ring
  have hpx : p = x := hx.2 hp hq hopen
  funext i
  have hi := congrFun hpx i
  change x i + δ * h i = x i at hi
  change h i = 0
  have hprod : δ * h i = 0 := by linarith
  exact (mul_eq_zero.mp hprod).resolve_left hδ.ne'

/-- Noncorner vertices are cut points in interiors of original cube edges.
In particular exactly one coordinate is fractional, and its cut coefficient
is nonzero. This includes degenerate cuts through existing cube vertices. -/
lemma noncorner_vertex_structure (a : Fin d → ℝ) (β : ℝ)
    {x : Fin d → ℝ} (hx : x ∈ extremePoints ℝ (Clip a β))
    (hn : ¬ Corner x) :
    ∃ i : Fin d, 0 < x i ∧ x i < 1 ∧ a i ≠ 0 ∧ cost a x = β ∧
      ∀ j, j ≠ i → x j = 0 ∨ x j = 1 := by
  classical
  change ¬ ∀ i, x i = 0 ∨ x i = 1 at hn
  push Not at hn
  obtain ⟨i, hxi0, hxi1⟩ := hn
  have hxp : 0 < x i := lt_of_le_of_ne (hx.1.1 i).1 hxi0.symm
  have hxm : x i < 1 := lt_of_le_of_ne (hx.1.1 i).2 hxi1
  have hunit : ∀ k, (x k = 0 ∨ x k = 1) → (Pi.single i (1 : ℝ)) k = 0 := by
    intro k hk
    by_cases hki : k = i
    · subst k
      exact False.elim (hk.elim hxi0 hxi1)
    · simp [Pi.single_eq_of_ne hki]
  have hai : a i ≠ 0 := by
    intro ha0
    have hz := vertex_direction_zero a β hx (Pi.single i 1) hunit (fun _ => by rw [cost_single, ha0]; ring)
    have he := congrFun hz i
    simpa using he
  have hcut : cost a x = β := by
    by_contra hnot
    have hz := vertex_direction_zero a β hx (Pi.single i 1) hunit (fun he => False.elim (hnot he))
    have he := congrFun hz i
    simpa using he
  refine ⟨i, hxp, hxm, hai, hcut, ?_⟩
  intro j hji
  by_contra hj
  push Not at hj
  let h : Fin d → ℝ := a j • Pi.single i (1 : ℝ) - a i • Pi.single j (1 : ℝ)
  have hb : ∀ k, (x k = 0 ∨ x k = 1) → h k = 0 := by
    intro k hk
    by_cases hki : k = i
    · subst k
      exact False.elim (hk.elim hxi0 hxi1)
    by_cases hkj : k = j
    · subst k
      exact False.elim (hk.elim hj.1 hj.2)
    simp [h, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]
  have hcost : cost a h = 0 := by
    dsimp [h]
    rw [cost_sub, cost_smul, cost_smul, cost_single, cost_single]
    ring
  have hz := vertex_direction_zero a β hx h hb (fun _ => hcost)
  have he := congrFun hz j
  have haz : a i = 0 := by
    simpa [h, Pi.single_eq_of_ne hji] using he
  exact hai haz

#print axioms noncorner_vertex_structure

end HirschCubeCut
