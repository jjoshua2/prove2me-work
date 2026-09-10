import Solutions.SingleCutCubeBasic

open Set Hirsch HirschClip

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCubeCut

variable {d : ℕ}

lemma corner_mem_box {x : Fin d → ℝ} (hx : Corner x) : x ∈ Box d := by
  intro i
  rcases hx i with hi | hi <;> simp [hi]

/-- Change a finite collection of coordinates to their target values when
each individual change does not increase the cutting functional. -/
lemma corner_cost_walk (a : Fin d → ℝ) (β : ℝ)
    (y : Fin d → ℝ) (hyc : Corner y) (s : Finset (Fin d)) :
    ∀ x : Fin d → ℝ, x ∈ Clip a β → Corner x →
      (∀ i, a i * y i ≤ a i * x i) →
      (∀ i, i ∉ s → x i = y i) → Walk (Clip a β) s.card x y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro x hx hxc hcost hs
      have hxy : x = y := funext (fun i => hs i (by simp))
      subst y
      exact ⟨fun _ => x, rfl, rfl, by simp⟩
  | @insert i s hi ih =>
      intro x hx hxc hcost hs
      let z := Function.update x i (y i)
      have hzc : Corner z := by
        intro j
        by_cases hji : j = i
        · subst j
          simpa [z] using hyc i
        · simpa [z, Function.update_of_ne hji] using hxc j
      have hzP : z ∈ Clip a β := by
        refine ⟨corner_mem_box hzc, ?_⟩
        change cost a (Function.update x i (y i)) ≤ β
        calc
          cost a (Function.update x i (y i)) =
              cost a x + (a i * y i - a i * x i) := by
                rw [cost_update]
                ring
          _ ≤ cost a x := add_le_of_nonpos_right (sub_nonpos.mpr (hcost i))
          _ ≤ β := hx.2
      have hcostz : ∀ j, a j * y j ≤ a j * z j := by
        intro j
        by_cases hji : j = i
        · subst j
          simp [z]
        · simpa [z, Function.update_of_ne hji] using hcost j
      have houtside : ∀ j, j ∉ s → z j = y j := by
        intro j hjs
        by_cases hji : j = i
        · subst j
          simp [z]
        · rw [show z j = x j by simp [z, Function.update_of_ne hji]]
          exact hs j (by simp [hji, hjs])
      have hfirst : x = z ∨ Adj (Clip a β) x z := by
        by_cases heq : x i = y i
        · left
          funext j
          by_cases hji : j = i
          · subst j
            simp [z, heq]
          · simp [z, Function.update_of_ne hji]
        · right
          apply corner_flip_adj a β hx hzP hxc hzc i
          · simpa [z] using heq
          · intro j hji
            simp [z, Function.update_of_ne hji]
      have hrest := ih z hzP hzc hcostz houtside
      have hw := walk_append (one_step_walk hfirst) hrest
      simpa [Finset.card_insert_of_notMem hi, Nat.add_comm] using hw

/-- Retained original corners admit a feasible coordinate-edge path of
Hamming length after one arbitrary real halfspace cut. This need not be a
shortest path in the clipped graph or monotone in an optimization objective. -/
theorem retained_corners_hamming_walk
    (a : Fin d → ℝ) (β : ℝ) (x y : Fin d → ℝ)
    (hx : x ∈ Clip a β) (hy : y ∈ Clip a β)
    (hxc : Corner x) (hyc : Corner y) :
    Walk (Clip a β) (Finset.univ.filter (fun i => x i ≠ y i)).card x y := by
  classical
  let z : Fin d → ℝ := fun i => if 0 ≤ a i then min (x i) (y i) else max (x i) (y i)
  have hzchoice : ∀ i, z i = x i ∨ z i = y i := by
    intro i
    by_cases ha : 0 ≤ a i <;> rcases le_total (x i) (y i) with h | h
    · exact Or.inl (by simp [z, ha, min_eq_left h])
    · exact Or.inr (by simp [z, ha, min_eq_right h])
    · exact Or.inr (by simp [z, ha, max_eq_right h])
    · exact Or.inl (by simp [z, ha, max_eq_left h])
  have hzc : Corner z := by
    intro i
    rcases hzchoice i with h | h
    · simpa only [h] using hxc i
    · simpa only [h] using hyc i
  have hzx : ∀ i, a i * z i ≤ a i * x i := by
    intro i
    by_cases ha : 0 ≤ a i
    · simpa only [z, if_pos ha] using mul_le_mul_of_nonneg_left (min_le_left (x i) (y i)) ha
    · simpa only [z, if_neg ha] using
        mul_le_mul_of_nonpos_left (le_max_left (x i) (y i)) (le_of_lt (lt_of_not_ge ha))
  have hzy : ∀ i, a i * z i ≤ a i * y i := by
    intro i
    by_cases ha : 0 ≤ a i
    · simpa only [z, if_pos ha] using mul_le_mul_of_nonneg_left (min_le_right (x i) (y i)) ha
    · simpa only [z, if_neg ha] using
        mul_le_mul_of_nonpos_left (le_max_right (x i) (y i)) (le_of_lt (lt_of_not_ge ha))
  let S := Finset.univ.filter (fun i => x i ≠ z i)
  let T := Finset.univ.filter (fun i => y i ≠ z i)
  have hS : ∀ i, i ∉ S → x i = z i := by
    intro i hi
    simpa [S] using hi
  have hT : ∀ i, i ∉ T → y i = z i := by
    intro i hi
    simpa [T] using hi
  have hdisjoint : Disjoint S T := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiT
    have hix : x i ≠ z i := (Finset.mem_filter.1 hiS).2
    have hiy : y i ≠ z i := (Finset.mem_filter.1 hiT).2
    rcases hzchoice i with h | h
    · exact hix h.symm
    · exact hiy h.symm
  have hunion : S ∪ T = Finset.univ.filter (fun i => x i ≠ y i) := by
    ext i
    rcases hzchoice i with h | h <;> simp [S, T, h, ne_comm]
  have hcard := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hcard
  rw [hcard]
  exact walk_append (corner_cost_walk a β z hzc S x hx hxc hzx hS)
    (walk_reverse (corner_cost_walk a β z hzc T y hy hyc hzy hT))

lemma retained_corners_walk
    (a : Fin d → ℝ) (β : ℝ) (x y : Fin d → ℝ)
    (hx : x ∈ Clip a β) (hy : y ∈ Clip a β)
    (hxc : Corner x) (hyc : Corner y) : Walk (Clip a β) d x y := by
  have hc : (Finset.univ.filter (fun i => x i ≠ y i)).card ≤ d := by
    simpa using Finset.card_le_card (Finset.filter_subset (fun i => x i ≠ y i) Finset.univ)
  exact walk_pad hc (retained_corners_hamming_walk a β x y hx hy hxc hyc)

#print axioms retained_corners_hamming_walk

end HirschCubeCut
