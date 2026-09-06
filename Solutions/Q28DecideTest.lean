import Solutions.Q28Cert

set_option maxHeartbeats 4000000

lemma popcount28_eq_filter (m : ℕ) :
    popcount28 m =
      (Finset.univ.filter (fun i : Fin 28 => m.testBit i.val)).card := by
  rw [Finset.card_filter]
  trans ∑ i : Fin 28, (if m.testBit i.val then 1 else 0)
  · unfold popcount28
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_succ]
    rw [Fin.sum_univ_zero]
    simp only [Fin.val_succ, Fin.val_zero]
    rfl
  · rfl
