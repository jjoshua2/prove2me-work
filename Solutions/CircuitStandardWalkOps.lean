import Solutions.CircuitSourceBridge

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

theorem standardCircuitWalk_stationary {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c) (L : ℕ) :
    StandardCircuitWalk K c L v v := by
  exact ⟨fun _ => v, rfl, rfl, fun _ _ => hv, fun _ _ => Or.inl rfl⟩

/-- Concatenate padded walks, using the common endpoint at the junction. -/
theorem standardCircuitWalk_trans {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L M : ℕ} {u v z : Fin n → ℝ}
    (h₁ : StandardCircuitWalk K c L u v)
    (h₂ : StandardCircuitWalk K c M v z) :
    StandardCircuitWalk K c (L + M) u z := by
  obtain ⟨w₁, h10, h1L, hf₁, hs₁⟩ := h₁
  obtain ⟨w₂, h20, h2M, hf₂, hs₂⟩ := h₂
  let w : ℕ → (Fin n → ℝ) := fun j =>
    if j < L then w₁ j else w₂ (j - L)
  have hfirst : ∀ j, j ≤ L → w j = w₁ j := by
    intro j hj
    by_cases hjlt : j < L
    · simp only [w, if_pos hjlt]
    · have hjEq : j = L := by omega
      subst j
      simp [w, h20, h1L]
  have hsecond : ∀ j, L ≤ j → w j = w₂ (j - L) := by
    intro j hj
    simp only [w, if_neg (not_lt_of_ge hj)]
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · rw [hfirst 0 (Nat.zero_le _), h10]
  · rw [hsecond (L + M) (by omega), Nat.add_sub_cancel_left, h2M]
  · intro j hj
    by_cases hjL : j ≤ L
    · rw [hfirst j hjL]
      exact hf₁ j hjL
    · rw [hsecond j (by omega)]
      exact hf₂ (j - L) (by omega)
  · intro j hj
    by_cases hjL : j < L
    · rw [hfirst j (by omega), hfirst (j + 1) (by omega)]
      exact hs₁ j hjL
    · have hjge : L ≤ j := by omega
      rw [hsecond j hjge, hsecond (j + 1) (by omega)]
      have hidx : j + 1 - L = (j - L) + 1 := by omega
      rw [hidx]
      exact hs₂ (j - L) (by omega)

theorem standardCircuitWalk_mono {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L M : ℕ} {u v : Fin n → ℝ}
    (h : StandardCircuitWalk K c L u v) (hLM : L ≤ M) :
    StandardCircuitWalk K c M u v := by
  have hv : v ∈ StandardSlice K c := by
    obtain ⟨w, _, hwL, hf, _⟩ := h
    simpa only [hwL] using hf L (le_rfl)
  have hstay := standardCircuitWalk_stationary K c v hv (M - L)
  have hcat := standardCircuitWalk_trans K c h hstay
  simpa only [Nat.add_sub_of_le hLM] using hcat

theorem standardCircuitWalk_of_step {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x y : Fin n → ℝ)
    (h : StandardCircuitStep K c x y) :
    StandardCircuitWalk K c 1 x y := by
  let w : ℕ → (Fin n → ℝ) := fun j => if j = 0 then x else y
  refine ⟨w, by simp [w], by simp [w], ?_, ?_⟩
  · intro j hj
    interval_cases j <;> simp [w, h.1, h.2.1]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    right
    simpa only [w, if_pos rfl, Nat.zero_add, if_neg (by decide : ¬(1 : ℕ) = 0)] using h

#print axioms standardCircuitWalk_stationary
#print axioms standardCircuitWalk_trans
#print axioms standardCircuitWalk_mono
#print axioms standardCircuitWalk_of_step
end HirschCircuit
