import Solutions.CircuitSourceBridge

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

/-- A feasible point supports a stationary padded circuit walk of any length. -/
theorem standardCircuitWalk_stationary {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c) (L : ℕ) :
    StandardCircuitWalk K c L v v := by
  refine ⟨fun _ => v, rfl, rfl, ?_, ?_⟩
  · intro _ _
    exact hv
  · intro _ _
    exact Or.inl rfl

/-- Concatenate two padded standard-form circuit walks. -/
theorem standardCircuitWalk_trans {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L M : ℕ} {u v z : Fin n → ℝ}
    (h₁ : StandardCircuitWalk K c L u v)
    (h₂ : StandardCircuitWalk K c M v z) :
    StandardCircuitWalk K c (L + M) u z := by
  obtain ⟨w₁, h10, h1L, hf₁, hs₁⟩ := h₁
  obtain ⟨w₂, h20, h2M, hf₂, hs₂⟩ := h₂
  let w : ℕ → (Fin n → ℝ) := fun j =>
    if j ≤ L then w₁ j else w₂ (j - L)
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · simp [w, h10]
  · by_cases hM0 : M = 0
    · subst M
      have hvz : v = z := by
        have := h2M
        rw [h20] at this
        exact this
      simp [w, h1L, hvz]
    · have hLM : ¬ L + M ≤ L := by omega
      simp [w, hLM, Nat.add_sub_cancel_left, h2M]
  · intro j hj
    by_cases hjL : j ≤ L
    · simp [w, hjL]
      exact hf₁ j hjL
    · simp [w, hjL]
      exact hf₂ (j - L) (by omega)
  · intro j hj
    by_cases hjlt : j < L
    · have hjL : j ≤ L := Nat.le_of_lt hjlt
      have hsuccL : j + 1 ≤ L := by omega
      simpa [w, hjL, hsuccL] using hs₁ j hjlt
    · have hjge : L ≤ j := Nat.le_of_not_gt hjlt
      by_cases hjEq : j = L
      · subst j
        have hMpos : 0 < M := by omega
        have hnotSucc : ¬ L + 1 ≤ L := by omega
        have hstep := hs₂ 0 hMpos
        have hleft : w L = v := by simp [w, h1L]
        have hright : w (L + 1) = w₂ 1 := by
          simp [w, hnotSucc]
        rw [hleft, hright, ← h20]
        exact hstep
      · have hjgt : L < j := lt_of_le_of_ne hjge (Ne.symm hjEq)
        have hjNot : ¬ j ≤ L := not_le_of_gt hjgt
        have hsNot : ¬ j + 1 ≤ L := by omega
        have hk : j - L < M := by omega
        simpa [w, hjNot, hsNot, Nat.add_sub_assoc hjge 1] using hs₂ (j - L) hk

/-- The padded standard-form circuit-walk predicate is monotone in its budget. -/
theorem standardCircuitWalk_mono {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ)
    {L M : ℕ} {u v : Fin n → ℝ}
    (h : StandardCircuitWalk K c L u v) (hLM : L ≤ M) :
    StandardCircuitWalk K c M u v := by
  obtain ⟨w, hw0, hwL, hf, hs⟩ := h
  have hv : v ∈ StandardSlice K c := by
    simpa [hwL] using hf L (le_rfl)
  have hstay := standardCircuitWalk_stationary K c v hv (M - L)
  have hcat := standardCircuitWalk_trans K c h hstay
  simpa [Nat.add_sub_of_le hLM] using hcat

/-- A single genuine standard circuit step gives a length-one walk. -/
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
    simp [w, h]

#print axioms standardCircuitWalk_stationary
#print axioms standardCircuitWalk_trans
#print axioms standardCircuitWalk_mono
#print axioms standardCircuitWalk_of_step

end HirschCircuit
