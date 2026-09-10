import Solutions.CircuitSourceBridge
import Solutions.CircuitAugmentation

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace HirschCircuit

/-- Turn a positive maximal nonnegative augmentation along an elementary
subspace direction into the exact `StandardCircuitStep` relation. -/
theorem standardCircuitStep_of_maximal_direction {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x g : Fin n → ℝ) (α : ℝ)
    (hx : x ∈ StandardSlice K c)
    (hgelem : IsElementaryIn K g)
    (hα : 0 < α)
    (hfeas : ∀ i, 0 ≤ x i + α * g i)
    (hmax : ∀ β : ℝ, α < β → ∃ i, x i + β * g i < 0) :
    StandardCircuitStep K c x (x + α • g) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  refine ⟨hx, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hK : (x + α • g) - c = (x - c) + α • g := by
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hK]
      exact K.add_mem hx.1 (K.smul_mem α hgelem.2.1)
    · intro i
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hfeas i
  · have hscale : x - (x + α • g) = (-α) • g := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hscale]
    exact isElementaryIn_smul K hgelem (neg_ne_zero.mpr hαne)
  · intro t ht hmem
    have hβ : α < t * α := by
      nlinarith [hα]
    obtain ⟨i, hi⟩ := hmax (t * α) hβ
    have hnonneg := hmem.2 i
    have heq :
        (x + t • ((x + α • g) - x)) i = x i + (t * α) * g i := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    rw [heq] at hnonneg
    linarith

/-- If an elementary direction is safe at every currently zero coordinate and
negative somewhere, its finite blocking ratio gives a genuine positive maximal
`StandardCircuitStep`. -/
theorem exists_standardCircuitStep_along_elementary {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c x g : Fin n → ℝ)
    (hx : x ∈ StandardSlice K c)
    (hgelem : IsElementaryIn K g)
    (hzero : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ α : ℝ, 0 < α ∧
      StandardCircuitStep K c x (x + α • g) ∧
      (∀ i, 0 ≤ x i + α * g i) ∧
      (∃ q, g q < 0 ∧ x q + α * g q = 0) := by
  obtain ⟨α, hα, hfeas, hsat, hmax⟩ :=
    exists_positive_maximal_nonnegative_step x g hx.2 hzero hneg
  refine ⟨α, hα, ?_, hfeas, hsat⟩
  exact standardCircuitStep_of_maximal_direction K c x g α hx hgelem hα hfeas hmax

#print axioms standardCircuitStep_of_maximal_direction
#print axioms exists_standardCircuitStep_along_elementary

end HirschCircuit
