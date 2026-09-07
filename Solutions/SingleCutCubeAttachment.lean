import Solutions.SingleCutCubeCorners
import Solutions.SingleCutCubeVertices

open Set Hirsch HirschClip

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschCubeCut

variable {d : ℕ}

/-- Each vertex of a cube cut by one arbitrary real halfspace is either an
original corner, or is joined to a retained original corner by one edge. -/
lemma vertex_corner_attachment (a : Fin d → ℝ) (β : ℝ)
    {x : Fin d → ℝ} (hx : x ∈ extremePoints ℝ (Clip a β)) :
    ∃ p : Fin d → ℝ, Corner p ∧ p ∈ Clip a β ∧ (p = x ∨ Adj (Clip a β) p x) := by
  classical
  by_cases hxc : Corner x
  · exact ⟨x, hxc, hx.1, Or.inl rfl⟩
  obtain ⟨i, hxp, hxm, hai, hcut, hother⟩ := noncorner_vertex_structure a β hx hxc
  let p : Fin d → ℝ := Function.update x i (if 0 ≤ a i then 0 else 1)
  have hpother : ∀ j, j ≠ i → p j = x j := by
    intro j hji
    simp [p, Function.update_of_ne hji]
  have hpc : Corner p := by
    intro j
    by_cases hji : j = i
    · subst j
      by_cases ha : 0 ≤ a i <;> simp [p, ha]
    · rw [hpother j hji]
      exact hother j hji
  have hpP : p ∈ Clip a β := by
    refine ⟨corner_mem_box hpc, ?_⟩
    change cost a (Function.update x i (if 0 ≤ a i then 0 else 1)) ≤ β
    rw [cost_update, hcut]
    by_cases ha : 0 ≤ a i
    · rw [if_pos ha]
      nlinarith [mul_nonneg ha hxp.le]
    · rw [if_neg ha]
      have han : a i < 0 := lt_of_not_ge ha
      nlinarith [mul_nonpos_of_nonpos_of_nonneg han.le (sub_nonneg.mpr hxm.le)]
  refine ⟨p, hpc, hpP, Or.inr ?_⟩
  have hpx : p ≠ x := by
    intro he
    have hi := congrFun he i
    by_cases ha : 0 ≤ a i
    · simp [p, ha] at hi
      linarith
    · simp [p, ha] at hi
      linarith
  refine ⟨hpx, (clip_convex a β).segment_subset hpP hx.1, ?_⟩
  intro r hr s hs z hz hop
  have hrfix : ∀ j, j ≠ i → r j = x j := by
    intro j hji
    have hzj : z j = x j := by
      obtain ⟨α, γ, hα, hγ, hαγ, heq⟩ := hz
      have hj := congrFun heq j
      change α * p j + γ * x j = z j at hj
      rw [hpother j hji, ← add_mul, hαγ, one_mul] at hj
      exact hj.symm
    have hzb : z j = 0 ∨ z j = 1 := by simpa only [hzj] using hother j hji
    exact (fixed_bound_left hr.1 hs.1 hop j hzb).trans hzj
  have hrupdate : r = Function.update x i (r i) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hji, hrfix j hji]
  have hcostr : cost a r = β + a i * (r i - x i) := by
    calc
      cost a r = cost a (Function.update x i (r i)) := congrArg (cost a) hrupdate
      _ = β + a i * (r i - x i) := by rw [cost_update, hcut]
  have hprod : a i * (r i - x i) ≤ 0 := by
    have hrle := hr.2
    rw [hcostr] at hrle
    linarith
  by_cases ha : 0 ≤ a i
  · have hapos : 0 < a i := lt_of_le_of_ne ha hai.symm
    have hrix : r i ≤ x i := by nlinarith
    let γ : ℝ := r i / x i
    have hγ0 : 0 ≤ γ := div_nonneg (hr.1 i).1 hxp.le
    have hγ1 : γ ≤ 1 := (div_le_iff₀ hxp).2 (by linarith)
    have hγx : γ * x i = r i := div_mul_cancel₀ _ hxp.ne'
    refine ⟨1 - γ, γ, by linarith, hγ0, by ring, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      change (1 - γ) * p i + γ * x i = r i
      rw [show p i = 0 by simp [p, ha]]
      linarith
    · change (1 - γ) * p j + γ * x j = r j
      rw [hpother j hji, hrfix j hji]
      ring
  · have han : a i < 0 := lt_of_not_ge ha
    have hxir : x i ≤ r i := by nlinarith
    let γ : ℝ := (1 - r i) / (1 - x i)
    have hden : 0 < 1 - x i := by linarith
    have hγ0 : 0 ≤ γ := div_nonneg (sub_nonneg.mpr (hr.1 i).2) hden.le
    have hγ1 : γ ≤ 1 := (div_le_iff₀ hden).2 (by linarith)
    have hγx : γ * (1 - x i) = 1 - r i := div_mul_cancel₀ _ hden.ne'
    refine ⟨1 - γ, γ, by linarith, hγ0, by ring, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      change (1 - γ) * p i + γ * x i = r i
      rw [show p i = 1 by simp [p, ha]]
      nlinarith
    · change (1 - γ) * p j + γ * x j = r j
      rw [hpother j hji, hrfix j hji]
      ring

#print axioms vertex_corner_attachment

end HirschCubeCut
