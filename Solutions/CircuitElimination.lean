import Mathlib
import Solutions.CircuitNormReduction

open Set HirschSlack HirschCircuitProgress HirschAugment HirschConformal HirschCircuitNorm

set_option maxHeartbeats 6000000

noncomputable section

namespace HirschCircuitElimination

/-- The second source operation is also constructive. Given the ghost-point
geometry, an elementary maximal step preserves trapped bounds and zeros a
previously positive coordinate outside the trapped set. -/
theorem exists_eliminating_circuit_step
    (n : ℕ) (K : Submodule ℝ (Fin n → ℝ)) (b x ref v : Fin n → ℝ)
    (T N : Finset (Fin n)) (M lambda eta : ℝ)
    (hM : 2 ≤ M) (hn : (n : ℝ) ≤ M)
    (hx : x ∈ standardSet K b)
    (hr : ref ∈ standardSet K b) (hv : v ∈ standardSet K b)
    (hl : 0 ≤ lambda) (he : 0 ≤ eta)
    (hprotect : eta * M ≤ lambda / 2)
    (hsmall : (lambda + eta) * M ^ 2 ≤ 5 / 16)
    (hxt : ∀ i ∈ T, x i ≤ M * v i)
    (hrt : ∀ i ∈ T, ref i ≤ M * v i)
    (htangent : ∀ i, x i = 0 →
      0 ≤ lambda * (v i - x i) + eta * (x i - ref i))
    (hN : ∀ i ∈ N, lambda * (v i - x i) + eta * (x i - ref i) ≤ 0)
    (q : Fin n) (hxq : 0 < x q)
    (hq : lambda * (v q - x q) + eta * (x q - ref q) = -x q) :
    ∃ y : Fin n → ℝ,
      StandardStep K b x y ∧
      (∀ i ∈ T, y i ≤ M * v i) ∧
      (∀ i ∈ N, y i ≤ x i) ∧
      ∃ j, 0 < x j ∧ y j = 0 ∧ j ∉ T := by
  let delta : Fin n → ℝ := lambda • (v - x) + eta • (x - ref)
  have hdK : delta ∈ K := by
    have h1 : v - x ∈ K := by
      have h := K.sub_mem hv.1 hx.1
      convert h using 1 <;> module
    have h2 : x - ref ∈ K := by
      have h := K.sub_mem hx.1 hr.1
      convert h using 1 <;> module
    exact K.add_mem (K.smul_mem lambda h1) (K.smul_mem eta h2)
  obtain ⟨parts, hsum, hlen, hparts⟩ := exists_conformal_decomposition K delta hdK
  let gain : (Fin n → ℝ) →ₗ[ℝ] ℝ := -(LinearMap.proj q)
  have hgapply : ∀ z : Fin n → ℝ, gain z = -z q := fun _ => rfl
  have hS : (parts.map gain).sum = x q := by
    rw [← map_list_sum gain, hsum, hgapply]
    change -(lambda * (v q - x q) + eta * (x q - ref q)) = x q
    rw [hq, neg_neg]
  obtain ⟨g, hgparts, hgainpos, hgain⟩ := large_list_summand parts gain M
    ((Nat.cast_le.mpr hlen).trans hn) (by rw [hS]; exact hxq)
  have hgE := (hparts g hgparts).1
  have hgconf := (hparts g hgparts).2
  have hgq : g q < 0 := by
    rw [hgapply] at hgainpos
    linarith
  have hgtangent : ∀ i, x i = 0 → 0 ≤ g i := by
    intro i hxi
    exact ((conformal_bounds hgconf i).1 (htangent i hxi)).1
  obtain ⟨alpha, ha, hstep, ⟨j, hgj, hxj, hyj⟩, _⟩ :=
    elementary_maximal_step K b x g hx hgE hgtangent ⟨q, hgq⟩
  have halpha : alpha ≤ M := by
    have hfeas := hstep.2.1.2 q
    change 0 ≤ x q + alpha * g q at hfeas
    rw [hS, hgapply] at hgain
    nlinarith
  have htrap : ∀ i ∈ T,
      (x + alpha • g) i ≤ M * v i ∧
      (0 < x i → 0 < (x + alpha • g) i) := by
    intro i hi
    exact elimination_trapped_coordinate M alpha lambda eta (x i) (ref i) (v i) (g i)
      hM ha.le halpha hl he hprotect hsmall (hx.2 i) (hr.2 i) (hv.2 i)
      (hxt i hi) (hrt i hi) (hgconf i)
  refine ⟨x + alpha • g, hstep, fun i hi => (htrap i hi).1, ?_, j, hxj, hyj, ?_⟩
  · intro i hi
    have hgi : g i ≤ 0 := ((conformal_bounds hgconf i).2 (hN i hi)).2
    change x i + alpha * g i ≤ x i
    have hprod := mul_nonpos_of_nonneg_of_nonpos ha.le hgi
    linarith
  · intro hjT
    have hpos := (htrap j hjT).2 hxj
    rw [hyj] at hpos
    exact (lt_irrefl 0) hpos

#print axioms exists_eliminating_circuit_step

end HirschCircuitElimination
