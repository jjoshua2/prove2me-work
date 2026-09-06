import Mathlib

open Set

set_option maxHeartbeats 1000000

noncomputable section

namespace HirschAxisGeneric

/-- Over `ℝ`, finitely many proper linear subspaces cannot cover even an
arbitrarily small ball around the origin.  This is the scale-down form needed
for Klee's generic push. -/
lemma exists_small_avoid_finite_submodules
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Finite ι]
    (p : ι → Submodule ℝ E)
    (hp : ∀ i, p i ≠ ⊤)
    {r : ℝ} (hr : 0 < r) :
    ∃ x : E, ‖x‖ < r ∧ ∀ i, x ∉ p i := by
  obtain ⟨z, hz⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  let λ : ℝ := r / (2 * (‖z‖ + 1))
  have hden : 0 < 2 * (‖z‖ + 1) := by positivity
  have hλ : 0 < λ := div_pos hr hden
  have hnorm : ‖λ • z‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hλ]
    apply (div_lt_iff₀ hden).2
    dsimp [λ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith [norm_nonneg z, mul_pos hr hden]
  refine ⟨λ • z, hnorm, ?_⟩
  intro i hmem
  have hback : z ∈ p i := by
    have hs := (p i).smul_mem λ⁻¹ hmem
    simpa [smul_smul, hλ.ne'] using hs
  exact hz i hback

/-- Subtype form: inside a fixed subspace `D`, finitely many proper subspaces
of `D` can be simultaneously avoided by an arbitrarily small vector. -/
lemma exists_small_generic_in
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Submodule ℝ E)
    {ι : Type*} [Finite ι]
    (p : ι → Submodule ℝ D)
    (hp : ∀ i, p i ≠ ⊤)
    {r : ℝ} (hr : 0 < r) :
    ∃ h : D, ‖h‖ < r ∧ ∀ i, h ∉ p i :=
  exists_small_avoid_finite_submodules p hp hr

end HirschAxisGeneric
