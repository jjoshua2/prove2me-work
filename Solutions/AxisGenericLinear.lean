import Mathlib

open Set

set_option maxHeartbeats 1000000

noncomputable section

namespace HirschAxisGeneric

/-- There is always a positive real smaller than a prescribed positive bound
and outside a given finite set. -/
lemma exists_pos_lt_notMem_finset
    (s : Finset ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ t : ℝ, 0 < t ∧ t < r ∧ t ∉ s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨r / 2, by linarith, by linarith, by simp⟩
  | @insert a s ha ih =>
      by_cases hapos : 0 < a
      · have hr' : 0 < min r a := lt_min hr hapos
        obtain ⟨t, ht0, htr', hts⟩ := ih hr'
        have htr : t < r := lt_of_lt_of_le htr' (min_le_left _ _)
        have hta : t < a := lt_of_lt_of_le htr' (min_le_right _ _)
        refine ⟨t, ht0, htr, ?_⟩
        simp [Finset.mem_insert, ne_of_lt hta, hts]
      · obtain ⟨t, ht0, htr, hts⟩ := ih hr
        have hta : t ≠ a := by
          intro h
          subst a
          exact hapos ht0
        refine ⟨t, ht0, htr, ?_⟩
        simp [Finset.mem_insert, hta, hts]

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
    have hden' : 0 < ‖z‖ + 1 := by positivity
    have h1 : λ * ‖z‖ < λ * (‖z‖ + 1) :=
      mul_lt_mul_of_pos_left (by linarith [norm_nonneg z]) hλ
    have hλbound : λ * (‖z‖ + 1) = r / 2 := by
      dsimp [λ]
      field_simp [hden'.ne']
      ring
    linarith
  refine ⟨λ • z, hnorm, ?_⟩
  intro i hmem
  have hback : z ∈ p i := by
    have hs := (p i).smul_mem λ⁻¹ hmem
    simpa [smul_smul, hλ.ne'] using hs
  exact hz i hback

/-- More useful dense form: near any prescribed point, one can avoid a finite
family of proper linear subspaces.  The line direction avoids every subspace,
so each subspace excludes at most one scalar on the line; a finite set of
scalars can then be avoided while staying arbitrarily close. -/
lemma exists_near_avoid_finite_submodules
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Finite ι]
    (p : ι → Submodule ℝ E)
    (hp : ∀ i, p i ≠ ⊤)
    (x0 : E) {r : ℝ} (hr : 0 < r) :
    ∃ x : E, ‖x - x0‖ < r ∧ ∀ i, x ∉ p i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨z, hz⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  have hunique (i : ι) {s t : ℝ}
      (hs : x0 + s • z ∈ p i) (ht : x0 + t • z ∈ p i) : s = t := by
    have hsub : (s - t) • z ∈ p i := by
      have h := (p i).sub_mem hs ht
      convert h using 1 <;> module
    by_contra hst
    have hst0 : s - t ≠ 0 := sub_ne_zero.mpr hst
    have hzmem : z ∈ p i := by
      have h := (p i).smul_mem (s - t)⁻¹ hsub
      simpa [smul_smul, hst0] using h
    exact hz i hzmem
  let bad : ι → ℝ := fun i =>
    if h : ∃ t : ℝ, x0 + t • z ∈ p i then Classical.choose h else 0
  let F : Finset ℝ := Finset.univ.image bad
  let R : ℝ := r / (‖z‖ + 1)
  have hR : 0 < R := div_pos hr (by positivity)
  obtain ⟨t, ht0, htR, htF⟩ := exists_pos_lt_notMem_finset F hR
  have havoid : ∀ i, x0 + t • z ∉ p i := by
    intro i hmem
    have hex : ∃ q : ℝ, x0 + q • z ∈ p i := ⟨t, hmem⟩
    have hbadmem : x0 + bad i • z ∈ p i := by
      dsimp [bad]
      rw [dif_pos hex]
      exact Classical.choose_spec hex
    have hteq : t = bad i := hunique i hmem hbadmem
    have hbF : bad i ∈ F := by
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩
    exact htF (hteq ▸ hbF)
  refine ⟨x0 + t • z, ?_, havoid⟩
  have hden : 0 < ‖z‖ + 1 := by positivity
  have h1 : t * ‖z‖ < t * (‖z‖ + 1) :=
    mul_lt_mul_of_pos_left (by linarith [norm_nonneg z]) ht0
  have h2 : t * (‖z‖ + 1) < R * (‖z‖ + 1) :=
    mul_lt_mul_of_pos_right htR hden
  have hRcancel : R * (‖z‖ + 1) = r := by
    dsimp [R]
    field_simp [hden.ne']
  rw [show x0 + t • z - x0 = t • z by module, norm_smul,
    Real.norm_eq_abs, abs_of_pos ht0]
  linarith

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

/-- Dense subtype form, used in coefficient space around a positive
barycentric point. -/
lemma exists_near_generic_in
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Submodule ℝ E)
    {ι : Type*} [Finite ι]
    (p : ι → Submodule ℝ D)
    (hp : ∀ i, p i ≠ ⊤)
    (x0 : D) {r : ℝ} (hr : 0 < r) :
    ∃ x : D, ‖x - x0‖ < r ∧ ∀ i, x ∉ p i :=
  exists_near_avoid_finite_submodules p hp x0 hr

end HirschAxisGeneric
