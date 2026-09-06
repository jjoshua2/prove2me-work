import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Module Hirsch

noncomputable section

namespace HirschAxisActive

variable {d n : ℕ}

/-- A displacement orthogonal to every tight normal at an extreme point
vanishes.  This is the finite-slack argument already used in the proved
`spindle_n_ge_two_d` solution, copied here because the helper itself was not
published as a platform theorem. -/
lemma extreme_tight_orthogonal
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hy : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    y = 0 := by
  by_contra hy0
  have hxP : x ∈ Hpoly a b := hx.1
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, x⟫ ≠ b i)
  by_cases hS : S = ∅
  · have hyi : ∀ i, ⟪a i, y⟫ = 0 := by
      intro i
      apply hy
      by_contra hne
      have hi : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩
      rw [hS] at hi
      exact Finset.notMem_empty i hi
    have hp1 : x + y ∈ Hpoly a b := by
      intro i
      simpa [inner_add_right, hyi i] using hxP i
    have hp2 : x - y ∈ Hpoly a b := by
      intro i
      simpa [inner_sub_right, hyi i] using hxP i
    have hop : x ∈ openSegment ℝ (x - y) (x + y) := mem_openSegment_sub_add x y
    have heq : x - y = x := hx.2 hp2 hp1 hop
    have : (x - y) + y = x + y := by rw [heq]
    have hyz : y = 0 := by simpa using this
    exact hy0 hyz
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
    let δ : ℝ := S.inf' hSne (fun i => b i - ⟪a i, x⟫)
    have hδ : 0 < δ := by
      obtain ⟨iδ, hiδ, hδeq⟩ := S.exists_mem_eq_inf' hSne (fun i => b i - ⟪a i, x⟫)
      have hne : ⟪a iδ, x⟫ ≠ b iδ := (Finset.mem_filter.1 hiδ).2
      have : 0 < b iδ - ⟪a iδ, x⟫ :=
        sub_pos.2 (lt_of_le_of_ne (hxP iδ) hne)
      simpa [δ, hδeq] using this
    let C : ℝ := ∑ i, |⟪a i, y⟫|
    have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
    let ε : ℝ := δ / (2 * (C + 1))
    have hεpos : 0 < ε := div_pos hδ (by positivity)
    have hεC : ε * C ≤ δ / 2 := by
      have hle : C ≤ C + 1 := by linarith
      have hle' : ε * C ≤ ε * (C + 1) := mul_le_mul_of_nonneg_left hle hεpos.le
      have hden : (2 * (C + 1) : ℝ) ≠ 0 := by positivity
      have heq : ε * (C + 1) = δ / 2 := by
        dsimp [ε]
        field_simp [hden]
      linarith
    have hmem (σ : ℝ) (hσabs : |σ| = ε) : x + σ • y ∈ Hpoly a b := by
      intro i
      have hinner : ⟪a i, x + σ • y⟫ = ⟪a i, x⟫ + σ * ⟪a i, y⟫ := by
        simp [inner_add_right, inner_smul_right]
      rw [hinner]
      by_cases ht : ⟪a i, x⟫ = b i
      · have hz : ⟪a i, y⟫ = 0 := hy i ht
        simp [ht, hz]
      · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩
        have hslack : δ ≤ b i - ⟪a i, x⟫ := Finset.inf'_le _ hiS
        have habs : |σ * ⟪a i, y⟫| ≤ ε * C := by
          have h1 : |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := by
            simp [abs_mul, hσabs]
          have h2 : |⟪a i, y⟫| ≤ C :=
            Finset.single_le_sum (f := fun j : Fin n => |⟪a j, y⟫|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
          calc
            |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := h1
            _ ≤ ε * C := mul_le_mul_of_nonneg_left h2 hεpos.le
        have hraw : σ * ⟪a i, y⟫ ≤ |σ * ⟪a i, y⟫| := le_abs_self _
        linarith
    have hp1 : x + ε • y ∈ Hpoly a b := hmem ε (abs_of_pos hεpos)
    have hp2 : x - ε • y ∈ Hpoly a b := by
      simpa [sub_eq_add_neg, neg_smul] using hmem (-ε) (by simp [abs_of_pos hεpos])
    have hop : x ∈ openSegment ℝ (x - ε • y) (x + ε • y) :=
      mem_openSegment_sub_add x (ε • y)
    have heq : x - ε • y = x := hx.2 hp2 hp1 hop
    have hyε : ε • y = 0 := by
      have : (x - ε • y) + ε • y = x + ε • y := by rw [heq]
      simpa using this
    exact hy0 ((smul_eq_zero.1 hyε).resolve_left hεpos.ne')

/-- In a `d`-dimensional space, from more than `d` active normals one can
remove at least one while keeping the common annihilator trivial. -/
lemma exists_removable_active
    (c : Fin n → EuclideanSpace ℝ (Fin d))
    (active : Finset (Fin n))
    (hcard : d < active.card)
    (holdzero : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, i ∈ active → ⟪c i, y⟫ = 0) → y = 0) :
    ∃ g, g ∈ active ∧
      ∀ y : EuclideanSpace ℝ (Fin d),
        (∀ i, i ∈ active → i ≠ g → ⟪c i, y⟫ = 0) → y = 0 := by
  classical
  let F : (active → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    { toFun := fun q => ∑ i : active, q i • c i.1
      map_add' := by
        intro q r
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro s q
        simp [Pi.smul_apply, Finset.smul_sum, mul_smul] }
  have hnotinj : ¬ Function.Injective F := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdom : Module.finrank ℝ (active → ℝ) = active.card := by
      simp [Fintype.card_coe]
    have hcod : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    rw [hdom, hcod] at hle
    omega
  have hker : F.ker ≠ ⊥ := by
    intro hk
    apply hnotinj
    rw [← LinearMap.ker_eq_bot]
    exact hk
  obtain ⟨q, hqker, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hex : ∃ ig : active, q ig ≠ 0 := by
    by_contra h
    push Not at h
    apply hq0
    funext i
    exact h i
  obtain ⟨ig, higq⟩ := hex
  let g : Fin n := ig.1
  have hgmem : g ∈ active := ig.2
  refine ⟨g, hgmem, ?_⟩
  intro y hy
  have hsum : (∑ i : active, q i * ⟪c i.1, y⟫) = 0 := by
    have hF0 : F q = 0 := LinearMap.mem_ker.1 hqker
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin d) => ⟪z, y⟫) hF0
    simpa [F, sum_inner, real_inner_smul_left] using h
  have hsingle : (∑ i : active, q i * ⟪c i.1, y⟫) =
      q ig * ⟪c g, y⟫ := by
    apply Finset.sum_eq_single ig
    · intro j hj hji
      have hjne : j.1 ≠ g := by
        intro heq
        apply hji
        apply Subtype.ext
        exact heq
      have hz := hy j.1 j.2 hjne
      simp [hz]
    · simp
  have hgorth : ⟪c g, y⟫ = 0 := by
    have : q ig * ⟪c g, y⟫ = 0 := by linarith [hsum, hsingle]
    exact (mul_eq_zero.mp this).resolve_left higq
  apply holdzero y
  intro i hi
  by_cases hig : i = g
  · simpa [hig] using hgorth
  · exact hy i hi hig

end HirschAxisActive
