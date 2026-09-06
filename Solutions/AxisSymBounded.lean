import Mathlib
import Solutions.AxisSymExtremes

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisSym

variable {d n : ℕ}

lemma sym_constraints
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ)
    (hfg : f ≠ g)
    {z : EuclideanSpace ℝ (Fin (d + 1))}
    (hz : z ∈ Hpoly (symPerturbA c f g ε) (symPerturbB (n := n))) :
    let x := Hirsch.proj z
    let t := z (Fin.last d)
    ⟪c f, x⟫ + t ≤ 1 ∧
    ⟪c f, x⟫ - t ≤ 1 ∧
    ⟪c g, x⟫ + ε * t ≤ 1 ∧
    ∀ i, i ≠ f → i ≠ g → ⟪c i, x⟫ ≤ 1 := by
  dsimp
  have hf := hz f.castSucc
  have hlast := hz (Fin.last n)
  have hg := hz g.castSucc
  simp [symPerturbA_castSucc, symPerturbA_last, symPerturbB, hfg,
    inner_embed_any] at hf hlast hg
  refine ⟨hf, ?_, hg, ?_⟩
  · linarith
  · intro i hif hig
    have hi := hz i.castSucc
    simpa [symPerturbA_castSucc, symPerturbB, hif, hig, inner_embed_any] using hi

/-- A sufficiently small positive tilt of the symmetric wedge is bounded.
The proof is an explicit recession estimate specialized to the normalized
spindle coordinates. -/
lemma sym_bounded_small
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n)
    (u : EuclideanSpace ℝ (Fin d))
    (hfg : f ≠ g)
    (hbd : Bornology.IsBounded (Hpoly c (fun _ => (1 : ℝ))))
    (huP : u ∈ Hpoly c (fun _ => (1 : ℝ)))
    (hfu : ⟪c f, u⟫ = 1)
    (hgu : ⟪c g, u⟫ = -1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        Bornology.IsBounded (Hpoly (symPerturbA c f g ε) (symPerturbB (n := n))) := by
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hCold : ∀ x ∈ Hpoly c (fun _ => (1 : ℝ)), ‖x‖ ≤ C0 :=
    fun x hx => (hC x hx).trans (le_max_left _ _)
  let M : ℝ := 1 + ‖c f‖ * C0
  have hM1 : 1 ≤ M := by
    dsimp [M]
    have hprod : 0 ≤ ‖c f‖ * C0 := mul_nonneg (norm_nonneg _) hC0
    linarith
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  let δ : ℝ := 1 / M
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hε0 : 0 ≤ ε := hε.le
  have hεM : ε * M ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right hεδ hM.le
    have hδM : δ * M = 1 := by
      dsimp [δ]
      field_simp [hM.ne']
    linarith
  let X : ℝ := 2 * C0 + ‖u‖
  let T : ℝ := 2 * M
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  refine (isBounded_iff_forall_norm_le).2
    ⟨Real.sqrt (X ^ 2 + T ^ 2), fun z hz => ?_⟩
  let x := Hirsch.proj z
  let t := z (Fin.last d)
  have hc := sym_constraints c f g ε hfg hz
  dsimp at hc
  rcases hc with ⟨hfplus, hfminus, hgineq, hother⟩
  have hzid : z = Hirsch.embed x t := by
    exact (embed_proj z).symm
  have hnormz : ‖z‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
    rw [hzid]
    have hx : ‖Hirsch.embed x t‖ ^ 2 = ⟪Hirsch.embed x t, Hirsch.embed x t⟫ :=
      (real_inner_self_eq_norm_sq (Hirsch.embed x t)).symm
    have hy : ‖x‖ ^ 2 = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
    rw [hx, inner_embed, hy]
    ring
  have hbounds : ‖x‖ ≤ X ∧ -T ≤ t ∧ t ≤ T := by
    by_cases ht : 0 ≤ t
    · have hxP : x ∈ Hpoly c (fun _ => (1 : ℝ)) := by
        intro i
        by_cases hig : i = g
        · subst i
          nlinarith [mul_nonneg hε0 ht]
        · by_cases hif : i = f
          · subst i
            linarith
          · exact hother i hif hig
      have hxC : ‖x‖ ≤ C0 := hCold x hxP
      have hinnerabs : |⟪c f, x⟫| ≤ ‖c f‖ * ‖x‖ := abs_real_inner_le_norm _ _
      have hinnerC : |⟪c f, x⟫| ≤ ‖c f‖ * C0 :=
        hinnerabs.trans (mul_le_mul_of_nonneg_left hxC (norm_nonneg _))
      have htM : t ≤ M := by
        have hneg : -⟪c f, x⟫ ≤ |⟪c f, x⟫| := neg_le_abs _
        dsimp [M]
        linarith
      have hxX : ‖x‖ ≤ X := by
        dsimp [X]
        nlinarith [norm_nonneg u]
      have htT : t ≤ T := by
        dsimp [T]
        nlinarith [hM.le]
      have hnegT : -T ≤ t := by linarith
      exact ⟨hxX, hnegT, htT⟩
    · have htneg : t < 0 := lt_of_not_ge ht
      let s : ℝ := -t
      have hs : 0 < s := by dsimp [s]; linarith
      have hs0 : 0 ≤ s := hs.le
      let lam : ℝ := ε * s
      have hlam0 : 0 ≤ lam := mul_nonneg hε0 hs0
      let D : ℝ := 2 + lam
      have hD : 0 < D := by dsimp [D]; linarith
      have hfold : ⟪c f, x⟫ ≤ 1 := by linarith
      have hix : ∀ i, i ≠ g → ⟪c i, x⟫ ≤ 1 := by
        intro i hig
        by_cases hif : i = f
        · simpa [hif] using hfold
        · exact hother i hif hig
      have hgx : ⟪c g, x⟫ ≤ 1 + lam := by
        dsimp [lam, s]
        linarith
      let y : EuclideanSpace ℝ (Fin d) :=
        D⁻¹ • ((2 : ℝ) • x + lam • u)
      have hyP : y ∈ Hpoly c (fun _ => (1 : ℝ)) := by
        intro i
        have hnum : 2 * ⟪c i, x⟫ + lam * ⟪c i, u⟫ ≤ D := by
          by_cases hig : i = g
          · subst i
            have hu := hgu
            dsimp [D]
            nlinarith [hgx]
          · have hxi := hix i hig
            have hui := huP i
            dsimp [D]
            nlinarith [mul_nonneg hlam0 (sub_nonneg.2 hui)]
        have hinner : ⟪c i, y⟫ = D⁻¹ *
            (2 * ⟪c i, x⟫ + lam * ⟪c i, u⟫) := by
          simp [y, inner_smul_right, inner_add_right]
          ring
        rw [hinner]
        have hmul := mul_le_mul_of_nonneg_left hnum (inv_nonneg.2 hD.le)
        have hcancel : D⁻¹ * D = 1 := inv_mul_cancel₀ hD.ne'
        simpa [hcancel] using hmul
      have hyC : ‖y‖ ≤ C0 := hCold y hyP
      let A : ℝ := 1 - ⟪c f, y⟫
      have hA0 : 0 ≤ A := by
        have := hyP f
        dsimp [A]
        linarith
      have hinnerabs : |⟪c f, y⟫| ≤ ‖c f‖ * ‖y‖ := abs_real_inner_le_norm _ _
      have hinnerC : |⟪c f, y⟫| ≤ ‖c f‖ * C0 :=
        hinnerabs.trans (mul_le_mul_of_nonneg_left hyC (norm_nonneg _))
      have hAM : A ≤ M := by
        have hneg : -⟪c f, y⟫ ≤ |⟪c f, y⟫| := neg_le_abs _
        dsimp [A, M]
        linarith
      have hrel : D * ⟪c f, y⟫ = 2 * ⟪c f, x⟫ + lam := by
        have hinner : ⟪c f, y⟫ = D⁻¹ *
            (2 * ⟪c f, x⟫ + lam * ⟪c f, u⟫) := by
          simp [y, inner_smul_right, inner_add_right]
          ring
        rw [hfu] at hinner
        have := congrArg (fun q : ℝ => D * q) hinner
        field_simp [hD.ne'] at this
        simpa using this
      have hAε : A * ε ≤ 1 := by
        have h := mul_le_mul hAM hεδ hM.le hA0
        have hδM : M * δ = 1 := by
          dsimp [δ]
          field_simp [hM.ne']
        simpa [mul_comm, hδM] using h
      have hAεs : A * ε * s ≤ s := by
        have := mul_le_mul_of_nonneg_right hAε hs0
        simpa [mul_assoc] using this
      have hsM : s ≤ 2 * M := by
        dsimp [D, lam, A, s] at hrel hfminus
        have hAs : A ≤ M := hAM
        nlinarith
      have hlam2 : lam ≤ 2 := by
        dsimp [lam]
        have h := mul_le_mul_of_nonneg_left hsM hε0
        have hεM' : ε * M ≤ 1 := hεM
        nlinarith
      have hxy : (2 : ℝ) • x = D • y - lam • u := by
        dsimp [y]
        have hD0 : D ≠ 0 := hD.ne'
        module
      have hnorm2 : 2 * ‖x‖ ≤ D * ‖y‖ + lam * ‖u‖ := by
        calc
          2 * ‖x‖ = ‖(2 : ℝ) • x‖ := by simp
          _ = ‖D • y - lam • u‖ := by rw [hxy]
          _ ≤ ‖D • y‖ + ‖lam • u‖ := norm_sub_le _ _
          _ = D * ‖y‖ + lam * ‖u‖ := by
            simp [abs_of_nonneg hD.le, abs_of_nonneg hlam0]
      have hD4 : D ≤ 4 := by dsimp [D]; linarith
      have hnormX : ‖x‖ ≤ X := by
        have hDy : D * ‖y‖ ≤ 4 * C0 :=
          calc
            D * ‖y‖ ≤ D * C0 := mul_le_mul_of_nonneg_left hyC hD.le
            _ ≤ 4 * C0 := mul_le_mul_of_nonneg_right hD4 hC0
        have hlamu : lam * ‖u‖ ≤ 2 * ‖u‖ :=
          mul_le_mul_of_nonneg_right hlam2 (norm_nonneg u)
        dsimp [X]
        nlinarith
      have htlow : -T ≤ t := by
        dsimp [T, s] at hsM ⊢
        linarith
      have hthi : t ≤ T := by linarith [hT0]
      exact ⟨hnormX, htlow, hthi⟩
  rcases hbounds with ⟨hxX, htlo, hthi⟩
  have hx2 : ‖x‖ ^ 2 ≤ X ^ 2 := by
    nlinarith [norm_nonneg x, hX0]
  have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith
  have hsq : ‖z‖ ^ 2 ≤ X ^ 2 + T ^ 2 := by
    rw [hnormz]
    nlinarith
  have hnonneg : 0 ≤ X ^ 2 + T ^ 2 := by positivity
  rw [← Real.sqrt_sq (norm_nonneg z)]
  exact Real.sqrt_le_sqrt hsq

end HirschAxisSym
