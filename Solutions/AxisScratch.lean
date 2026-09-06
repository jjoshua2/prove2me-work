import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_wedge

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisScratch

variable {d n : ℕ}

lemma embed_castSucc (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) (i : Fin d) :
    Hirsch.embed x t i.castSucc = x i := by
  simp [Hirsch.embed, Fin.snoc_castSucc]

lemma embed_last (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Hirsch.embed x t (Fin.last d) = t := by
  simp [Hirsch.embed, Fin.snoc_last]

lemma inner_embed (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    ⟪Hirsch.embed x t, Hirsch.embed y s⟫ = ⟪x, y⟫ + t * s := by
  simp [Hirsch.embed, inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- Preliminary one-sided coordinate model.  This is kept only as a small
incidence sanity-check while the source-faithful symmetric perturbed wedge is
formalized below. -/
noncomputable def stepA
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)) :=
  Fin.snoc
    (fun i =>
      if i = g then Hirsch.embed (c i) 1
      else if i = f then Hirsch.embed (c i) 1
      else Hirsch.embed (c i) 0)
    (Hirsch.embed 0 (-1))

noncomputable def stepB (g : Fin n) : Fin (n + 1) → ℝ :=
  Fin.snoc (fun i => if i = g then 2 else 1) 0

lemma stepA_castSucc (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g i : Fin n) :
    stepA c f g i.castSucc =
      if i = g then Hirsch.embed (c i) 1
      else if i = f then Hirsch.embed (c i) 1
      else Hirsch.embed (c i) 0 := by
  simp [stepA, Fin.snoc_castSucc]

lemma stepA_last (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) :
    stepA c f g (Fin.last n) = Hirsch.embed 0 (-1) := by
  simp [stepA, Fin.snoc_last]

lemma stepB_castSucc (g i : Fin n) :
    stepB g i.castSucc = if i = g then 2 else 1 := by
  simp [stepB, Fin.snoc_castSucc]

lemma stepB_last (g : Fin n) : stepB g (Fin.last n) = 0 := by
  simp [stepB, Fin.snoc_last]

lemma step_spindle_incidence
    (c : Fin n → EuclideanSpace ℝ (Fin d))
    (u v : EuclideanSpace ℝ (Fin d)) (f g : Fin n)
    (hUle : ∀ i, ⟪c i, u⟫ ≤ 1)
    (hVle : ∀ i, ⟪c i, v⟫ ≤ 1)
    (hxor : ∀ i, (⟪c i, u⟫ = 1) ↔ ⟪c i, v⟫ ≠ 1)
    (hanti : ∀ i, ⟪c i, v⟫ = -⟪c i, u⟫)
    (hf : ⟪c f, u⟫ = 1)
    (hg : ⟪c g, v⟫ = 1) :
    let U := Hirsch.embed u 0
    let V := Hirsch.embed v 1
    U ∈ Hpoly (stepA c f g) (stepB g) ∧
    V ∈ Hpoly (stepA c f g) (stepB g) ∧
    ∀ j, (⟪stepA c f g j, U⟫ = stepB g j) ↔
      ⟪stepA c f g j, V⟫ ≠ stepB g j := by
  have hfv : ⟪c f, v⟫ = -1 := by simpa [hf] using hanti f
  have hgu : ⟪c g, u⟫ = -1 := by
    have h := hanti g
    linarith
  have hfg : f ≠ g := by
    intro h
    subst g
    linarith [hf, hg, hanti f]
  dsimp
  constructor
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · simp [stepA_last, stepB_last, inner_embed]
    · intro i
      simp only [stepA_castSucc, stepB_castSucc]
      by_cases hig : i = g
      · subst i
        simp [inner_embed, hgu]
        norm_num
      · by_cases hif : i = f
        · subst i
          simp [hig, inner_embed, hf]
        · simp [hig, hif, inner_embed]
          exact hUle i
  · constructor
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simp [stepA_last, stepB_last, inner_embed]
      · intro i
        simp only [stepA_castSucc, stepB_castSucc]
        by_cases hig : i = g
        · subst i
          simp [inner_embed, hg]
          norm_num
        · by_cases hif : i = f
          · subst i
            simp [hig, inner_embed, hfv]
          · simp [hig, hif, inner_embed]
            exact hVle i
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simp [stepA_last, stepB_last, inner_embed]
      · intro i
        simp only [stepA_castSucc, stepB_castSucc]
        by_cases hig : i = g
        · subst i
          simp [inner_embed, hg, hgu]
          norm_num
        · by_cases hif : i = f
          · subst i
            simp [hig, inner_embed, hf, hfv]
          · rw [if_neg hig, if_neg hif, if_neg hig]
            simpa [inner_embed] using hxor i

end HirschAxisScratch
