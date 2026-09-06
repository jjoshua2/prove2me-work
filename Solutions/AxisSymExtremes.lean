import Mathlib
import Solutions.AxisSymScratch

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisSym

variable {d n : ℕ}

lemma inner_embed_any
    (c : EuclideanSpace ℝ (Fin d)) (s : ℝ)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    ⟪Hirsch.embed c s, z⟫ =
      ⟪c, Hirsch.proj z⟫ + s * z (Fin.last d) := by
  calc
    ⟪Hirsch.embed c s, z⟫ =
        ⟪Hirsch.embed c s, Hirsch.embed (Hirsch.proj z) (z (Fin.last d))⟫ := by
          rw [embed_proj z]
    _ = ⟪c, Hirsch.proj z⟫ + s * z (Fin.last d) := inner_embed _ _ _ _

lemma embed_zero_zero : Hirsch.embed (0 : EuclideanSpace ℝ (Fin d)) 0 = 0 := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [embed_last]
  · intro j
    simp [embed_castSucc]

/-- At the endpoint incident to the wedge foot, the two copies of the foot
facet have opposite new-coordinate coefficients.  They force the new
displacement coordinate to vanish, after which old extremality finishes. -/
lemma foot_apex_extreme
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hxle : ∀ i, ⟪c i, x⟫ ≤ 1)
    (hf : ⟪c f, x⟫ = 1)
    (hgnot : ⟪c g, x⟫ ≠ 1)
    (holdzero : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪c i, x⟫ = 1 → ⟪c i, y⟫ = 0) → y = 0) :
    Hirsch.embed x 0 ∈
      extremePoints ℝ (Hpoly (symPerturbA c f g ε) (symPerturbB (n := n))) := by
  apply extreme_of_active_orthogonal
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [symPerturbB, sym_inner_last_zero] using hxle f
    · intro i
      simpa [symPerturbB, sym_inner_castSucc_zero] using hxle i
  · intro z hz
    let y := Hirsch.proj z
    let t := z (Fin.last d)
    have hfg : f ≠ g := by
      intro h
      subst g
      exact hgnot hf
    have hplus : ⟪c f, y⟫ + t = 0 := by
      have hactive :
          ⟪symPerturbA c f g ε f.castSucc, Hirsch.embed x 0⟫ =
            symPerturbB (n := n) f.castSucc := by
        simpa [symPerturbB, sym_inner_castSucc_zero] using hf
      have h := hz f.castSucc hactive
      rw [symPerturbA_castSucc] at h
      simp [hfg, inner_embed_any] at h
      exact h
    have hminus : ⟪c f, y⟫ - t = 0 := by
      have hactive :
          ⟪symPerturbA c f g ε (Fin.last n), Hirsch.embed x 0⟫ =
            symPerturbB (n := n) (Fin.last n) := by
        simpa [symPerturbB, sym_inner_last_zero] using hf
      have h := hz (Fin.last n) hactive
      rw [symPerturbA_last, inner_embed_any] at h
      dsimp [y, t] at h
      linarith
    have ht : t = 0 := by linarith
    have hyactive : ∀ i, ⟪c i, x⟫ = 1 → ⟪c i, y⟫ = 0 := by
      intro i hi
      have hig : i ≠ g := by
        intro h
        subst i
        exact hgnot hi
      have hactive :
          ⟪symPerturbA c f g ε i.castSucc, Hirsch.embed x 0⟫ =
            symPerturbB (n := n) i.castSucc := by
        simpa [symPerturbB, sym_inner_castSucc_zero] using hi
      have h := hz i.castSucc hactive
      rw [symPerturbA_castSucc] at h
      by_cases hif : i = f
      · subst i
        simp [hig, inner_embed_any, ht] at h
        exact h
      · simp [hig, hif, inner_embed_any] at h
        exact h
    have hy : y = 0 := holdzero y hyactive
    calc
      z = Hirsch.embed y t := (embed_proj z).symm
      _ = Hirsch.embed 0 0 := by rw [hy, ht]
      _ = 0 := embed_zero_zero

/-- At the endpoint whose active facet `g` is tilted, all the other active
normals first kill the old-coordinate displacement.  The nonzero tilt of `g`
then kills the new coordinate. -/
lemma perturbed_apex_extreme
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hxle : ∀ i, ⟪c i, x⟫ ≤ 1)
    (hg : ⟪c g, x⟫ = 1)
    (hfnot : ⟪c f, x⟫ ≠ 1)
    (hε : ε ≠ 0)
    (hrem : ∀ y : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪c i, x⟫ = 1 → i ≠ g → ⟪c i, y⟫ = 0) → y = 0) :
    Hirsch.embed x 0 ∈
      extremePoints ℝ (Hpoly (symPerturbA c f g ε) (symPerturbB (n := n))) := by
  apply extreme_of_active_orthogonal
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [symPerturbB, sym_inner_last_zero] using hxle f
    · intro i
      simpa [symPerturbB, sym_inner_castSucc_zero] using hxle i
  · intro z hz
    let y := Hirsch.proj z
    let t := z (Fin.last d)
    have hyactive : ∀ i, ⟪c i, x⟫ = 1 → i ≠ g → ⟪c i, y⟫ = 0 := by
      intro i hi hig
      have hif : i ≠ f := by
        intro h
        subst i
        exact hfnot hi
      have hactive :
          ⟪symPerturbA c f g ε i.castSucc, Hirsch.embed x 0⟫ =
            symPerturbB (n := n) i.castSucc := by
        simpa [symPerturbB, sym_inner_castSucc_zero] using hi
      have h := hz i.castSucc hactive
      rw [symPerturbA_castSucc] at h
      simp [hig, hif, inner_embed_any] at h
      exact h
    have hy : y = 0 := hrem y hyactive
    have hgactive :
        ⟪symPerturbA c f g ε g.castSucc, Hirsch.embed x 0⟫ =
          symPerturbB (n := n) g.castSucc := by
      simpa [symPerturbB, sym_inner_castSucc_zero] using hg
    have hgt := hz g.castSucc hgactive
    rw [symPerturbA_castSucc] at hgt
    simp [inner_embed_any, hy] at hgt
    have ht : t = 0 := by
      exact hgt.resolve_left hε
    calc
      z = Hirsch.embed y t := (embed_proj z).symm
      _ = Hirsch.embed 0 0 := by rw [hy, ht]
      _ = 0 := embed_zero_zero

end HirschAxisSym
