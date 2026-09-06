import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_wedge

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisProduct

variable {d n : ℕ}

lemma embed_castSucc (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) (i : Fin d) :
    Hirsch.embed x t i.castSucc = x i := by
  simp [Hirsch.embed, Fin.snoc_castSucc]

lemma embed_last (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Hirsch.embed x t (Fin.last d) = t := by
  simp [Hirsch.embed, Fin.snoc_last]

lemma proj_apply (z : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    Hirsch.proj z i = z i.castSucc := by
  rw [Hirsch.proj, PiLp.toLp_apply]
  rfl

lemma proj_embed (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Hirsch.proj (Hirsch.embed x t) = x := by
  ext i
  rw [proj_apply, embed_castSucc]

lemma embed_proj (z : EuclideanSpace ℝ (Fin (d + 1))) :
    Hirsch.embed (Hirsch.proj z) (z (Fin.last d)) = z := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [embed_last]
  · intro j
    simp [embed_castSucc, proj_apply]

lemma proj_add (x y : EuclideanSpace ℝ (Fin (d + 1))) :
    Hirsch.proj (x + y) = Hirsch.proj x + Hirsch.proj y := by
  ext i
  simp [proj_apply]

lemma proj_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    Hirsch.proj (c • x) = c • Hirsch.proj x := by
  ext i
  simp [proj_apply]

lemma inner_embed (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    ⟪Hirsch.embed x t, Hirsch.embed y s⟫ = ⟪x, y⟫ + t * s := by
  simp [Hirsch.embed, inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  ring

lemma norm_embed (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ‖Hirsch.embed x t‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
  have hx : ‖Hirsch.embed x t‖ ^ 2 = ⟪Hirsch.embed x t, Hirsch.embed x t⟫ :=
    (real_inner_self_eq_norm_sq (Hirsch.embed x t)).symm
  have hy : ‖x‖ ^ 2 = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
  rw [hx, inner_embed, hy]
  ring

/-- Row `r` is redundant in the given H-description. -/
def RowRedundant
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (r : Fin n) : Prop :=
  ∀ x, (∀ i, i ≠ r → ⟪a i, x⟫ ≤ b i) → ⟪a r, x⟫ ≤ b r

/-- Replace a redundant old row by `t ≤ 1` and append `t ≥ 0`. -/
noncomputable def productA
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)) :=
  Fin.snoc
    (fun i => if i = r then Hirsch.embed 0 1 else Hirsch.embed (a i) 0)
    (Hirsch.embed 0 (-1))

noncomputable def productB (b : Fin n → ℝ) (r : Fin n) : Fin (n + 1) → ℝ :=
  Fin.snoc (fun i => if i = r then 1 else b i) 0

lemma productA_castSucc (a : Fin n → EuclideanSpace ℝ (Fin d)) (r i : Fin n) :
    productA a r i.castSucc =
      if i = r then Hirsch.embed 0 1 else Hirsch.embed (a i) 0 := by
  simp [productA, Fin.snoc_castSucc]

lemma productA_last (a : Fin n → EuclideanSpace ℝ (Fin d)) (r : Fin n) :
    productA a r (Fin.last n) = Hirsch.embed 0 (-1) := by
  simp [productA, Fin.snoc_last]

lemma productB_castSucc (b : Fin n → ℝ) (r i : Fin n) :
    productB b r i.castSucc = if i = r then 1 else b i := by
  simp [productB, Fin.snoc_castSucc]

lemma productB_last (b : Fin n → ℝ) (r : Fin n) :
    productB b r (Fin.last n) = 0 := by
  simp [productB, Fin.snoc_last]

lemma mem_product_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (r : Fin n)
    (hred : RowRedundant a b r)
    (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Hirsch.embed x t ∈ Hpoly (productA a r) (productB b r) ↔
      x ∈ Hpoly a b ∧ 0 ≤ t ∧ t ≤ 1 := by
  constructor
  · intro hz
    have ht0 : 0 ≤ t := by
      have h := hz (Fin.last n)
      simp [productA_last, productB_last, inner_embed] at h
      linarith
    have ht1 : t ≤ 1 := by
      have h := hz r.castSucc
      simp [productA_castSucc, productB_castSucc, inner_embed] at h
      exact h
    have hxother : ∀ i, i ≠ r → ⟪a i, x⟫ ≤ b i := by
      intro i hir
      have h := hz i.castSucc
      simpa [productA_castSucc, productB_castSucc, hir, inner_embed] using h
    have hxr : ⟪a r, x⟫ ≤ b r := hred x hxother
    exact ⟨fun i => by by_cases hi : i = r; · simpa [hi] using hxr; · exact hxother i hi,
      ht0, ht1⟩
  · rintro ⟨hx, ht0, ht1⟩ j
    refine Fin.lastCases ?_ ?_ j
    · simp [productA_last, productB_last, inner_embed]
      linarith
    · intro i
      by_cases hir : i = r
      · subst i
        simpa [productA_castSucc, productB_castSucc, inner_embed] using ht1
      · simpa [productA_castSucc, productB_castSucc, hir, inner_embed] using hx i

lemma product_nonempty
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (r : Fin n)
    (hred : RowRedundant a b r) (hne : (Hpoly a b).Nonempty) :
    (Hpoly (productA a r) (productB b r)).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨Hirsch.embed x 0, (mem_product_iff a b r hred x 0).2 ⟨hx, by norm_num, by norm_num⟩⟩

lemma product_bounded
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (r : Fin n)
    (hred : RowRedundant a b r)
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    Bornology.IsBounded (Hpoly (productA a r) (productB b r)) := by
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  refine (isBounded_iff_forall_norm_le).2
    ⟨Real.sqrt (C0 ^ 2 + 1), fun z hz => ?_⟩
  have hzid : z = Hirsch.embed (Hirsch.proj z) (z (Fin.last d)) := (embed_proj z).symm
  have hz' := (mem_product_iff a b r hred (Hirsch.proj z) (z (Fin.last d))).1
    (by simpa [hzid] using hz)
  have hxC : ‖Hirsch.proj z‖ ≤ C0 :=
    (hC (Hirsch.proj z) hz'.1).trans (le_max_left _ _)
  have ht0 := hz'.2.1
  have ht1 := hz'.2.2
  have hsq : ‖z‖ ^ 2 = ‖Hirsch.proj z‖ ^ 2 + (z (Fin.last d)) ^ 2 := by
    rw [hzid]
    exact norm_embed _ _
  have hsqle : ‖z‖ ^ 2 ≤ C0 ^ 2 + 1 := by
    have hx2 : ‖Hirsch.proj z‖ ^ 2 ≤ C0 ^ 2 := by
      nlinarith [norm_nonneg (Hirsch.proj z)]
    have ht2 : (z (Fin.last d)) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  rw [← Real.sqrt_sq (norm_nonneg z)]
  exact Real.sqrt_le_sqrt hsqle

lemma product_endpoint_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (r : Fin n)
    (hred : RowRedundant a b r)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    {t : ℝ} (ht : t = 0 ∨ t = 1) :
    Hirsch.embed x t ∈ extremePoints ℝ (Hpoly (productA a r) (productB b r)) := by
  refine ⟨(mem_product_iff a b r hred x t).2 ⟨hx.1, ?_, ?_⟩, ?_⟩
  · rcases ht with rfl | rfl <;> norm_num
  · rcases ht with rfl | rfl <;> norm_num
  · intro p hp q hq hop
    obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hop
    have hp' := (mem_product_iff a b r hred (Hirsch.proj p) (p (Fin.last d))).1
      (by simpa [embed_proj] using hp)
    have hq' := (mem_product_iff a b r hred (Hirsch.proj q) (q (Fin.last d))).1
      (by simpa [embed_proj] using hq)
    have hprojcomb : α • Hirsch.proj p + β • Hirsch.proj q = x := by
      have h := congrArg Hirsch.proj hcomb
      simpa [proj_add, proj_smul, proj_embed] using h
    have hopP : x ∈ openSegment ℝ (Hirsch.proj p) (Hirsch.proj q) :=
      ⟨α, β, hα, hβ, hαβ, hprojcomb⟩
    have hpx : Hirsch.proj p = x := hx.2 hp'.1 hq'.1 hopP
    have hlastcomb := congrArg
      (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) hcomb
    have hpt : p (Fin.last d) = t := by
      rcases ht with rfl | rfl
      · have : α * p (Fin.last d) + β * q (Fin.last d) = 0 := by
          simpa [embed_last, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hlastcomb
        nlinarith [hp'.2.1, hq'.2.1]
      · have : α * p (Fin.last d) + β * q (Fin.last d) = 1 := by
          simpa [embed_last, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using hlastcomb
        nlinarith [hp'.2.2, hq'.2.2]
    calc
      p = Hirsch.embed (Hirsch.proj p) (p (Fin.last d)) := (embed_proj p).symm
      _ = Hirsch.embed x t := by rw [hpx, hpt]

end HirschAxisProduct
