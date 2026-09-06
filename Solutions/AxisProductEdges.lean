import Mathlib
import Solutions.AxisProductScratch

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisProduct

variable {d n : ℕ}

lemma embed_add (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    Hirsch.embed (x + y) (t + s) = Hirsch.embed x t + Hirsch.embed y s := by
  refine PiLp.ext fun i => ?_
  simp only [Hirsch.embed, ofLp_add, PiLp.toLp_apply, Pi.add_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j
    simp [Fin.snoc_castSucc, Pi.add_apply]

lemma embed_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Hirsch.embed (c • x) (c * t) = c • Hirsch.embed x t := by
  refine PiLp.ext fun i => ?_
  simp only [Hirsch.embed, ofLp_smul, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j
    simp [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]

lemma embed_affine (α β : ℝ) (hαβ : α + β = 1)
    (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    Hirsch.embed (α • x + β • y) (α * t + β * s) =
      α • Hirsch.embed x t + β • Hirsch.embed y s := by
  rw [embed_add, embed_smul, embed_smul]

lemma convex_Hpoly (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy α β hα hβ hαβ i
  have hi : ⟪a i, α • x + β • y⟫ = α * ⟪a i, x⟫ + β * ⟪a i, y⟫ := by
    simp [inner_add_right, inner_smul_right]
  rw [hi]
  have h1 := mul_le_mul_of_nonneg_left (hx i) hα
  have h2 := mul_le_mul_of_nonneg_left (hy i) hβ
  have : α * b i + β * b i = b i := by rw [← add_mul, hαβ, one_mul]
  linarith

lemma product_proj_adj
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (r : Fin n)
    (hred : RowRedundant a b r)
    {p q : EuclideanSpace ℝ (Fin (d + 1))}
    (hadj : Adj (Hpoly (productA a r) (productB b r)) p q) :
    Hirsch.proj p = Hirsch.proj q ∨ Adj (Hpoly a b) (Hirsch.proj p) (Hirsch.proj q) := by
  obtain ⟨hpq, hextr⟩ := hadj
  by_cases hproj : Hirsch.proj p = Hirsch.proj q
  · exact Or.inl hproj
  · refine Or.inr ⟨hproj, ?_⟩
    have hpW := hextr.subset (left_mem_segment ℝ p q)
    have hqW := hextr.subset (right_mem_segment ℝ p q)
    have hp' := (mem_product_iff a b r hred (Hirsch.proj p) (p (Fin.last d))).1
      (by simpa [embed_proj] using hpW)
    have hq' := (mem_product_iff a b r hred (Hirsch.proj q) (q (Fin.last d))).1
      (by simpa [embed_proj] using hqW)
    refine ⟨(convex_Hpoly a b).segment_subset hp'.1 hq'.1, ?_⟩
    intro x hx y hy z hz hzopen
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hz
    let t := α * p (Fin.last d) + β * q (Fin.last d)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact add_nonneg (mul_nonneg hα hp'.2.1) (mul_nonneg hβ hq'.2.1)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      have h1 := mul_le_mul_of_nonneg_left hp'.2.2 hα
      have h2 := mul_le_mul_of_nonneg_left hq'.2.2 hβ
      have hone : α * 1 + β * 1 = 1 := by norm_num [hαβ]
      linarith
    have hxW : Hirsch.embed x t ∈ Hpoly (productA a r) (productB b r) :=
      (mem_product_iff a b r hred x t).2 ⟨hx, ht0, ht1⟩
    have hyW : Hirsch.embed y t ∈ Hpoly (productA a r) (productB b r) :=
      (mem_product_iff a b r hred y t).2 ⟨hy, ht0, ht1⟩
    have hzW : Hirsch.embed z t ∈ segment ℝ p q := by
      refine ⟨α, β, hα, hβ, hαβ, ?_⟩
      calc
        α • p + β • q
            = α • Hirsch.embed (Hirsch.proj p) (p (Fin.last d)) +
              β • Hirsch.embed (Hirsch.proj q) (q (Fin.last d)) := by
                rw [← embed_proj p, ← embed_proj q]
        _ = Hirsch.embed (α • Hirsch.proj p + β • Hirsch.proj q) t := by
              symm
              exact embed_affine α β hαβ _ _ _ _
        _ = Hirsch.embed z t := by rw [hzcomb]
    obtain ⟨γ, δ, hγ, hδ, hγδ, hopencomb⟩ := hzopen
    have hopW : Hirsch.embed z t ∈ openSegment ℝ (Hirsch.embed x t) (Hirsch.embed y t) := by
      refine ⟨γ, δ, hγ, hδ, hγδ, ?_⟩
      calc
        γ • Hirsch.embed x t + δ • Hirsch.embed y t
            = Hirsch.embed (γ • x + δ • y) (γ * t + δ * t) :=
                (embed_affine γ δ hγδ x y t t).symm
        _ = Hirsch.embed z t := by
              rw [hopencomb]
              congr 1
              rw [← add_mul, hγδ, one_mul]
    have hxseg : Hirsch.embed x t ∈ segment ℝ p q :=
      hextr.left_mem_of_mem_openSegment hxW hyW hzW hopW
    obtain ⟨α', β', hα', hβ', hαβ', hxcomb⟩ := hxseg
    refine ⟨α', β', hα', hβ', hαβ', ?_⟩
    have h := congrArg Hirsch.proj hxcomb
    simpa [proj_add, proj_smul, proj_embed] using h

lemma midpoint_cross
    (p q : EuclideanSpace ℝ (Fin (d + 1))) :
    midpoint ℝ p q = midpoint ℝ
      (Hirsch.embed (Hirsch.proj p) (q (Fin.last d)))
      (Hirsch.embed (Hirsch.proj q) (p (Fin.last d))) := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [midpoint_eq_smul_add, embed_last, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul]
    ring
  · intro j
    simp [midpoint_eq_smul_add, embed_castSucc, proj_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]

/-- An edge of a Cartesian product cannot change both the base point and the
interval coordinate. -/
lemma product_adj_proj_or_height_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (r : Fin n)
    (hred : RowRedundant a b r)
    {p q : EuclideanSpace ℝ (Fin (d + 1))}
    (hadj : Adj (Hpoly (productA a r) (productB b r)) p q) :
    Hirsch.proj p = Hirsch.proj q ∨ p (Fin.last d) = q (Fin.last d) := by
  obtain ⟨hpq, hextr⟩ := hadj
  by_cases hproj : Hirsch.proj p = Hirsch.proj q
  · exact Or.inl hproj
  refine Or.inr ?_
  have hpW := hextr.subset (left_mem_segment ℝ p q)
  have hqW := hextr.subset (right_mem_segment ℝ p q)
  have hp' := (mem_product_iff a b r hred (Hirsch.proj p) (p (Fin.last d))).1
    (by simpa [embed_proj] using hpW)
  have hq' := (mem_product_iff a b r hred (Hirsch.proj q) (q (Fin.last d))).1
    (by simpa [embed_proj] using hqW)
  let rp := Hirsch.embed (Hirsch.proj p) (q (Fin.last d))
  let sq := Hirsch.embed (Hirsch.proj q) (p (Fin.last d))
  have hrW : rp ∈ Hpoly (productA a r) (productB b r) :=
    (mem_product_iff a b r hred _ _).2 ⟨hp'.1, hq'.2.1, hq'.2.2⟩
  have hsW : sq ∈ Hpoly (productA a r) (productB b r) :=
    (mem_product_iff a b r hred _ _).2 ⟨hq'.1, hp'.2.1, hp'.2.2⟩
  let m := midpoint ℝ p q
  have hmseg : m ∈ segment ℝ p q := midpoint_mem_segment ℝ p q
  have hmopen : m ∈ openSegment ℝ rp sq := by
    refine ⟨(1/2 : ℝ), (1/2 : ℝ), by positivity, by positivity, by ring, ?_⟩
    rw [← midpoint_eq_smul_add]
    exact (midpoint_cross p q).symm
  have hrseg : rp ∈ segment ℝ p q :=
    hextr.left_mem_of_mem_openSegment hrW hsW hmseg hmopen
  obtain ⟨α, β, hα, hβ, hαβ, hrcomb⟩ := hrseg
  have hprojcomb : α • Hirsch.proj p + β • Hirsch.proj q = Hirsch.proj p := by
    have h := congrArg Hirsch.proj hrcomb
    simpa [rp, proj_add, proj_smul, proj_embed] using h
  obtain ⟨i, hi⟩ : ∃ i, Hirsch.proj p i ≠ Hirsch.proj q i := by
    by_contra h
    push_neg at h
    exact hproj (PiLp.ext h)
  have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hprojcomb
  have hprod : β * (Hirsch.proj q i - Hirsch.proj p i) = 0 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hcoord
    nlinarith [hαβ]
  have hdiff : Hirsch.proj q i - Hirsch.proj p i ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hi)
  have hβ0 : β = 0 := (mul_eq_zero.mp hprod).resolve_right hdiff
  have hα1 : α = 1 := by linarith
  have hlast := congrArg
    (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) hrcomb
  simp [rp, embed_last, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hβ0, hα1] at hlast
  exact hlast.symm

end HirschAxisProduct
