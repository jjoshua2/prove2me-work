import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCut

variable {d : ℕ}

lemma inner_combo (c p q : EuclideanSpace ℝ (Fin d)) (α β : ℝ) :
    ⟪c, α • p + β • q⟫ = α * ⟪c, p⟫ + β * ⟪c, q⟫ := by
  simp [inner_add_right, inner_smul_right]

/-- A retained old edge stays an edge after adding one halfspace. -/
lemma retained_edge
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {p q : EuclideanSpace ℝ (Fin d)} (hadj : Adj Q p q)
    (hp : ⟪c, p⟫ ≤ b) (hq : ⟪c, q⟫ ≤ b) :
    Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) p q := by
  refine ⟨hadj.1, hadj.2.mono Set.inter_subset_left ?_⟩
  intro x hx
  refine ⟨hadj.2.subset hx, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hx
  change ⟪c, α • p + β • q⟫ ≤ b
  rw [inner_combo]
  have h1 := mul_le_mul_of_nonneg_left hp hα
  have h2 := mul_le_mul_of_nonneg_left hq hβ
  have h3 : α * b + β * b = b := by rw [← add_mul, hαβ, one_mul]
  linarith

/-- The first part of an old edge crossing the cut plane is an edge of the
clipped polytope. Its new endpoint lies exactly on the cut plane. -/
lemma clip_crossing_edge
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    {p q : EuclideanSpace ℝ (Fin d)} (hadj : Adj Q p q)
    (hp : ⟪c, p⟫ < b) (hq : b ≤ ⟪c, q⟫) :
    ∃ z : EuclideanSpace ℝ (Fin d), ⟪c, z⟫ = b ∧
      Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) p z := by
  let D : ℝ := ⟪c, q⟫ - ⟪c, p⟫
  have hD : 0 < D := by dsimp [D]; linarith
  let t : ℝ := (b - ⟪c, p⟫) / D
  have ht : 0 < t := div_pos (sub_pos.mpr hp) hD
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hD).2
    dsimp [D]
    linarith
  have htD : t * D = b - ⟪c, p⟫ := div_mul_cancel₀ _ hD.ne'
  let z : EuclideanSpace ℝ (Fin d) := (1 - t) • p + t • q
  have hz : ⟪c, z⟫ = b := by
    rw [show z = (1 - t) • p + t • q from rfl, inner_combo]
    dsimp [D] at htD
    nlinarith
  have hzseg : z ∈ segment ℝ p q :=
    ⟨1 - t, t, by linarith, ht.le, by ring, rfl⟩
  have heq : segment ℝ p z = {w | w ∈ segment ℝ p q ∧ ⟪c, w⟫ ≤ b} := by
    ext w
    constructor
    · intro hw
      have hwold : w ∈ segment ℝ p q :=
        (convex_segment p q).segment_subset (left_mem_segment ℝ p q) hzseg hw
      refine ⟨hwold, ?_⟩
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
      rw [inner_combo, hz]
      have h1 := mul_le_mul_of_nonneg_left hp.le hα
      have h2 : α * b + β * b = b := by rw [← add_mul, hαβ, one_mul]
      linarith
    · rintro ⟨hw, hwb⟩
      obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hw
      have hαone : α = 1 - β := by linarith
      have hinner : ⟪c, w⟫ = ⟪c, p⟫ + β * D := by
        rw [← hcomb, inner_combo, hαone]
        dsimp [D]
        ring
      have hβt : β ≤ t := by
        rw [hinner] at hwb
        nlinarith
      let γ : ℝ := β / t
      have hγ0 : 0 ≤ γ := div_nonneg hβ ht.le
      have hγ1 : γ ≤ 1 := by
        apply (div_le_iff₀ ht).2
        linarith
      have hγt : γ * t = β := div_mul_cancel₀ _ ht.ne'
      have hflat : (1 - γ) • p + γ • z =
          (1 - γ * t) • p + (γ * t) • q := by
        dsimp [z]
        module
      refine ⟨1 - γ, γ, by linarith, hγ0, by ring, ?_⟩
      rw [hflat, hγt, ← hαone]
      exact hcomb
  have hpz : p ≠ z := by
    intro h
    exact hp.ne ((congrArg (fun x : EuclideanSpace ℝ (Fin d) => ⟪c, x⟫) h).trans hz)
  refine ⟨z, hz, hpz, ?_, ?_⟩
  · intro w hw
    rw [heq] at hw
    exact ⟨hadj.2.subset hw.1, hw.2⟩
  · intro x hx y hy w hw hop
    rw [heq] at hw ⊢
    exact ⟨hadj.2.left_mem_of_mem_openSegment hx.1 hy.1 hw.1 hop, hx.2⟩

#print axioms clip_crossing_edge

end HirschCut
