import Mathlib
import Solutions.PolynomialClipWalk

open scoped RealInnerProductSpace
open Set Hirsch HirschCut HirschClip

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschClip

/-- Two strictly retained endpoints use one outer walk, not two independent
routes to the plane. Clip its first and last contacts and replace everything
between them by a cut-face walk. The total retained length is at most B. -/
theorem splice_outer_walk
    (d B C : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C)
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hstart : ⟪c, w 0⟫ < b) (hfinish : ⟪c, w B⟫ < b)
    (hstep : ∀ j < B, w j = w (j + 1) ∨ Adj Q (w j) (w (j + 1))) :
    Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) (B + C) (w 0) (w B) := by
  classical
  by_cases hex : ∃ k : ℕ, k ≤ B ∧ b ≤ ⟪c, w k⟫
  · let k := Nat.find hex
    have hk : k ≤ B ∧ b ≤ ⟪c, w k⟫ := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      have hbad : b ≤ ⟪c, w 0⟫ := by simpa only [hk0] using hk.2
      exact (not_le_of_gt hstart) hbad
    have hbefore : ∀ j < k, ⟪c, w j⟫ < b := by
      intro j hj
      by_contra h
      have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, le_of_not_gt h⟩
      omega
    obtain ⟨p, hp, hcp, hwp⟩ := clip_prefix Q c b k hkpos w hbefore hk.2
      (fun j hj => hstep j (by omega))
    let wr : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (B - j)
    have hwr0 : wr 0 = w B := by simp only [wr, Nat.sub_zero]
    have hwrstep : ∀ j < B, wr j = wr (j + 1) ∨ Adj Q (wr j) (wr (j + 1)) :=
      reverse_steps Q w hstep
    have hexr : ∃ l : ℕ, l ≤ B - k ∧ b ≤ ⟪c, wr l⟫ := by
      refine ⟨B - k, le_rfl, ?_⟩
      have hidx : B - (B - k) = k := by omega
      simpa only [wr, hidx] using hk.2
    let l := Nat.find hexr
    have hl : l ≤ B - k ∧ b ≤ ⟪c, wr l⟫ := Nat.find_spec hexr
    have hlpos : 0 < l := by
      by_contra h
      have hl0 : l = 0 := by omega
      have hbad : b ≤ ⟪c, w B⟫ := by simpa only [hl0, hwr0] using hl.2
      exact (not_le_of_gt hfinish) hbad
    have hbeforer : ∀ j < l, ⟪c, wr j⟫ < b := by
      intro j hj
      by_contra h
      have hmin : l ≤ j := Nat.find_min' hexr ⟨by omega, le_of_not_gt h⟩
      omega
    obtain ⟨q, hq, hcq, hwq⟩ := clip_prefix Q c b l hlpos wr hbeforer hl.2
      (fun j hj => hwrstep j (by omega))
    have hqp : Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) l q (w B) := by
      simpa only [hwr0] using walk_reverse hwq
    have hmiddle := cut_face_walk Q c b C hF hp hq hcp hcq
    have hspliced := walk_append (walk_append hwp hmiddle) hqp
    exact walk_pad (by omega : k + C + l ≤ B + C) hspliced
  · have hle : ∀ j ≤ B, ⟪c, w j⟫ ≤ b := by
      intro j hj
      have hn : ¬ b ≤ ⟪c, w j⟫ := fun h => hex ⟨j, hj, h⟩
      exact (lt_of_not_ge hn).le
    have hretained : Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) B (w 0) (w B) := by
      refine ⟨w, rfl, rfl, ?_⟩
      intro j hj
      rcases hstep j hj with h | h
      · exact Or.inl h
      · exact Or.inr (retained_edge Q c b h (hle j (by omega)) (hle (j + 1) (by omega)))
    exact walk_pad (Nat.le_add_right B C) hretained

#print axioms splice_outer_walk

end HirschClip
