import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialHalfspaceEdge
import Solutions.PolynomialHalfspaceVertex
import Solutions.PolynomialAdjEndpoints

open scoped RealInnerProductSpace
open Set Hirsch HirschCut

set_option maxHeartbeats 4000000

noncomputable section

/-- From a retained original vertex, stop an outer edge walk at its first
cut-plane crossing. This helper does not require convexity of the outer set. -/
theorem HirschCut.outer_vertex_cut_access
    (d B : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ Q) (hule : ⟪c, u⟫ ≤ b)
    (hv : v ∈ extremePoints ℝ Q) (hvge : b ≤ ⟪c, v⟫)
    (hD : DiamLE Q B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧ ⟪c, z⟫ = b ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w B = z ∧
        ∀ j < B, w j = w (j + 1) ∨
          Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) (w j) (w (j + 1)) := by
  classical
  let P := Q ∩ {x | ⟪c, x⟫ ≤ b}
  by_cases huEq : ⟪c, u⟫ = b
  · have huP : u ∈ extremePoints ℝ P := by
      refine ⟨⟨hu.1, hule⟩, ?_⟩
      intro x hx y hy hop
      exact hu.2 hx.1 hy.1 hop
    exact ⟨u, huP, huEq, fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  have huLt : ⟪c, u⟫ < b := lt_of_le_of_ne hule huEq
  obtain ⟨w, hw0, hwB, hws⟩ := hD u hu v hv
  have hex : ∃ k : ℕ, k ≤ B ∧ b ≤ ⟪c, w k⟫ := by
    exact ⟨B, le_rfl, by simpa only [hwB] using hvge⟩
  let k := Nat.find hex
  have hk : k ≤ B ∧ b ≤ ⟪c, w k⟫ := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hzero
    have h := hk.2
    rw [hzero, hw0] at h
    linarith
  obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjB : j < B := by omega
  have hbefore (l : ℕ) (hl : l < k) : ⟪c, w l⟫ < b := by
    by_contra hnot
    have hge : b ≤ ⟪c, w l⟫ := le_of_not_gt hnot
    have hmin : k ≤ l := Nat.find_min' hex ⟨by omega, hge⟩
    omega
  have hleft : ⟪c, w j⟫ < b := hbefore j (by omega)
  have hright : b ≤ ⟪c, w (j + 1)⟫ := by
    simpa only [hjk, Nat.succ_eq_add_one] using hk.2
  have hedge : Adj Q (w j) (w (j + 1)) := by
    rcases hws j hjB with hsame | hedge
    · rw [hsame] at hleft
      exact False.elim ((not_lt_of_ge hright) hleft)
    · exact hedge
  obtain ⟨z, hcz, hzedge⟩ := clip_crossing_edge Q c b hedge hleft hright
  have hzext := HirschPolynomialAccess.adj_right_extreme P hzedge
  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun l => if l ≤ j then w l else z
  refine ⟨z, hzext, hcz, wp, ?_, ?_, ?_⟩
  · change (if 0 ≤ j then w 0 else z) = u
    rw [if_pos (Nat.zero_le j)]
    exact hw0
  · change (if B ≤ j then w B else z) = z
    exact if_neg (by omega)
  · intro l hlB
    by_cases hlj : l < j
    · have hl0 : l ≤ j := by omega
      have hl1 : l + 1 ≤ j := by omega
      have hpl : ⟪c, w l⟫ ≤ b := (hbefore l (by omega)).le
      have hpl1 : ⟪c, w (l + 1)⟫ ≤ b := (hbefore (l + 1) (by omega)).le
      rcases hws l hlB with hsame | hadj
      · exact Or.inl (by simpa only [wp, if_pos hl0, if_pos hl1] using hsame)
      · have he := retained_edge Q c b hadj hpl hpl1
        exact Or.inr (by simpa only [wp, if_pos hl0, if_pos hl1] using he)
    · by_cases hleq : l = j
      · subst l
        have hnext : ¬ j + 1 ≤ j := by omega
        exact Or.inr (by simpa only [wp, if_pos le_rfl, if_neg hnext] using hzedge)
      · have h0 : ¬ l ≤ j := by omega
        have h1 : ¬ l + 1 ≤ j := by omega
        exact Or.inl (by simp only [wp, if_neg h0, if_neg h1])

/-- Every vertex of a halfspace-clipped convex set reaches the specified cut
plane within the outer diameter budget. Vertices newly created by the cut
are already on the target plane; a vertex strictly inside is an original
outer vertex. This is cut-face access, not a bound on the full cut diameter. -/
theorem solution
    (d B : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ Q) (hvge : b ≤ ⟪c, v⟫)
    (hD : DiamLE Q B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧ ⟪c, z⟫ = b ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w B = z ∧
        ∀ j < B, w j = w (j + 1) ∨
          Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) (w j) (w (j + 1)) := by
  by_cases huEq : ⟪c, u⟫ = b
  · exact ⟨u, hu, huEq, fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  have huLt : ⟪c, u⟫ < b := lt_of_le_of_ne hu.1.2 huEq
  have huQ := strict_cut_extreme_to_parent Q hconv c b hu huLt
  exact outer_vertex_cut_access d B Q c b u v huQ hu.1.2 hv hvge hD

#print axioms solution
