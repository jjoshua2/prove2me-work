import Mathlib
import Solutions.PolynomialProductWalk
import Solutions.PolynomialAdjEndpoints

open Set Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschProduct

/-- A first target contact in a padded walk crosses a genuine edge. -/
lemma first_contact {E : Type*} (R : E → E → Prop) (T : E → Prop)
    {D : ℕ} (w : ℕ → E)
    (h0 : ¬ T (w 0)) (hD : T (w D))
    (hs : ∀ j < D, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ j < D, ¬ T (w j) ∧ T (w (j + 1)) ∧ R (w j) (w (j + 1)) := by
  classical
  have hex : ∃ k : ℕ, k ≤ D ∧ T (w k) := ⟨D, le_rfl, hD⟩
  let k := Nat.find hex
  have hk : k ≤ D ∧ T (w k) := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    apply h0
    simpa only [h] using hk.2
  obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjD : j < D := by omega
  have hjnot : ¬ T (w j) := by
    intro hjT
    have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, hjT⟩
    omega
  have hjnext : T (w (j + 1)) := by simpa only [hjk, Nat.succ_eq_add_one] using hk.2
  have hadj : R (w j) (w (j + 1)) := by
    rcases hs j hjD with heq | hadj
    · exact False.elim (hjnot (heq ▸ hjnext))
    · exact hadj
  exact ⟨j, hjD, hjnot, hjnext, hadj⟩

/-- Short prefixes to the predecessors of target-crossing edges are enough.
No low-dimension assumption is built into this graph/face interface. -/
theorem access_of_boundary_walks {d : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ P)
    (T : EuclideanSpace ℝ (Fin d) → Prop) (hTv : T v)
    (B : ℕ)
    (hconn : ∃ D : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w D = v ∧
      ∀ j < D, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hshort : ∀ x z, Adj P x z → ¬ T x → T z →
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w B = x ∧
        ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ z : EuclideanSpace ℝ (Fin d), z ∈ extremePoints ℝ P ∧ T z ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  classical
  by_cases hTu : T u
  · exact ⟨u, hu, hTu, fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
  obtain ⟨D, w, hw0, hwD, hws⟩ := hconn
  obtain ⟨j, hjD, hx, hz, hadj⟩ := first_contact (Adj P) T w
    (by simpa only [hw0] using hTu) (by simpa only [hwD] using hTv) hws
  have hzext := HirschPolynomialAccess.adj_right_extreme P hadj
  obtain ⟨p, hp0, hpB, hps⟩ := hshort (w j) (w (j + 1)) hadj hx hz
  let q : ℕ → EuclideanSpace ℝ (Fin d) := fun k => if k = 0 then w j else w (j + 1)
  have hq0 : q 0 = w j := by simp only [q, if_pos rfl]
  have hq1 : q 1 = w (j + 1) := by simp [q]
  have hqs : ∀ k < 1, q k = q (k + 1) ∨ Adj P (q k) (q (k + 1)) := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact Or.inr (by simpa only [Nat.zero_add, hq0, hq1] using hadj)
  obtain ⟨wp, hp0, hpB, hps⟩ := append_walk (Adj P) p q hp0 hpB hq0 hq1 hps hqs
  exact ⟨w (j + 1), hzext, hz, wp, hp0, hpB, hps⟩

#print axioms access_of_boundary_walks

end HirschProduct
