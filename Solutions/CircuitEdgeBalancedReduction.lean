import Solutions.CircuitEdgeRefinementHardness

set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Local hypothesis matching the existing Open d-step core theorem. -/
def BalancedPolynomialBoundClaim : Prop :=
  ∃ C k : ℕ, ∀ (D : ℕ)
    (a : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (b : Fin (2 * D) → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    DiamLE (Hpoly a b) (C * D ^ k)

/-- Local hypothesis matching the already-Proved balanced transfer theorem. -/
def BalancedHpolyTransferClaim : Prop :=
  ∀ (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    ∃ (D : ℕ) (aQ : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (bQ : Fin (2 * D) → ℝ),
      D = d + (n - 2 * d) ∧
      (Hpoly aQ bQ).Nonempty ∧
      Bornology.IsBounded (Hpoly aQ bQ) ∧
      ∀ L : ℕ, DiamLE (Hpoly aQ bQ) L → DiamLE (Hpoly a b) L

/-- The remaining circuit-to-edge theorem is already a consequence of the
existing balanced polynomial-diameter core. The circuit walk is used only in
the zero-length case to infer equality of its endpoints; for every positive
length the graph-diameter route ignores its intermediates entirely. -/
theorem edge_refinement_of_balanced
    (htransfer : BalancedHpolyTransferClaim)
    (hbalanced : BalancedPolynomialBoundClaim) :
    PolynomialEdgeRefinementClaim := by
  obtain ⟨C, k, hC⟩ := hbalanced
  refine ⟨C, k, ?_⟩
  intro d n a b hbd _hirr _hstrict u hu v hv L hcirc
  by_cases hL0 : L = 0
  · subst L
    obtain ⟨cw, hcw0, hcwL, _hmem, _hsteps⟩ := hcirc
    have huv : u = v := hcw0.symm.trans hcwL
    subst v
    refine ⟨fun _ => u, rfl, ?_, ?_⟩
    · simp
    · intro j hj
      omega
  · have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 hL0
    have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
    obtain ⟨D, aQ, bQ, hD, hneQ, hbdQ, htr⟩ :=
      htransfer d n a b hne hbd
    have hQ : DiamLE (Hpoly aQ bQ) (C * D ^ k) :=
      hC D aQ bQ hneQ hbdQ
    have hP : DiamLE (Hpoly a b) (C * D ^ k) := htr (C * D ^ k) hQ
    have hDle : D ≤ n + d := by
      rw [hD]
      omega
    have hbase : C * D ^ k ≤ C * (n + d) ^ k :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hDle k)
    have hmul : C * (n + d) ^ k ≤ C * (n + d) ^ k * L := by
      calc
        C * (n + d) ^ k = (C * (n + d) ^ k) * 1 := by simp
        _ ≤ (C * (n + d) ^ k) * L := Nat.mul_le_mul_left _ hL1
    obtain ⟨w, hw0, hwB, hwstep⟩ := hP u hu v hv
    exact pad_adj_walk (Hpoly a b) (hbase.trans hmul) w hw0 hwB hwstep

#print axioms edge_refinement_of_balanced

end HirschCircuit
