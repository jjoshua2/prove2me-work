import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuitBalanced

/-- Local copy of the remaining edge-refinement claim, used only to audit the
reduction without importing the Open platform target. -/
def EdgeRefinementClaim : Prop :=
  ∃ C k : ℕ, ∀ (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    Bornology.IsBounded (Hpoly a b) →
    RowPresentationIrredundant a b → StrictlyFeasibleRows a b →
    ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
    ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
    ∀ L : ℕ, RowCircuitWalk a b L u v →
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (C * (n + d) ^ k * L) = v ∧
        ∀ j < C * (n + d) ^ k * L,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))

/-- Local copy of the existing Open balanced d-step core. -/
def BalancedPolynomialBoundClaim : Prop :=
  ∃ C k : ℕ, ∀ (D : ℕ)
    (a : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (b : Fin (2 * D) → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    DiamLE (Hpoly a b) (C * D ^ k)

/-- Local copy of the already-Proved balanced H-polytope transfer theorem. -/
def BalancedTransferClaim : Prop :=
  ∀ (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    ∃ (D : ℕ) (aQ : Fin (2 * D) → EuclideanSpace ℝ (Fin D)) (bQ : Fin (2 * D) → ℝ),
      D = d + (n - 2 * d) ∧
      (Hpoly aQ bQ).Nonempty ∧
      Bornology.IsBounded (Hpoly aQ bQ) ∧
      ∀ L : ℕ, DiamLE (Hpoly aQ bQ) L → DiamLE (Hpoly a b) L

/-- Stationary padding preserves an adjacency walk. -/
theorem pad_adj_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {u v : E} {B D : ℕ} (hBD : B ≤ D)
    (w : ℕ → E) (hw0 : w 0 = u) (hwB : w B = v)
    (hstep : ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ wp : ℕ → E, wp 0 = u ∧ wp D = v ∧
      ∀ j < D, wp j = wp (j + 1) ∨ Adj P (wp j) (wp (j + 1)) := by
  let wp : ℕ → E := fun j => w (min j B)
  refine ⟨wp, ?_, ?_, ?_⟩
  · simpa [wp] using hw0
  · simpa [wp, Nat.min_eq_right hBD] using hwB
  · intro j hj
    by_cases hjB : j < B
    · have hjle : j ≤ B := Nat.le_of_lt hjB
      have hj1le : j + 1 ≤ B := by omega
      simpa [wp, Nat.min_eq_left hjle, Nat.min_eq_left hj1le] using hstep j hjB
    · have hBj : B ≤ j := by omega
      have hBj1 : B ≤ j + 1 := by omega
      exact Or.inl (by simp [wp, Nat.min_eq_right hBj, Nat.min_eq_right hBj1])

/-- The remaining circuit-to-edge claim follows from the existing balanced
polynomial-diameter core and the already-Proved transfer theorem. For positive
`L`, the supplied circuit walk can be ignored entirely: a graph-diameter path
is stronger and is padded by the required factor `L`. -/
theorem edge_refinement_of_balanced
    (htransfer : BalancedTransferClaim)
    (hbalanced : BalancedPolynomialBoundClaim) : EdgeRefinementClaim := by
  obtain ⟨C, k, hC⟩ := hbalanced
  refine ⟨C, k, ?_⟩
  intro d n a b hbd _hirr _hstrict u hu v hv L hcirc
  by_cases hL0 : L = 0
  · subst L
    obtain ⟨cw, hcw0, hcwL, _hmem, _hsteps⟩ := hcirc
    have huv : u = v := hcw0.symm.trans hcwL
    refine ⟨fun _ => u, rfl, ?_, ?_⟩
    · simpa using huv
    · intro j hj
      omega
  · have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 hL0
    have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
    obtain ⟨D, aQ, bQ, hD, hneQ, hbdQ, htr⟩ :=
      htransfer d n a b hne hbd
    have hQ : DiamLE (Hpoly aQ bQ) (C * D ^ k) := hC D aQ bQ hneQ hbdQ
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

end HirschCircuitBalanced
