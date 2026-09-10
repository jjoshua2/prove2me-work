import Theorems.Thm_Hirsch_balanced_hpoly_transfer
import Theorems.Thm_Hirsch_balanced_polynomial_bound
import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

/-- Generic stationary padding for an edge walk. -/
theorem childB_pad_adj_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
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

/-- Exact Child-B reduction to the existing balanced polynomial-diameter core.
`balanced_hpoly_transfer` is Proved; `balanced_polynomial_bound` remains the
single Open imported theorem, so this submission should be a sketch rather
than a direct proof while that core remains Open. -/
theorem solution :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      Hirsch.RowPresentationIrredundant a b → Hirsch.StrictlyFeasibleRows a b →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ L : ℕ, Hirsch.RowCircuitWalk a b L u v →
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k * L) = v ∧
          ∀ j < C * (n + d) ^ k * L,
            w j = w (j + 1) ∨
              Hirsch.Adj (Hirsch.Hpoly a b) (w j) (w (j + 1)) := by
  obtain ⟨C, k, hbalanced⟩ := Hirsch.balanced_polynomial_bound
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
    obtain ⟨D, aQ, bQ, hD, hneQ, hbdQ, htransfer⟩ :=
      Hirsch.balanced_hpoly_transfer d n a b hne hbd
    have hQ : DiamLE (Hpoly aQ bQ) (C * D ^ k) :=
      hbalanced D aQ bQ hneQ hbdQ
    have hP : DiamLE (Hpoly a b) (C * D ^ k) :=
      htransfer (C * D ^ k) hQ
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
    exact childB_pad_adj_walk (Hpoly a b) (hbase.trans hmul) w hw0 hwB hwstep

#print axioms solution
