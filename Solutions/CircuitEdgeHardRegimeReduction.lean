import Solutions.CircuitEdgeRefinementHardness

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Larman's classical graph-diameter estimate, stated as a local hypothesis so
this file can be axiom-audited without importing the local theorem stub. The
corresponding Prove2Me theorem `Hirsch.larman_bound` is already Proved. -/
def LarmanBoundClaim : Prop :=
  ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3))

/-- The genuinely unresolved complement after Larman's bound becomes
polynomial: only presentations with `n < 2^(d-3)` need an edge-refinement
argument. -/
def HardRegimeEdgeRefinementClaim : Prop :=
  ∃ C k : ℕ, ∀ (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    Bornology.IsBounded (Hpoly a b) →
    RowPresentationIrredundant a b → StrictlyFeasibleRows a b →
    ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
    ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
    ∀ L : ℕ, RowCircuitWalk a b L u v →
    n < 2 ^ (d - 3) →
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (C * (n + d) ^ k * L) = v ∧
        ∀ j < C * (n + d) ^ k * L,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))

/-- Powers over a positive natural base are monotone under adding an exponent. -/
theorem nat_pow_le_pow_add_right (N k r : ℕ) (hN : 1 ≤ N) :
    N ^ k ≤ N ^ (k + r) := by
  rw [pow_add]
  have hr : 1 ≤ N ^ r := one_le_pow₀ hN
  simpa using Nat.mul_le_mul_left (N ^ k) hr

/-- Child B reduces, without loss, to the high-dimensional regime
`n < 2^(d-3)`. In the complementary regime Larman supplies a quadratic graph
walk and the input circuit walk is unnecessary. -/
theorem edge_refinement_of_hard_regime
    (hlarman : LarmanBoundClaim)
    (hhard : HardRegimeEdgeRefinementClaim) :
    PolynomialEdgeRefinementClaim := by
  obtain ⟨C, k, hhard⟩ := hhard
  let C' : ℕ := C + 1
  let k' : ℕ := k + 2
  refine ⟨C', k', ?_⟩
  intro d n a b hbd hirr hstrict u hu v hv L hcirc
  by_cases hL0 : L = 0
  · subst L
    obtain ⟨cw, hcw0, hcwL, _hmem, _hsteps⟩ := hcirc
    have huv : u = v := hcw0.symm.trans hcwL
    subst v
    refine ⟨fun _ => u, rfl, ?_, ?_⟩
    · simp
    · intro j hj
      omega
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 hL0
  by_cases hN0 : n + d = 0
  · have hn0 : n = 0 := by omega
    have hd0 : d = 0 := by omega
    subst n
    subst d
    have huv : u = v := Subsingleton.elim _ _
    subst v
    refine ⟨fun _ => u, rfl, ?_, ?_⟩
    · simp [k']
    · intro j hj
      simp [k'] at hj
  have hN1 : 1 ≤ n + d := Nat.one_le_iff_ne_zero.2 hN0
  by_cases hreg : 2 ^ (d - 3) ≤ n
  · have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
    obtain ⟨w, hw0, hwB, hwstep⟩ := hlarman d n a b hne hbd u hu v hv
    have hquad : n * 2 ^ (d - 3) ≤ (n + d) ^ 2 := by
      have h1 : n * 2 ^ (d - 3) ≤ n * n := Nat.mul_le_mul_left n hreg
      have h2 : n * n ≤ (n + d) ^ 2 := by
        simp [pow_two]
        nlinarith
      exact h1.trans h2
    have hpow : (n + d) ^ 2 ≤ (n + d) ^ (k + 2) := by
      have h := nat_pow_le_pow_add_right (n + d) 2 k hN1
      simpa [Nat.add_comm] using h
    have hcoef : (n + d) ^ (k + 2) ≤ C' * (n + d) ^ (k + 2) := by
      have hC : 1 ≤ C' := by simp [C']
      calc
        (n + d) ^ (k + 2) = 1 * (n + d) ^ (k + 2) := by simp
        _ ≤ C' * (n + d) ^ (k + 2) := Nat.mul_le_mul_right _ hC
    have hbase : n * 2 ^ (d - 3) ≤ C' * (n + d) ^ k' := by
      dsimp [k']
      exact hquad.trans (hpow.trans hcoef)
    have hmul : C' * (n + d) ^ k' ≤ C' * (n + d) ^ k' * L := by
      calc
        C' * (n + d) ^ k' = (C' * (n + d) ^ k') * 1 := by simp
        _ ≤ (C' * (n + d) ^ k') * L :=
          Nat.mul_le_mul_left _ hL1
    exact pad_adj_walk (Hpoly a b) (hbase.trans hmul) w hw0 hwB hwstep
  · have hhardreg : n < 2 ^ (d - 3) := by omega
    obtain ⟨w, hw0, hwB, hwstep⟩ :=
      hhard d n a b hbd hirr hstrict u hu v hv L hcirc hhardreg
    have hpow : (n + d) ^ k ≤ (n + d) ^ (k + 2) :=
      nat_pow_le_pow_add_right (n + d) k 2 hN1
    have hC : C ≤ C' := by simp [C']
    have hbase : C * (n + d) ^ k ≤ C' * (n + d) ^ k' := by
      dsimp [k']
      exact Nat.mul_le_mul hC hpow
    have hbudget : C * (n + d) ^ k * L ≤ C' * (n + d) ^ k' * L :=
      Nat.mul_le_mul_right L hbase
    exact pad_adj_walk (Hpoly a b) hbudget w hw0 hwB hwstep

#print axioms nat_pow_le_pow_add_right
#print axioms edge_refinement_of_hard_regime

end HirschCircuit
