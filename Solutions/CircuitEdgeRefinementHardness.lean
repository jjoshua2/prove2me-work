import Solutions.CircuitPhaseRoute

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- Local copy of the sole remaining Prove2Me leaf. This is deliberately a
`Prop`, not an import of the Open platform theorem. -/
def PolynomialEdgeRefinementClaim : Prop :=
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

/-- Polynomial graph diameter restricted to exactly the class on which the
remaining circuit-to-edge child is stated. -/
def IrredundantStrictPolynomialDiameter : Prop :=
  ∃ C k : ℕ, ∀ (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    Bornology.IsBounded (Hpoly a b) →
    RowPresentationIrredundant a b → StrictlyFeasibleRows a b →
    DiamLE (Hpoly a b) (C * (n + d) ^ k)

/-- Generic stationary padding for graph walks. -/
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

/-- The verified standard-slice cubic route already gives a cubic row-circuit
walk between arbitrary vertices of any nonempty bounded fixed presentation;
no endpoint-separation preprocessing is needed here. -/
theorem rowCircuitWalk_cubic_fixed_presentation {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) :
    RowCircuitWalk a b (17 * n ^ 3) u v := by
  have hinj := rowMap_injective_of_bounded a b hbd u hu.1
  have hsu0 : slack a b u ∈ SlackPoly a b :=
    (slack_mem_SlackPoly_iff a b u).2 hu.1
  have hsv0 := slack_mem_extremePoints_of_mem_extremePoints a b hinj v hv
  have hsu : slack a b u ∈ StandardSlice (LinearMap.range (rowMap a)) b := by
    rw [← slackPoly_eq_standardSlice]
    exact hsu0
  have hsv : slack a b v ∈
      Set.extremePoints ℝ (StandardSlice (LinearMap.range (rowMap a)) b) := by
    rw [← slackPoly_eq_standardSlice]
    exact hsv0
  have hstd := standardCircuitWalk_cubic (LinearMap.range (rowMap a)) b
    (slack a b u) (slack a b v) hsu hsv
  exact (bounded_rowCircuitWalk_iff_standardCircuitWalk a b hbd u hu.1
    (17 * n ^ 3) u v).2 hstd

/-- The remaining circuit-to-edge leaf already implies a polynomial graph
Diameter bound on its entire stated class. The supplied circuit walk is taken
to be the verified `17*n^3` route. -/
theorem edge_refinement_implies_irredundant_strict_polynomial_diameter
    (href : PolynomialEdgeRefinementClaim) :
    IrredundantStrictPolynomialDiameter := by
  obtain ⟨C, k, hC⟩ := href
  refine ⟨17 * C, k + 3, ?_⟩
  intro d n a b hbd hirr hstrict
  intro u hu v hv
  have hcirc := rowCircuitWalk_cubic_fixed_presentation a b hbd u v hu hv
  obtain ⟨w, hw0, hwB, hwstep⟩ :=
    hC d n a b hbd hirr hstrict u hu v hv (17 * n ^ 3) hcirc
  let B : ℕ := C * (n + d) ^ k * (17 * n ^ 3)
  let D : ℕ := (17 * C) * (n + d) ^ (k + 3)
  have hpow : n ^ 3 ≤ (n + d) ^ 3 :=
    Nat.pow_le_pow_left (by omega : n ≤ n + d) 3
  have hBD : B ≤ D := by
    dsimp [B, D]
    rw [pow_add]
    have hinner : (n + d) ^ k * n ^ 3 ≤
        (n + d) ^ k * (n + d) ^ 3 :=
      Nat.mul_le_mul_left ((n + d) ^ k) hpow
    have hmul := Nat.mul_le_mul_left (17 * C) hinner
    nlinarith only [hmul]
  exact pad_adj_walk (Hpoly a b) hBD w hw0 hwB hwstep

/-- Conversely, a polynomial graph-diameter bound on the same class proves
exactly the remaining child. For positive `L` the supplied circuit walk is
irrelevant: use the diameter path and pad it by `L`. For `L=0`, the circuit
walk itself forces the endpoints to coincide. -/
theorem irredundant_strict_polynomial_diameter_implies_edge_refinement
    (hdiam : IrredundantStrictPolynomialDiameter) :
    PolynomialEdgeRefinementClaim := by
  obtain ⟨C, k, hC⟩ := hdiam
  refine ⟨C, k, ?_⟩
  intro d n a b hbd hirr hstrict u hu v hv L hcirc
  by_cases hL : L = 0
  · subst L
    obtain ⟨cw, hcw0, hcwL, _hmem, _hsteps⟩ := hcirc
    have huv : u = v := hcw0.symm.trans hcwL
    refine ⟨fun _ => u, rfl, ?_, ?_⟩
    · simpa using huv
    · intro j hj
      omega
  · have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 hL
    obtain ⟨w, hw0, hwB, hwstep⟩ := hC d n a b hbd hirr hstrict u hu v hv
    let B : ℕ := C * (n + d) ^ k
    have hBD : B ≤ B * L := by
      simpa only [mul_one] using Nat.mul_le_mul_left B hL1
    simpa only [B] using
      (pad_adj_walk (Hpoly a b) hBD w hw0 hwB hwstep)

/-- On the class appearing in Child B, the supposedly auxiliary edge-refinement
claim is logically equivalent to the polynomial graph-diameter problem. -/
theorem edge_refinement_iff_irredundant_strict_polynomial_diameter :
    PolynomialEdgeRefinementClaim ↔ IrredundantStrictPolynomialDiameter := by
  exact ⟨edge_refinement_implies_irredundant_strict_polynomial_diameter,
    irredundant_strict_polynomial_diameter_implies_edge_refinement⟩

#print axioms rowCircuitWalk_cubic_fixed_presentation
#print axioms edge_refinement_implies_irredundant_strict_polynomial_diameter
#print axioms irredundant_strict_polynomial_diameter_implies_edge_refinement
#print axioms edge_refinement_iff_irredundant_strict_polynomial_diameter

end HirschCircuit
