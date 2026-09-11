import Definitions.Def_Hirsch_circuit_model

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschCircuit

variable {d n : ℕ}

/-- Two consecutive maximal circuit augmentations commute when no describing
row changes along both displacements. The intermediate point is replaced, but
both displacements, maximality, and the final endpoint are preserved.
Neither the start nor the intermediate points need to be vertices. -/
theorem rowCircuitStep_swap_of_rowwise_separation
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y z : EuclideanSpace ℝ (Fin d))
    (hxy : RowCircuitStep a b x y) (hyz : RowCircuitStep a b y z)
    (hsep : ∀ i, ⟪a i, y - x⟫ = 0 ∨ ⟪a i, z - y⟫ = 0) :
    RowCircuitStep a b x (x + (z - y)) ∧
      RowCircuitStep a b (x + (z - y)) z := by
  let w := x + (z - y)
  have hfirst : w - x = z - y := by dsimp [w]; abel
  have hsecond : z - w = y - x := by dsimp [w]; abel
  have hw : w ∈ Hpoly a b := by
    intro i
    rcases hsep i with hg | hh
    · have hi := hyz.2.1 i
      rw [inner_sub_right] at hg
      dsimp [w]
      rw [inner_add_right, inner_sub_right]
      linarith
    · dsimp [w]
      rw [inner_add_right, hh, add_zero]
      exact hxy.1 i
  constructor
  · change RowCircuitStep a b x w
    refine ⟨hxy.1, hw, ?_, ?_⟩
    · rw [hfirst]
      exact hyz.2.2.1
    · intro t ht hfeas
      apply hyz.2.2.2 t ht
      intro i
      rcases hsep i with hg | hh
      · have hval : ⟪a i, y⟫ = ⟪a i, x⟫ := by
          rw [inner_sub_right] at hg
          linarith
        have hi := hfeas i
        rw [hfirst, inner_add_right, inner_smul_right] at hi
        rw [inner_add_right, inner_smul_right, hval]
        exact hi
      · rw [inner_add_right, inner_smul_right, hh, mul_zero, add_zero]
        exact hyz.1 i
  · change RowCircuitStep a b w z
    refine ⟨hw, hyz.2.1, ?_, ?_⟩
    · rw [hsecond]
      exact hxy.2.2.1
    · intro t ht hfeas
      apply hxy.2.2.2 t ht
      intro i
      rcases hsep i with hg | hh
      · rw [inner_add_right, inner_smul_right, hg, mul_zero, add_zero]
        exact hxy.1 i
      · have hval : ⟪a i, w⟫ = ⟪a i, x⟫ := by
          dsimp [w]
          rw [inner_add_right, hh, add_zero]
        have hi := hfeas i
        rw [hsecond, inner_add_right, inner_smul_right, hval] at hi
        exact hi

/-- Support-set formulation of the maximal-step commutation lemma. -/
theorem rowCircuitStep_swap_of_disjoint_support
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y z : EuclideanSpace ℝ (Fin d))
    (hxy : RowCircuitStep a b x y) (hyz : RowCircuitStep a b y z)
    (hdis : Disjoint (circuitRowSupport a (y - x)) (circuitRowSupport a (z - y))) :
    RowCircuitStep a b x (x + (z - y)) ∧
      RowCircuitStep a b (x + (z - y)) z := by
  classical
  apply rowCircuitStep_swap_of_rowwise_separation a b x y z hxy hyz
  intro i
  by_cases hg : ⟪a i, y - x⟫ = 0
  · exact Or.inl hg
  · right
    by_contra hh
    have hi1 : i ∈ circuitRowSupport a (y - x) := hg
    have hi2 : i ∈ circuitRowSupport a (z - y) := hh
    exact Set.disjoint_left.1 hdis hi1 hi2

/-- Candidate extension, not yet kernel-checked: a tight increasing row is
an exact witness of maximality for a feasible normalized circuit segment. -/
theorem rowCircuitStep_of_feasible_of_tight_increasing_row
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Hpoly a b) (hy : y ∈ Hpoly a b)
    (hg : IsRowCircuit a (y - x)) (i : Fin n)
    (htight : ⟪a i, y⟫ = b i)
    (hpos : 0 < ⟪a i, y - x⟫) : RowCircuitStep a b x y := by
  refine ⟨hx, hy, hg, ?_⟩
  intro t ht hfeas
  have hrow := hfeas i
  rw [inner_add_right, inner_smul_right] at hrow
  have hend : ⟪a i, x⟫ + ⟪a i, y - x⟫ = b i := by
    rw [inner_sub_right]
    linarith
  have hinc : 0 < (t - 1) * ⟪a i, y - x⟫ :=
    mul_pos (sub_pos.mpr ht) hpos
  nlinarith

/-- Candidate extension, not yet kernel-checked: overlapping row supports are
allowed. Feasibility of the swapped point and a tight increasing blocker for
EACH swapped segment certify preservation of both original displacements and
maximality. This is not a claim about adjacency or carrier-diameter cost. -/
theorem rowCircuitStep_swap_of_feasible_and_tight_blockers
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y z : EuclideanSpace ℝ (Fin d))
    (hxy : RowCircuitStep a b x y) (hyz : RowCircuitStep a b y z)
    (hw : x + (z - y) ∈ Hpoly a b) (i j : Fin n)
    (hi : ⟪a i, x + (z - y)⟫ = b i)
    (hipos : 0 < ⟪a i, z - y⟫)
    (hj : ⟪a j, z⟫ = b j)
    (hjpos : 0 < ⟪a j, y - x⟫) :
    RowCircuitStep a b x (x + (z - y)) ∧
      RowCircuitStep a b (x + (z - y)) z := by
  let w := x + (z - y)
  have hfirst : w - x = z - y := by dsimp [w]; abel
  have hsecond : z - w = y - x := by dsimp [w]; abel
  constructor
  · change RowCircuitStep a b x w
    refine rowCircuitStep_of_feasible_of_tight_increasing_row a b x w hxy.1 hw
      ?_ i hi ?_
    · rw [hfirst]
      exact hyz.2.2.1
    · rw [hfirst]
      exact hipos
  · change RowCircuitStep a b w z
    refine rowCircuitStep_of_feasible_of_tight_increasing_row a b w z hw hyz.2.1
      ?_ j hj ?_
    · rw [hsecond]
      exact hxy.2.2.1
    · rw [hsecond]
      exact hjpos

#print axioms rowCircuitStep_of_feasible_of_tight_increasing_row
#print axioms rowCircuitStep_swap_of_feasible_and_tight_blockers

#print axioms rowCircuitStep_swap_of_rowwise_separation
#print axioms rowCircuitStep_swap_of_disjoint_support

end HirschCircuit
