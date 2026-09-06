import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.AxisLocalPerturb

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

set_option maxHeartbeats 2500000

noncomputable section

namespace HirschAxisEdge

variable {d n : ℕ}

lemma inner_midpoint
    (a x y : EuclideanSpace ℝ (Fin d)) :
    ⟪a, midpoint ℝ x y⟫ = (⟪a, x⟫ + ⟪a, y⟫) / 2 := by
  rw [midpoint_eq_smul_add (R := ℝ) x y]
  simp [inner_add_right, inner_smul_right]
  ring

lemma midpoint_tight_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Hpoly a b) (hy : y ∈ Hpoly a b)
    (i : Fin n) :
    ⟪a i, midpoint ℝ x y⟫ = b i ↔
      ⟪a i, x⟫ = b i ∧ ⟪a i, y⟫ = b i := by
  rw [inner_midpoint]
  constructor
  · intro hm
    have hxle := hx i
    have hyle := hy i
    constructor <;> linarith
  · rintro ⟨hxi, hyi⟩
    rw [hxi, hyi]
    ring

/-- For an edge, the common active normals leave only the edge direction
unconstrained.  This is the active-normal form of “an edge is one-dimensional”. -/
lemma common_active_orthogonal_parallel
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x y z : EuclideanSpace ℝ (Fin d)}
    (hadj : Adj (Hpoly a b) x y)
    (hz : ∀ i,
      ⟪a i, x⟫ = b i → ⟪a i, y⟫ = b i → ⟪a i, z⟫ = 0) :
    ∃ α : ℝ, z = α • (y - x) := by
  rcases hadj with ⟨hxy, hextr⟩
  by_cases hz0 : z = 0
  · exact ⟨0, by simp [hz0]⟩
  have hxP : x ∈ Hpoly a b := hextr.subset (left_mem_segment ℝ x y)
  have hyP : y ∈ Hpoly a b := hextr.subset (right_mem_segment ℝ x y)
  let m := midpoint ℝ x y
  have hmseg : m ∈ segment ℝ x y := midpoint_mem_segment ℝ x y
  have hmP : m ∈ Hpoly a b := hextr.subset hmseg
  have hztight : ∀ i, ⟪a i, m⟫ = b i → ⟪a i, z⟫ = 0 := by
    intro i hi
    have hboth := (midpoint_tight_iff a b hxP hyP i).1 (by simpa [m] using hi)
    exact hz i hboth.1 hboth.2
  obtain ⟨ε, hε, hp, hq⟩ :=
    HirschAxisLocal.exists_two_sided_feasible_perturb a b hmP hztight
  let p := m - ε • z
  let q := m + ε • z
  have hp' : p ∈ Hpoly a b := by simpa [p] using hp
  have hq' : q ∈ Hpoly a b := by simpa [q] using hq
  have hεz : ε • z ≠ 0 := by
    exact (smul_ne_zero hε.ne' hz0)
  have hopen : m ∈ openSegment ℝ p q := by
    simpa [p, q] using
      (mem_openSegment_sub_add (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) m (ε • z))
  have hpseg : p ∈ segment ℝ x y :=
    hextr.left_mem_of_mem_openSegment hp' hq' hmseg hopen
  obtain ⟨α, β, hα, hβ, hαβ, hpcomb⟩ := hpseg
  have hpform : p = x + β • (y - x) := by
    calc
      p = α • x + β • y := hpcomb.symm
      _ = x + β • (y - x) := by
        rw [show α = 1 - β by linarith]
        module
  have hmform : m = x + (1 / 2 : ℝ) • (y - x) := by
    dsimp [m]
    rw [midpoint_eq_smul_add (R := ℝ)]
    module
  have hdisp : (-ε) • z = (β - 1 / 2) • (y - x) := by
    calc
      (-ε) • z = p - m := by
        rw [hpform, hmform]
        dsimp [p]
        module
      _ = (β - 1 / 2) • (y - x) := by
        rw [hpform, hmform]
        module
  refine ⟨(-ε)⁻¹ * (β - 1 / 2), ?_⟩
  have hs := congrArg (fun w : EuclideanSpace ℝ (Fin d) => (-ε)⁻¹ • w) hdisp
  simpa [smul_smul, hε.ne'] using hs.symm

end HirschAxisEdge
