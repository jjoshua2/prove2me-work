import Solutions.PolynomialHpolyHorizonEdge

/-! Complete local classification of vertices of the canonical capped finite
H-polyhedron: every cap vertex is old, or is on the horizon and adjacent to an
old H-polyhedron vertex. -/

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

lemma hpoly_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy α β hα hβ hab
  intro i
  change ⟪a i, α • x + β • y⟫ ≤ b i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith [hx i, hy i]

/-- A genuinely new horizon cap vertex is adjacent, in the capped graph, to an
old H-polyhedron vertex reached by the finite first-hit construction. -/
theorem new_horizon_adjacent_old_vertex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hnotold : x ∉ extremePoints ℝ (Hpoly a b)) :
    ∃ y, y ∈ extremePoints ℝ (Hpoly a b) ∧
      Adj (cappedHpoly a b T) y x := by
  obtain ⟨r, t, j, hr0, ht, hrActive, hrCap, hjpos, hjhit, hyOld, hyCap⟩ :=
    new_horizon_first_hit_old_vertex a b T x hx horizon hnotold
  let y := x + t • r
  have hadj : Adj (cappedHpoly a b T) y x :=
    first_hit_segment_adjacent a b T x r t j hx horizon hr0 ht hrActive hrCap
      hjpos hyOld.1 hjhit
  exact ⟨y, hyOld, hadj⟩

/-- Every extreme vertex of the canonical cap is either an old H-polyhedron
vertex, or a horizon vertex adjacent to one. -/
theorem cap_vertex_old_or_horizon_adjacent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T)) :
    x ∈ extremePoints ℝ (Hpoly a b) ∨
      (⟪capNormal a, x⟫ = T ∧
        ∃ y, y ∈ extremePoints ℝ (Hpoly a b) ∧
          Adj (cappedHpoly a b T) y x) := by
  have hcaple : ⟪capNormal a, x⟫ ≤ T := hx.1.2
  rcases hcaple.eq_or_lt with heq | hlt
  · by_cases hold : x ∈ extremePoints ℝ (Hpoly a b)
    · exact Or.inl hold
    · exact Or.inr ⟨heq, new_horizon_adjacent_old_vertex a b T x hx heq hold⟩
  · left
    have hx' : x ∈ extremePoints ℝ
        (Hpoly a b ∩ {z | ⟪capNormal a, z⟫ ≤ T}) := by
      simpa [cappedHpoly] using hx
    exact HirschCut.strict_cut_extreme_to_parent
      (Hpoly a b) (hpoly_convex a b) (capNormal a) T hx' hlt

#print axioms hpoly_convex
#print axioms new_horizon_adjacent_old_vertex
#print axioms cap_vertex_old_or_horizon_adjacent

end HirschHpolyCap
