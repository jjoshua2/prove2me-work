import Solutions.PolynomialHpolyFarCapCompact

/-! Preservation of old H-polyhedron vertices and edges under a cap halfspace. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

lemma segment_mem_cap_of_endpoints
    (c : EuclideanSpace ℝ (Fin d)) (T : ℝ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : ⟪c, x⟫ ≤ T) (hy : ⟪c, y⟫ ≤ T) :
    segment ℝ x y ⊆ {z | ⟪c, z⟫ ≤ T} := by
  rintro z ⟨α, β, hα, hβ, hab, rfl⟩
  change ⟪c, α • x + β • y⟫ ≤ T
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  nlinarith

/-- An old extreme vertex satisfying the cap inequality remains an extreme
vertex after capping. -/
lemma old_vertex_survives_cap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hcap : ⟪capNormal a, x⟫ ≤ T) :
    x ∈ extremePoints ℝ (cappedHpoly a b T) := by
  apply inter_extremePoints_subset_extremePoints_of_subset inter_subset_left
  exact ⟨⟨hx.1, hcap⟩, hx⟩

/-- An old edge whose endpoints satisfy the cap inequality survives as the same
edge of the capped H-polyhedron. -/
lemma old_edge_survives_cap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    {x y : EuclideanSpace ℝ (Fin d)}
    (hxy : Adj (Hpoly a b) x y)
    (hx : ⟪capNormal a, x⟫ ≤ T) (hy : ⟪capNormal a, y⟫ ≤ T) :
    Adj (cappedHpoly a b T) x y := by
  refine ⟨hxy.1, hxy.2.mono inter_subset_left ?_⟩
  intro z hz
  exact ⟨hxy.2.subset hz, segment_mem_cap_of_endpoints (capNormal a) T hx hy hz⟩

#print axioms segment_mem_cap_of_endpoints
#print axioms old_vertex_survives_cap
#print axioms old_edge_survives_cap

end HirschHpolyCap
