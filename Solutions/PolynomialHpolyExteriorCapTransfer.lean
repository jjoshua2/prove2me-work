import Solutions.PolynomialHpolyHorizonClassify
import Solutions.PolynomialExteriorCapNoStrict
import Solutions.PolynomialAdjEndpoints

/-! Concrete exterior-cap transfer for a finite pointed H-polyhedron.

The abstract compact cap, exterior region, old-vertex routes, and cap-vertex
classification required by the generic exterior clipping theorem are all
constructed from the canonical summed-normal cap.  The only cap-level inputs
left are that the chosen level lies above every old H-vertex and strictly above
the final clipped polytope. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRadial HirschRegionRoute

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ} {ι : Type*} [Fintype ι]

/-- The horizon face of the canonical capped H-polyhedron. -/
def horizonCap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  cappedHpoly a b T ∩ {x | ⟪capNormal a, x⟫ = T}

lemma cappedHpoly_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    Convex ℝ (cappedHpoly a b T) := by
  intro x hx y hy α β hα hβ hab
  constructor
  · exact hpoly_convex a b hx.1 hy.1 hα hβ hab
  · change ⟪capNormal a, α • x + β • y⟫ ≤ T
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have hx' : α * ⟪capNormal a, x⟫ ≤ α * T :=
      mul_le_mul_of_nonneg_left hx.2 hα
    have hy' : β * ⟪capNormal a, y⟫ ≤ β * T :=
      mul_le_mul_of_nonneg_left hy.2 hβ
    calc
      α * ⟪capNormal a, x⟫ + β * ⟪capNormal a, y⟫ ≤ α * T + β * T :=
        add_le_add hx' hy'
      _ = (α + β) * T := by ring
      _ = T := by rw [hab, one_mul]

lemma horizonCap_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    Convex ℝ (horizonCap a b T) := by
  intro x hx y hy α β hα hβ hab
  constructor
  · exact cappedHpoly_convex a b T hx.1 hy.1 hα hβ hab
  · change ⟪capNormal a, α • x + β • y⟫ = T
    rw [inner_add_right, inner_smul_right, inner_smul_right, hx.2, hy.2]
    calc
      α * T + β * T = (α + β) * T := by ring
      _ = T := by rw [hab, one_mul]

/-- If the final clipped set lies strictly below the cap level, capping the
outer H-polyhedron does not change that final set. -/
lemma finalClip_capped_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ) (T : ℝ)
    (hFinalBelow : ∀ x ∈ finalClip (Hpoly a b) f c, ⟪capNormal a, x⟫ < T) :
    finalClip (cappedHpoly a b T) f c = finalClip (Hpoly a b) f c := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hx.1.1, hx.2⟩
  · intro x hx
    exact ⟨⟨hx.1, (hFinalBelow x hx).le⟩, hx.2⟩

/-- A padded old H-polyhedron diameter route survives the cap whenever every
old H-vertex is below the chosen cap level.  Extremality of intermediate edge
endpoints is recovered from `Adj`, rather than assumed separately. -/
lemma old_diameter_routes_survive_cap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hOldBelow : ∀ x ∈ extremePoints ℝ (Hpoly a b), ⟪capNormal a, x⟫ ≤ T) :
    ∀ u ∈ extremePoints ℝ (Hpoly a b), ∀ v ∈ extremePoints ℝ (Hpoly a b),
      Route (Adj (cappedHpoly a b T)) D u v := by
  intro u hu v hv
  obtain ⟨w, hw0, hwD, hwstep⟩ := hD u hu v hv
  refine ⟨w, hw0, hwD, ?_⟩
  intro k hk
  rcases hwstep k hk with hstay | hedge
  · exact Or.inl hstay
  · right
    have hleft : w k ∈ extremePoints ℝ (Hpoly a b) :=
      HirschPolynomialAccess.adj_left_extreme (Hpoly a b) hedge
    have hright : w (k + 1) ∈ extremePoints ℝ (Hpoly a b) :=
      HirschPolynomialAccess.adj_right_extreme (Hpoly a b) hedge
    exact old_edge_survives_cap a b T hedge
      (hOldBelow (w k) hleft) (hOldBelow (w (k + 1)) hright)

/-- Concrete pointed-H-polyhedron exterior-cap diameter transfer.

`hkernel` is the finite H-representation form of pointedness: the row normals
have no nonzero common kernel direction.  A cap level `T` above every old
H-vertex and strictly above the final clipped set yields a compact canonical
outer cap.  If the old H-vertex graph has padded diameter `D` and final cut
face `i` has diameter at most `B i`, then the final simultaneous clip has
padded diameter at most `D + 1 + Σ_i B i`. -/
theorem simultaneous_clip_diameter_from_finite_hpoly_far_cap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ι → ℝ)
    (T : ℝ)
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ j, ⟪a j, r⟫ = 0) → r = 0)
    (D : ℕ) (hD : DiamLE (Hpoly a b) D)
    (hOldBelow : ∀ x ∈ extremePoints ℝ (Hpoly a b), ⟪capNormal a, x⟫ ≤ T)
    (hFinalBelow : ∀ x ∈ finalClip (Hpoly a b) f c, ⟪capNormal a, x⟫ < T)
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE (finalClip (Hpoly a b) f c ∩ {x | f i x = c i}) (B i)) :
    DiamLE (finalClip (Hpoly a b) f c) (D + 1 + ∑ i, B i) := by
  let R := cappedHpoly a b T
  let G := horizonCap a b T
  let V := extremePoints ℝ (Hpoly a b)
  have hR : Convex ℝ R := cappedHpoly_convex a b T
  have hRc : IsCompact R := cappedHpoly_isCompact a b T hkernel
  have hG : Convex ℝ G := horizonCap_convex a b T
  have hGR : G ⊆ R := inter_subset_left
  have hEq : finalClip R f c = finalClip (Hpoly a b) f c := by
    exact finalClip_capped_eq a b f c T hFinalBelow
  have hout : ∀ x ∈ G, x ∉ finalClip R f c := by
    intro x hxG hxP
    have hxOrig : x ∈ finalClip (Hpoly a b) f c := by
      rw [← hEq]
      exact hxP
    exact (ne_of_lt (hFinalBelow x hxOrig)) hxG.2
  have hOld : ∀ u ∈ V, ∀ v ∈ V, Route (Adj R) D u v := by
    exact old_diameter_routes_survive_cap a b T D hD hOldBelow
  have hclass : ∀ x ∈ extremePoints ℝ R,
      x ∈ V ∨ (x ∈ G ∧ ∃ y ∈ V, Adj R y x) := by
    intro x hx
    rcases cap_vertex_old_or_horizon_adjacent a b T x hx with hold | ⟨hhorizon, y, hy, hadj⟩
    · exact Or.inl hold
    · exact Or.inr ⟨⟨hx.1, hhorizon⟩, y, hy, hadj⟩
  have hB' : ∀ i, DiamLE (finalClip R f c ∩ {x | f i x = c i}) (B i) := by
    intro i
    rw [hEq]
    exact hB i
  have hres := HirschExterior.simultaneous_clip_diameter_from_exterior_cap_no_strict
    R G V hR hRc hG hGR f c hout D hOld hclass B hB'
  rw [hEq] at hres
  exact hres

#print axioms horizonCap_convex
#print axioms finalClip_capped_eq
#print axioms old_diameter_routes_survive_cap
#print axioms simultaneous_clip_diameter_from_finite_hpoly_far_cap

end HirschHpolyCap
