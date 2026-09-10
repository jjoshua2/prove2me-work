import Solutions.PolynomialHpolyRecessionCap

/-! Compactness of the canonical far cap for a finite pointed H-polyhedron.
The proof embeds the ambient space by all row evaluations. The common-kernel
condition makes this a closed embedding; the original upper inequalities plus
one cap inequality give two-sided coordinate bounds in the image. -/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch Topology

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

def rowMap (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := fun x i => ⟪a i, x⟫
  map_add' := by
    intro x y
    ext i
    simp [inner_add_right]
  map_smul' := by
    intro c x
    ext i
    simp [inner_smul_right]

@[simp] lemma rowMap_apply
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    rowMap a x i = ⟪a i, x⟫ := rfl

def rowLower (b : Fin n → ℝ) (T : ℝ) (i : Fin n) : ℝ :=
  -T - (Finset.univ.erase i).sum b

def cappedHpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  Hpoly a b ∩ {x | ⟪capNormal a, x⟫ ≤ T}

lemma rowMap_ker_eq_bot
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, r⟫ = 0) → r = 0) :
    LinearMap.ker (rowMap a) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  have hdiff : x - y = 0 := hkernel (x - y) (by
    intro i
    have hi : ⟪a i, x⟫ = ⟪a i, y⟫ := congrFun hxy i
    rw [inner_sub_right, hi, sub_self])
  exact sub_eq_zero.mp hdiff

lemma rowMap_isClosedEmbedding
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, r⟫ = 0) → r = 0) :
    IsClosedEmbedding (rowMap a) := by
  exact LinearMap.isClosedEmbedding_of_injective (rowMap_ker_eq_bot a hkernel)

lemma capped_row_bounds
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ cappedHpoly a b T) :
    rowMap a x ∈ Set.Icc (rowLower b T) b := by
  rcases hx with ⟨hxH, hxcap⟩
  change ⟪capNormal a, x⟫ ≤ T at hxcap
  constructor
  · intro i
    have hsumInner : ⟪∑ j, a j, x⟫ = ∑ j, ⟪a j, x⟫ := by
      simpa using (sum_inner (Finset.univ : Finset (Fin n)) a x)
    have hsumEval : -T ≤ ∑ j, ⟪a j, x⟫ := by
      rw [capNormal, inner_neg_left, hsumInner] at hxcap
      linarith
    have hother :
        (Finset.univ.erase i).sum (fun j => ⟪a j, x⟫) ≤
          (Finset.univ.erase i).sum b := by
      exact Finset.sum_le_sum fun j _ => hxH j
    have hsplit :
        (Finset.univ.erase i).sum (fun j => ⟪a j, x⟫) + ⟪a i, x⟫ =
          ∑ j, ⟪a j, x⟫ := by
      exact Finset.sum_erase_add _ (Finset.mem_univ i)
    change rowLower b T i ≤ ⟪a i, x⟫
    rw [rowLower]
    linarith
  · intro i
    exact hxH i

lemma cappedHpoly_isClosed
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ) :
    IsClosed (cappedHpoly a b T) := by
  have hH : IsClosed (Hpoly a b) := by
    change IsClosed {x : EuclideanSpace ℝ (Fin d) | ∀ i, ⟪a i, x⟫ ≤ b i}
    rw [show {x : EuclideanSpace ℝ (Fin d) | ∀ i, ⟪a i, x⟫ ≤ b i} =
        ⋂ i, {x | ⟪a i, x⟫ ≤ b i} by ext x; simp]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hcap : IsClosed {x : EuclideanSpace ℝ (Fin d) | ⟪capNormal a, x⟫ ≤ T} :=
    isClosed_le (continuous_const.inner continuous_id) continuous_const
  exact hH.inter hcap

/-- A finite H-polyhedron with no common row kernel becomes compact after
intersecting it with the canonical summed-normal cap halfspace. -/
theorem cappedHpoly_isCompact
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (hkernel : ∀ r : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, r⟫ = 0) → r = 0) :
    IsCompact (cappedHpoly a b T) := by
  let K : Set (Fin n → ℝ) := Set.Icc (rowLower b T) b
  have hK : IsCompact K := isCompact_Icc
  have hpre : IsCompact ((rowMap a) ⁻¹' K) :=
    (rowMap_isClosedEmbedding a hkernel).isCompact_preimage hK
  apply hpre.of_isClosed_subset (cappedHpoly_isClosed a b T)
  intro x hx
  exact capped_row_bounds a b T hx

#print axioms rowMap_ker_eq_bot
#print axioms rowMap_isClosedEmbedding
#print axioms capped_row_bounds
#print axioms cappedHpoly_isClosed
#print axioms cappedHpoly_isCompact

end HirschHpolyCap
