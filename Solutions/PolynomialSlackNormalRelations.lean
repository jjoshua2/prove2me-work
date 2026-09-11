import Solutions.PolynomialSlackMomentCertificate
import Solutions.PolynomialVertexSpan

/-!
# Finite normal-relation witnesses for the excess-two slack model

A reference extreme vertex supplies injectivity. Two finite vector identities
supply the annihilating moments. All certificate data are ordinary real vectors
and scalars; no carrier diameter or unknown theorem is a hypothesis.

Existence of these relation witnesses from boundedness alone is separate work.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschExcessTwo

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HirschSlackMoment

/-- Any positive diagonal row scaling remains injective when the original
H-polyhedron has an extreme vertex. -/
theorem weightedRows_injective_of_extremePoint {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b)) :
    Function.Injective (weightedRows a c) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b z hz (x - y)
  intro i _
  have hi := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s i) hxy
  change c i * ⟪a i, x⟫ = c i * ⟪a i, y⟫ at hi
  have heq : ⟪a i, x⟫ = ⟪a i, y⟫ := mul_left_cancel₀ (ne_of_gt (hc i)) hi
  rw [inner_sub_right, heq, sub_self]

lemma weighted_normal_relation_eval {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (c : Fin n → ℝ)
    (hrel : (∑ i, c i • a i) = 0) (x : EuclideanSpace ℝ (Fin d)) :
    (∑ i, c i * ⟪a i, x⟫) = 0 := by
  have h := congrArg (fun y : EuclideanSpace ℝ (Fin d) => ⟪y, x⟫) hrel
  simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h

/-- Two finite vector relations imply both moments annihilate every row-map
image. The right-hand sides are not involved in this direction-space fact. -/
theorem normal_relations_annihilate_weightedRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (c t : Fin n → ℝ)
    (hfirst : (∑ i, c i • a i) = 0)
    (hsecond : (∑ i, (t i * c i) • a i) = 0) :
    ∀ x, momentMap t (weightedRows a c x) = 0 := by
  intro x
  apply Prod.ext
  · change (∑ i, c i * ⟪a i, x⟫) = 0
    exact weighted_normal_relation_eval a c hfirst x
  · change (∑ i, t i * (c i * ⟪a i, x⟫)) = 0
    simpa only [mul_assoc] using
      weighted_normal_relation_eval a (fun i => t i * c i) hsecond x

/-- A normalized positive normal relation, an independent second relation,
and a reference vertex provide the complete geometric diameter certificate.
The conclusion simultaneously covers every original row-support face. -/
theorem hpoly_and_row_faces_diamLE_two_of_normal_relations {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (ht : ∃ i j, t i ≠ t j)
    (hfirst : (∑ i, c i • a i) = 0)
    (hsecond : (∑ i, (t i * c i) • a i) = 0)
    (hmass : (∑ i, c i * b i) = 1)
    (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b)) :
    DiamLE (Hpoly a b) 2 ∧
      ∀ S : Finset (Fin n),
        DiamLE {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} 2 := by
  let mu : ℝ := ∑ i, t i * (c i * b i)
  have hL := weightedRows_injective_of_extremePoint a b c hc z hz
  have hzero := normal_relations_annihilate_weightedRows a c t hfirst hsecond
  have hoffset : momentMap t (weightedOffset b c) = (1, mu) := by
    apply Prod.ext
    · exact hmass
    · rfl
  refine ⟨hpoly_diamLE_two_of_positive_slack_certificate
    a b c t mu hn hc hL ht hzero hoffset, ?_⟩
  intro S
  exact row_support_diamLE_two_of_positive_slack_certificate
    a b c t mu hn hc hL ht hzero hoffset S

#print axioms weightedRows_injective_of_extremePoint
#print axioms normal_relations_annihilate_weightedRows
#print axioms hpoly_and_row_faces_diamLE_two_of_normal_relations

end HirschSlackMoment
