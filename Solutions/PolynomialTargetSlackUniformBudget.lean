import Mathlib
import Solutions.PolynomialTargetConeBatchReinsertion
import Solutions.PolynomialCircuitInjectiveNeutralRank

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschRegionRoute

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschTargetDeletion

/-- At a vertex, at least `d` describing rows are tight. Equivalently, the
number of rows strictly slack at that target is at most the presentation row
excess `n-d`. No boundedness or irredundancy assumption is needed. -/
theorem target_slack_rows_card_le_rowExcess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    (Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)).card ≤ n - d := by
  classical
  let J : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)
  have hJ : ∀ i ∈ J, ⟪a i, v⟫ < b i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨m, hcount, e, _hret, hinj, _hv', _hrecover⟩ :=
    exists_target_preserving_batch_deletion a b v hv J hJ
  have hdm : d ≤ m :=
    HirschCircuitLocalization.rows_ge_dimension_of_injective
      (fun k => a (e k)) hinj
  change J.card ≤ n - d
  omega

/-- Uniform-budget specialization of target-cone batch reinsertion.

If every final face belonging to a row strictly slack at target `v` admits an
ambient parent-edge route of the SAME budget `B`, then the whole parent has
padded diameter `2 + (n-d)*B`, and `v` reaches every parent vertex within
`1 + (n-d)*B`.

The face routes may leave their corresponding face. This theorem only packages
the row-excess cardinality bound with the verified simultaneous batch repair;
it does not supply the face budget `B`. -/
theorem target_slack_batch_reinsertion_uniform_parent_face_bound
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hFaces : ∀ i : Fin n, ⟪a i, v⟫ < b i →
      ∀ p ∈ extremePoints ℝ (Hpoly a b), ⟪a i, p⟫ = b i →
      ∀ q ∈ extremePoints ℝ (Hpoly a b), ⟪a i, q⟫ = b i →
        Route (Adj (Hpoly a b)) B p q) :
    DiamLE (Hpoly a b) (2 + (n - d) * B) ∧
    (∀ u ∈ extremePoints ℝ (Hpoly a b),
      Route (Adj (Hpoly a b)) (1 + (n - d) * B) v u) := by
  classical
  let J : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)
  have hJiff : ∀ i, i ∈ J ↔ ⟪a i, v⟫ < b i := by
    intro i
    simp [J]
  have hbatch := target_slack_batch_reinsertion_with_parent_routes
    a b v hv hbd J hJiff (fun _ => B)
    (by
      intro i hi p hp hpi q hq hqi
      exact hFaces i ((hJiff i).mp hi) p hp hpi q hq hqi)
  have hcard : J.card ≤ n - d := by
    simpa [J] using target_slack_rows_card_le_rowExcess a b v hv
  have hsum : (∑ _i : J, B) = J.card * B := by
    simp
  have hmul : J.card * B ≤ (n - d) * B :=
    Nat.mul_le_mul_right B hcard
  have hdiamLe : 2 + J.card * B ≤ 2 + (n - d) * B :=
    Nat.add_le_add_left hmul 2
  have hrootLe : 1 + J.card * B ≤ 1 + (n - d) * B :=
    Nat.add_le_add_left hmul 1
  constructor
  · intro p hp q hq
    obtain ⟨w, hw0, hwB, hstep⟩ := hbatch.1 p hp q hq
    rw [hsum] at hwB hstep
    exact HirschProduct.pad_walk (Adj (Hpoly a b)) hdiamLe
      w hw0 hwB hstep
  · intro u hu
    obtain ⟨w, hw0, hwB, hstep⟩ := hbatch.2 u hu
    rw [hsum] at hwB hstep
    exact HirschProduct.pad_walk (Adj (Hpoly a b)) hrootLe
      w hw0 hwB hstep

#print axioms target_slack_rows_card_le_rowExcess
#print axioms target_slack_batch_reinsertion_uniform_parent_face_bound

end HirschTargetDeletion
