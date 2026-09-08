import Solutions.CircuitConformalPiece

set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators

namespace HirschCircuit

/-- Conformality is transitive. -/
theorem conformalTo_trans {n : ℕ} {x y z : Fin n → ℝ}
    (hxy : ConformalTo x y) (hyz : ConformalTo y z) :
    ConformalTo x z := by
  intro i
  constructor
  · rcases le_total 0 (z i) with hz | hz
    · have hy0 := conformalTo_coord_nonneg_of_right_nonneg hyz hz
      have hx0 := conformalTo_coord_nonneg_of_right_nonneg hxy hy0
      exact mul_nonneg hx0 hz
    · have hy0 := conformalTo_coord_nonpos_of_right_nonpos hyz hz
      have hx0 := conformalTo_coord_nonpos_of_right_nonpos hxy hy0
      exact mul_nonneg_of_nonpos_of_nonpos hx0 hz
  · exact (hxy i).2.trans (hyz i).2

/-- Any vector in a finite-dimensional subspace is an exact sum of elementary
vectors conformal to it, using no more pieces than its support cardinality. -/
theorem exists_elementary_conformal_decomposition {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (z : Fin n → ℝ) (hzK : z ∈ K) :
    ∃ gs : List (Fin n → ℝ),
      gs.length ≤ (supportFinset z).card ∧
      (∀ g ∈ gs, IsElementaryIn K g ∧ ConformalTo g z) ∧
      gs.sum = z := by
  classical
  have aux : ∀ k : ℕ, ∀ z : Fin n → ℝ,
      z ∈ K → (supportFinset z).card = k →
      ∃ gs : List (Fin n → ℝ),
        gs.length ≤ (supportFinset z).card ∧
        (∀ g ∈ gs, IsElementaryIn K g ∧ ConformalTo g z) ∧
        gs.sum = z := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro z hzK hk
      by_cases hz0 : z = 0
      · subst z
        refine ⟨[], by simp, ?_, by simp⟩
        simp
      · obtain ⟨g, hgelem, hgconf, hresconf, hcardlt⟩ :=
          exists_saturating_elementary_conformal K hzK hz0
        let r : Fin n → ℝ := z - g
        have hrK : r ∈ K := by
          exact K.sub_mem hzK hgelem.2.1
        have hrlt : (supportFinset r).card < k := by
          simpa [r, hk] using hcardlt
        obtain ⟨gs, hlen, hall, hsum⟩ :=
          ih (supportFinset r).card hrlt r hrK rfl
        refine ⟨g :: gs, ?_, ?_, ?_⟩
        · simp only [List.length_cons]
          omega
        · intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨hgelem, hgconf⟩
          · obtain ⟨hpelem, hpconf⟩ := hall p hp
            exact ⟨hpelem, conformalTo_trans hpconf hresconf⟩
        · rw [List.sum_cons, hsum]
          dsimp [r]
          funext i
          simp only [Pi.add_apply, Pi.sub_apply]
          ring
  exact aux (supportFinset z).card z hzK rfl

/-- The decomposition above uses at most the ambient number of coordinates. -/
theorem exists_elementary_conformal_decomposition_le_n {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (z : Fin n → ℝ) (hzK : z ∈ K) :
    ∃ gs : List (Fin n → ℝ),
      gs.length ≤ n ∧
      (∀ g ∈ gs, IsElementaryIn K g ∧ ConformalTo g z) ∧
      gs.sum = z := by
  obtain ⟨gs, hlen, hall, hsum⟩ :=
    exists_elementary_conformal_decomposition K z hzK
  refine ⟨gs, ?_, hall, hsum⟩
  have hcard : (supportFinset z).card ≤ n := by
    have hsub : supportFinset z ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.card_le_card hsub
    simpa using this
  exact hlen.trans hcard

#print axioms conformalTo_trans
#print axioms exists_elementary_conformal_decomposition
#print axioms exists_elementary_conformal_decomposition_le_n

end HirschCircuit
