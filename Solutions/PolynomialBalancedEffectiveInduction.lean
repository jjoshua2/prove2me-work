import Mathlib
import Solutions.PolynomialBalancedTargetRank
import Solutions.PolynomialFaceEffectiveRows
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

lemma adj_reverse_core {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Adj P v u := by
  refine ⟨Ne.symm h.1, ?_⟩
  simpa only [segment_symm] using h.2

/-- Every genuine edge leaving a vertex acquires a nonzero row that was not
active at the starting vertex. -/
lemma adjacent_acquires_new_nonzero_row_core {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u z : EuclideanSpace ℝ (Fin d)}
    (huz : Adj (Hpoly a b) u z) :
    ∃ i : Fin n,
      a i ≠ 0 ∧ ⟪a i, z⟫ = b i ∧ ⟪a i, u⟫ ≠ b i := by
  have hz : z ∈ extremePoints ℝ (Hpoly a b) :=
    adj_right_extreme (Hpoly a b) huz
  by_contra h
  push Not at h
  have horth : ∀ j, ⟪a j, z⟫ = b j → ⟪a j, z - u⟫ = 0 := by
    intro j hjz
    by_cases haj : a j = 0
    · simp [haj]
    · have hju : ⟪a j, u⟫ = b j := by
        by_contra hju
        exact h j haj hjz hju
      simp [inner_sub_right, hjz, hju]
  have hzero := vertex_tight_rows_span_checked d n a b z hz (z - u) horth
  have hzu : z = u := sub_eq_zero.mp hzero
  exact huz.1 hzu.symm

/-- At exact balance, every neighbor of the source in a separated pair enters
at least one supporting row of the target. No global diameter theorem is used. -/
theorem balanced_neighbor_hits_target_row
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (u v z : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (huz : Adj (Hpoly a b) u z) :
    ∃ i : Fin (2 * d),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧ ⟪a i, z⟫ = b i := by
  obtain ⟨i, hai, hiz, hiu⟩ := adjacent_acquires_new_nonzero_row_core a b huz
  obtain ⟨_, hsource | htarget⟩ := balanced_rows_partition d a b u v hu hv hsep i
  · exact False.elim (hiu hsource.1)
  · exact ⟨i, hai, htarget.2, hiz⟩

/-- Sharing one nonzero row forces the common-face direction space to be a
proper subspace, hence to have dimension strictly below the ambient one. -/
theorem commonFaceDim_lt_of_shared_nonzero_row {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hai : a i ≠ 0)
    (hip : ⟪a i, p⟫ = b i) (hiq : ⟪a i, q⟫ = b i) :
    commonFaceDim a b p q < d := by
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b p q
  have hWne : W ≠ ⊤ := by
    intro htop
    have haiW : a i ∈ W := by
      rw [htop]
      trivial
    have hiC : i ∈ commonSourceRows a b p q := by
      simp [commonSourceRows, hai, hip, hiq]
    have hker : rowEvalMap a (commonSourceRows a b p q) (a i) = 0 := by
      apply LinearMap.mem_ker.1
      simpa [W, commonDirection] using haiW
    have hinner : ⟪a i, a i⟫ = 0 := congrFun hker ⟨i, hiC⟩
    have hpos : 0 < ⟪a i, a i⟫ := real_inner_self_pos.mpr hai
    linarith
  have hlt : Module.finrank ℝ W <
      Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.finrank_lt hWne
  have hambient : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  simpa [W, commonFaceDim, hambient] using hlt

/-- One good first target face closes the d-step induction.

Assume the d-step diameter bound in every smaller dimension. If `z` is any
neighbor of the source and the target-common face `F(v,z)` has at most twice
its dimension in nonzero restricted row normals, then `u` reaches `v` in
exactly `d` padded edge steps. -/
theorem balanced_neighbor_dstep_of_effective_target_face
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v z : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (huz : Adj (Hpoly a b) u z)
    (heff : commonFaceEffectiveCount a b v z ≤
      2 * commonFaceDim a b v z)
    (hsmall : ∀ e : ℕ, e < d →
      ∀ (a' : Fin (2 * e) → EuclideanSpace ℝ (Fin e)) (b' : Fin (2 * e) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') e) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w d = v ∧
      ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let P := Hpoly a b
  have hz : z ∈ extremePoints ℝ P := adj_right_extreme P huz
  obtain ⟨i, hai, hiv, hiz⟩ :=
    balanced_neighbor_hits_target_row d a b u v z hu hv hsep huz
  let e := commonFaceDim a b v z
  have he_lt : e < d := by
    dsimp [e]
    exact commonFaceDim_lt_of_shared_nonzero_row a b v z i hai hiv hiz
  let Q := Hpoly (commonFaceA a b v z) (commonFaceB a b v z)
  have hQne : Q.Nonempty := by
    obtain ⟨qv, hqv, _⟩ := commonFacePoint_surjOn a b v z
      (commonFace_u_mem a b v z hv.1)
    exact ⟨qv, hqv⟩
  have hQbd : Bornology.IsBounded Q := commonFace_coord_bounded a b v z hbd
  have hbalanced : ∀
      (a' : Fin (2 * e) → EuclideanSpace ℝ (Fin e)) (b' : Fin (2 * e) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') e := hsmall e he_lt
  have hD : DiamLE Q e := by
    dsimp [Q, e]
    exact commonFace_coord_diam_of_balanced_effective
      a b v z hv.1 heff hbalanced hQne hQbd
  obtain ⟨wt, hwt0, hwtE, hwtstep⟩ :=
    common_face_walk_of_coord_diam a b v z hv hz e hD
  let wr : ℕ → EuclideanSpace ℝ (Fin d) := fun j => wt (e - j)
  have hwr0 : wr 0 = z := by
    simpa [wr] using hwtE
  have hwrE : wr e = v := by
    simpa [wr] using hwt0
  have hwrstep : ∀ j < e,
      wr j = wr (j + 1) ∨ Adj P (wr j) (wr (j + 1)) := by
    intro j hj
    have hk : e - (j + 1) < e := by omega
    have heq : e - (j + 1) + 1 = e - j := by omega
    rcases hwtstep (e - (j + 1)) hk with hsame | hadj
    · exact Or.inl (by
        change wt (e - j) = wt (e - (j + 1))
        simpa only [heq] using hsame.symm)
    · exact Or.inr (by
        change Adj P (wt (e - j)) (wt (e - (j + 1)))
        have hrev := adj_reverse_core hadj
        simpa only [heq] using hrev)
  let p : ℕ → EuclideanSpace ℝ (Fin d) := fun j => if j = 0 then u else z
  have hp0 : p 0 = u := by simp [p]
  have hp1 : p 1 = z := by simp [p]
  have hpstep : ∀ j < 1,
      p j = p (j + 1) ∨ Adj P (p j) (p (j + 1)) := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    exact Or.inr (by simpa [p] using huz)
  obtain ⟨w0, hw00, hw0E, hw0step⟩ :=
    HirschProduct.append_walk (Adj P) p wr hp0 hp1 hwr0 hwrE hpstep hwrstep
  have hlen : 1 + e ≤ d := by omega
  obtain ⟨w, hw0, hwd, hwstep⟩ :=
    HirschProduct.pad_walk (Adj P) hlen w0 hw00 hw0E hw0step
  exact ⟨w, hw0, hwd, hwstep⟩

/-- Necessary condition for a minimal-dimensional d-step counterexample:
every neighbor of the source has a target-common face with more than twice its
dimension in effective restricted rows. -/
theorem balanced_counterexample_neighbors_row_rich
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (hsmall : ∀ e : ℕ, e < d →
      ∀ (a' : Fin (2 * e) → EuclideanSpace ℝ (Fin e)) (b' : Fin (2 * e) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') e)
    (hcounter : ¬ ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w d = v ∧
      ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ∀ z, Adj (Hpoly a b) u z →
      2 * commonFaceDim a b v z < commonFaceEffectiveCount a b v z := by
  intro z huz
  by_contra hrich
  have heff : commonFaceEffectiveCount a b v z ≤
      2 * commonFaceDim a b v z := by omega
  exact hcounter (balanced_neighbor_dstep_of_effective_target_face
    d a b hbd u v z hu hv hsep huz heff hsmall)

#print axioms balanced_neighbor_hits_target_row
#print axioms commonFaceDim_lt_of_shared_nonzero_row
#print axioms balanced_neighbor_dstep_of_effective_target_face
#print axioms balanced_counterexample_neighbors_row_rich

end HirschPolynomialAccess
