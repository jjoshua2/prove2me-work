import Mathlib
import Solutions.PolynomialBalancedTargetRank
import Solutions.PolynomialFaceSparsePresentation
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

lemma sparse_adj_reverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Adj P v u := by
  refine ⟨Ne.symm h.1, ?_⟩
  simpa only [segment_symm] using h.2

/-- Every genuine edge leaving a vertex acquires a nonzero row that was not
active at the starting vertex. -/
lemma sparse_adjacent_acquires_new_nonzero_row {d n : ℕ}
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

/-- At exact balance, every neighbor of the source enters a supporting row of
the separated target. -/
theorem sparse_balanced_neighbor_hits_target_row
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
  obtain ⟨i, hai, hiz, hiu⟩ := sparse_adjacent_acquires_new_nonzero_row a b huz
  obtain ⟨_, hsource | htarget⟩ := balanced_rows_partition d a b u v hu hv hsep i
  · exact False.elim (hiu hsource.1)
  · exact ⟨i, hai, htarget.2, hiz⟩

/-- Sharing one nonzero row forces common-face dimension below the ambient
dimension. -/
theorem sparse_commonFaceDim_lt_of_shared_nonzero_row {d n : ℕ}
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

/-- A single source neighbor whose target-common face has an equivalent
subpresentation of at most twice its dimension closes the d-step induction. -/
theorem balanced_neighbor_dstep_of_sparse_target_face
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
    (hsparse : CommonFaceHasSubpresentationAtMost a b v z
      (2 * commonFaceDim a b v z))
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
    sparse_balanced_neighbor_hits_target_row d a b u v z hu hv hsep huz
  let e := commonFaceDim a b v z
  have he_lt : e < d := by
    dsimp [e]
    exact sparse_commonFaceDim_lt_of_shared_nonzero_row a b v z i hai hiv hiz
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
    exact commonFace_coord_diam_of_sparse_balanced
      a b v z hsparse hbalanced hQne hQbd
  obtain ⟨wt, hwt0, hwtE, hwtstep⟩ :=
    common_face_walk_of_coord_diam a b v z hv hz e hD
  let wr : ℕ → EuclideanSpace ℝ (Fin d) := fun j => wt (e - j)
  have hwr0 : wr 0 = z := by simpa [wr] using hwtE
  have hwrE : wr e = v := by simpa [wr] using hwt0
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
        have hrev := sparse_adj_reverse hadj
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

/-- In a minimal-dimensional d-step counterexample, no source neighbor may
have a target-common face representable by at most twice its dimension rows. -/
theorem balanced_counterexample_neighbors_not_sparse
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
      ¬ CommonFaceHasSubpresentationAtMost a b v z
        (2 * commonFaceDim a b v z) := by
  intro z huz hsparse
  exact hcounter (balanced_neighbor_dstep_of_sparse_target_face
    d a b hbd u v z hu hv hsep huz hsparse hsmall)

/-- Codimension-one specialization: a minimal counterexample cannot have a
source neighbor whose target-common `(d-1)`-face is describable by `2d-2` or
fewer rows. This is the formal H-presentation analogue of the classical
`2d-2` ridge sufficient condition. -/
theorem balanced_codim_one_counterexample_neighbor_not_sparse
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
    (hdim : commonFaceDim a b v z = d - 1)
    (hsmall : ∀ e : ℕ, e < d →
      ∀ (a' : Fin (2 * e) → EuclideanSpace ℝ (Fin e)) (b' : Fin (2 * e) → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') e)
    (hcounter : ¬ ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w d = v ∧
      ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))) :
    ¬ CommonFaceHasSubpresentationAtMost a b v z (2 * d - 2) := by
  intro hsparse
  obtain ⟨i, _, _, _⟩ :=
    sparse_balanced_neighbor_hits_target_row d a b u v z hu hv hsep huz
  have hdpos : 0 < d := by
    have hiLt := i.isLt
    omega
  have heq : 2 * commonFaceDim a b v z = 2 * d - 2 := by
    rw [hdim]
    omega
  apply balanced_counterexample_neighbors_not_sparse
    d a b hbd u v hu hv hsep hsmall hcounter z huz
  simpa only [heq] using hsparse

#print axioms diamLE_of_sparse_balanced_presentation
#print axioms balanced_neighbor_dstep_of_sparse_target_face
#print axioms balanced_counterexample_neighbors_not_sparse
#print axioms balanced_codim_one_counterexample_neighbor_not_sparse

end HirschPolynomialAccess
