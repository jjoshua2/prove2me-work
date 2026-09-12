import Solutions.PolynomialBasisStarMass

/-! Extract the target-tight basis required by the all-row mass construction.
No simplicity, row independence, or supplied basis is assumed at the target. -/
open Set Hirsch HirschRegionRoute HirschRadial HirschPolynomialAccess
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschTargetDeletion

/-- The existing vertex annihilator theorem implies that all tight normals span. -/
theorem target_tight_normals_span_top {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    Submodule.span ℝ (a '' {i | ⟪a i, v⟫ = b i}) = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  apply vertex_tight_rows_span_checked d n a b v hv z
  intro i hi
  have hai : a i ∈ Submodule.span ℝ (a '' {j | ⟪a j, v⟫ = b j}) :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal hai hz

/-- Select exactly d distinct original tight rows, with injective row evaluation.
This includes nonsimple targets with more than d tight rows. -/
theorem exists_target_tight_basis {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ e : Fin d ↪ Fin n,
      Function.Injective (HirschCircuit.rowMap (fun k => a (e k))) ∧
      ∀ k, ⟪a (e k), v⟫ = b (e k) := by
  classical
  let T := {i : Fin n | ⟪a i, v⟫ = b i}
  let normals : T → EuclideanSpace ℝ (Fin d) := fun i => a i.1
  have htop : Submodule.span ℝ (Set.range normals) = ⊤ := by
    have he : Set.range normals = a '' T := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i.1, i.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
    rw [he]
    exact target_tight_normals_span_top a b v hv
  obtain ⟨κ, f, hf, hspan, hli⟩ := exists_linearIndependent' ℝ normals
  letI : Fintype κ := Fintype.ofInjective f hf
  let B := Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card κ = d := by
    rw [← Module.finrank_eq_card_basis B]
    exact finrank_euclideanSpace_fin (𝕜 := ℝ)
  let q : Fin d ≃ κ := Fintype.equivOfCardEq (by simp [hcard])
  let e : Fin d ↪ Fin n :=
    ⟨fun k => (f (q k)).1, Subtype.val_injective.comp (hf.comp q.injective)⟩
  refine ⟨e, ?_, fun k => (f (q k)).2⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have horth : ∀ k : κ, ⟪B k, x-y⟫ = 0 := by
    intro k
    have h := congrFun hxy (q.symm k)
    change ⟪a (e (q.symm k)), x⟫ = ⟪a (e (q.symm k)), y⟫ at h
    have he : a (e (q.symm k)) = B k := by simp [e, B, normals]
    rw [he] at h
    simp [inner_sub_right, h]
  calc
    ⟪x-y, x-y⟫ = ⟪∑ k, B.repr (x-y) k • B k, x-y⟫ := by rw [B.sum_repr]
    _ = 0 := by simp [sum_inner, inner_smul_left, horth]

/-- Every bounded strictly feasible presentation and vertex pair admits a
cost-independent basis-star certificate with total carrier excess at most 3e.
The d-row basis is produced here, rather than supplied as an extra premise. -/
theorem exists_automatic_basis_star_linear_mass {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ e : Fin d ↪ Fin n,
      ∃ c : DeferredClipCertificate (Hpoly a b)
          (fun i : basisRemainingRows e => a i.1)
          (fun i : basisRemainingRows e => b i.1) 1 v u,
        ((clipRepairCutLegs c.legs).map fun leg =>
          HirschCircuitLocalization.commonFacePresentationExcess a b leg.entry leg.exit).sum ≤
            3*(n-d) := by
  obtain ⟨e, hinj, htight⟩ := exists_target_tight_basis a b v hv
  exact ⟨e, basis_star_exists_linear_carrier_mass a b v hv hbd e hinj htight o hstrict u hu⟩

#print axioms target_tight_normals_span_top
#print axioms exists_target_tight_basis
#print axioms exists_automatic_basis_star_linear_mass
end HirschTargetDeletion
