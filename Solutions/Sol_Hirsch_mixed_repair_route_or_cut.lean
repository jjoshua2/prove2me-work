import Solutions.PolynomialPortalCut

open scoped BigOperators
open Set

noncomputable section

/-- Finite repair regions and surviving bidirectional edges either give a
one-charge-per-region route or an explicit cut of the supplied repair network.
All public hypotheses and conclusions are expanded, with no local vocabulary
required in a future platform problem statement. -/
theorem solution {V ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i,
      ∃ q : ℕ → V, q 0 = x ∧ q (C i) = y ∧
        ∀ k < C i, q k = q (k + 1) ∨ R (q k) (q (k + 1)))
    (a b : κ → V) (hab : ∀ e, R (a e) (b e)) (hba : ∀ e, R (b e) (a e))
    (u v : V) :
    (∃ q : ℕ → V, q 0 = u ∧ q ((∑ i, C i) + Fintype.card κ) = v ∧
      ∀ k < (∑ i, C i) + Fintype.card κ,
        q k = q (k + 1) ∨ R (q k) (q (k + 1))) ∨
    ∃ U : Set V, u ∈ U ∧ v ∉ U ∧
      (∀ i, ∀ x ∈ S i, ∀ y ∈ S i, x ∈ U → y ∈ U) ∧
      ∀ e, (a e ∈ U ↔ b e ∈ U) := by
  exact HirschRegionRoute.route_or_mixed_closed_cut R S C hlocal a b hab hba u v

#print axioms solution
