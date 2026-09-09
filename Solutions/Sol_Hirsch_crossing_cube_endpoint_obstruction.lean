import Solutions.PolynomialCrossingCubeObstruction

open Set

noncomputable section

/-- Endpoint-only certificates on two crossing unit-cost repair regions do not
imply a five-step repair route: Boolean cubes of every dimension at least six
supply counterexamples.  The cube-edge relation and padded-route predicate are
expanded directly in this public statement. -/
theorem solution (d : ℕ) (hd : 6 ≤ d) :
    let R : Finset (Fin d) → Finset (Fin d) → Prop := fun x y =>
      ∃ k, (k ∉ x ∧ y = insert k x) ∨ (k ∉ y ∧ x = insert k y)
    ∃ (w : ℕ → Finset (Fin d)) (S : Bool → Set (Finset (Fin d))),
      (∀ b, ∀ x ∈ S b, ∀ y ∈ S b,
        ∃ q : ℕ → Finset (Fin d), q 0 = x ∧ q 1 = y ∧
          ∀ j < 1, q j = q (j + 1) ∨ R (q j) (q (j + 1))) ∧
      w 0 ∈ S false ∧ w 2 ∈ S false ∧
      w 1 ∈ S true ∧ w 3 ∈ S true ∧
      (∀ j < 3, (0 ≤ j ∧ j < 2) ∨ (1 ≤ j ∧ j < 3)) ∧
      ¬ (∃ q : ℕ → Finset (Fin d), q 0 = w 0 ∧ q 5 = w 3 ∧
          ∀ j < 5, q j = q (j + 1) ∨ R (q j) (q (j + 1))) := by
  dsimp
  simpa [HirschRegionRoute.Route, HirschRegionRoute.CubeAdj] using
    (HirschRegionRoute.crossing_cube_endpoint_certificate_insufficient d hd)

#print axioms solution
