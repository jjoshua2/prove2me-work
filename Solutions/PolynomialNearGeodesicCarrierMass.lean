import Solutions.PolynomialNearGeodesicMassBridge
import Solutions.PolynomialAllCutCarrierMass

/-!
# Carrier mass for optimized near-geodesic portal walks

The face and actual pair at each charged position are explicit. A repeated
label is permitted and its pair is charged again. Full availability s=n-d
cancels the occurrence-count term, leaving (k+3)(n-d) total excess.
No small rank, small excess, simplex type, or distance bound is assumed.
New candidate: the local Lean and axiom gates have not been run here.
-/
open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschCircuitLocalization

/-- Repeated labels remain separate indices. The current pair must really
lie on the current nonzero defining row, exactly as in #206's saving lemma. -/
theorem near_geodesic_actual_pair_mass
    {d n : ℕ} {V : Type*} [DecidableEq V]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : V → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact (Hpoly a b)) (hbd : Bornology.IsBounded (Hpoly a b))
    (hF : ∀ i, IsExtreme ℝ (Hpoly a b) (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (available : Finset V) (row : V → Fin n)
    (hinj : Set.InjOn row (↑available : Set V))
    (hfaces : ∀ i ∈ available, F i = hpolyRowFace a b (row i))
    {s t : V}
    (p : (intersectionGraph (fun i => extremePoints ℝ (Hpoly a b) ∩ F i)).Walk s t)
    (k : ℕ)
    (hnear : p.length ≤
      (intersectionGraph (fun i => extremePoints ℝ (Hpoly a b) ∩ F i)).dist s t + k)
    (positions : Finset ℕ) (hpos : positions ⊆ Finset.range (p.length+1))
    (hlabels : ∀ j ∈ positions, p.getVert j ∈ available)
    (entry exit : ℕ → EuclideanSpace ℝ (Fin d))
    (hentry : ∀ j ∈ positions, entry j ∈ extremePoints ℝ (Hpoly a b))
    (hexit : ∀ j ∈ positions, exit j ∈ extremePoints ℝ (Hpoly a b))
    (hnormal : ∀ j ∈ positions, a (row (p.getVert j)) ≠ 0)
    (htight₁ : ∀ j ∈ positions, ⟪a (row (p.getVert j)), entry j⟫ = b (row (p.getVert j)))
    (htight₂ : ∀ j ∈ positions, ⟪a (row (p.getVert j)), exit j⟫ = b (row (p.getVert j))) :
    (∑ j ∈ positions, commonFacePresentationExcess a b (entry j) (exit j)) +
      positions.card * available.card ≤
      positions.card * (n-d) + (k+3) * available.card := by
  have hlocal : ∀ j ∈ positions,
      commonFacePresentationExcess a b (entry j) (exit j) + available.card ≤
        (n-d) + availableContactLoad
          (intersectionGraph (fun i => extremePoints ℝ (Hpoly a b) ∩ F i))
          available (p.getVert j) := by
    intro j hj
    exact commonFace_available_contact_budget a b F hP hbd hF hclosed
      available row hinj hfaces (p.getVert j) (hlabels j hj) (entry j) (exit j)
      (hentry j hj) (hexit j hj) (hnormal j hj) (htight₁ j hj) (htight₂ j hj)
  have hs := Finset.sum_le_sum hlocal
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  have hloads := near_geodesic_total_position_load p k hnear available positions hpos
  omega

/-- Arithmetic cancellation does not need a bound on the occurrence count.
It is valid for walks with repeated cuts. -/
theorem full_available_mass_cancellation (mass occurrences e k : ℕ)
    (h : mass + occurrences*e ≤ occurrences*e + (k+3)*e) :
    mass ≤ (k+3)*e := by omega

/-- Once actual local edge costs have a certified per-excess multiplier K,
controlled detours have no additional occurrence-count penalty. -/
theorem finite_cost_sum_of_mass_cap
    {α : Type*} (I : Finset α) (cost mass : α → ℕ) (K e k : ℕ)
    (hlocal : ∀ i ∈ I, cost i ≤ K * mass i)
    (hmass : (∑ i ∈ I, mass i) ≤ (k+3)*e) :
    (∑ i ∈ I, cost i) ≤ K*(k+3)*e := by
  have hs := Finset.sum_le_sum hlocal
  rw [← Finset.mul_sum] at hs
  have h := hs.trans (Nat.mul_le_mul_left K hmass)
  simpa only [Nat.mul_assoc] using h

#print axioms near_geodesic_actual_pair_mass
#print axioms full_available_mass_cancellation
#print axioms finite_cost_sum_of_mass_cap
end HirschCircuitLocalization
