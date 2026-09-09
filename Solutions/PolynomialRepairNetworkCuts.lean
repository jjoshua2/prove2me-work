import Solutions.PolynomialMixedRegionRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- Every partition of the region labels separating the endpoint labels
has a genuine shared point across it. No chronological overlap is used. -/
def RegionCutCondition {V ι : Type*} (S : ι → Set V) (i j : ι) : Prop :=
  ∀ A : Set ι, i ∈ A → j ∉ A →
    ∃ a ∈ A, ∃ b, b ∉ A ∧ ∃ z, z ∈ S a ∧ z ∈ S b

/-- A reachable region cannot be separated from the start by disjoint regions. -/
lemma region_cut_condition_of_walk {V ι : Type*} (S : ι → Set V)
    {i j : ι} (p : (intersectionGraph S).Walk i j) :
    RegionCutCondition S i j := by
  classical
  induction p with
  | @nil i =>
      intro A hi hj
      exact (hj hi).elim
  | @cons i k j hik p ih =>
      intro A hi hj
      by_cases hk : k ∈ A
      · exact ih A hk hj
      · exact ⟨i, hi, k, hk, hik.2⟩

/-- The reachable-label set supplies a separating cut whenever no region
walk exists. This is an exact certificate criterion, not parent connectivity. -/
theorem region_walk_iff_cut_condition {V ι : Type*} (S : ι → Set V)
    (i j : ι) :
    Nonempty ((intersectionGraph S).Walk i j) ↔ RegionCutCondition S i j := by
  classical
  constructor
  · rintro ⟨p⟩
    exact region_cut_condition_of_walk S p
  · intro hcut
    by_contra hno
    let A : Set ι := {k | Nonempty ((intersectionGraph S).Walk i k)}
    have hi : i ∈ A := ⟨.nil⟩
    have hj : j ∉ A := hno
    obtain ⟨a, ha, b, hb, z, hza, hzb⟩ := hcut A hi hj
    obtain ⟨p⟩ := ha
    obtain ⟨q⟩ := shared_point_walk S hza hzb
    exact hb ⟨p.append q⟩

/-- A finite repair network pays each available region once, provided every
separating label cut has an actual shared-point bridge. -/
theorem route_of_region_cut_condition {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ k, ∀ x ∈ S k, ∀ y ∈ S k, Route R (C k) x y)
    (i j : ι) (hcut : RegionCutCondition S i j)
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    Route R (∑ k, C k) u v := by
  exact route_of_connected_regions R S C hlocal
    ((region_walk_iff_cut_condition S i j).mpr hcut) u v hu hv

/-- A selected finite subfamily is enough; unused regions incur no charge.
The ambient label type need not itself be finite. -/
theorem route_of_subfamily_cut_condition {V ι : Type*}
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ) (K : Finset ι)
    (hlocal : ∀ k ∈ K, ∀ x ∈ S k, ∀ y ∈ S k, Route R (C k) x y)
    (i j : K)
    (hcut : RegionCutCondition (fun k : K => S k) i j)
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    Route R (∑ k : K, C k) u v := by
  exact route_of_region_cut_condition R (fun k : K => S k) (fun k : K => C k)
    (fun k => hlocal k k.property) i j hcut u v hu hv

/-- Failure of certificate connectivity has a concrete separating cut.
It does not imply that the full parent relation has no route. -/
theorem route_or_separating_region_cut {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ k, ∀ x ∈ S k, ∀ y ∈ S k, Route R (C k) x y)
    (i j : ι) (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    Route R (∑ k, C k) u v ∨
      ∃ A : Set ι, i ∈ A ∧ j ∉ A ∧
        ∀ a ∈ A, ∀ b, b ∉ A → ∀ z, z ∈ S a → z ∉ S b := by
  classical
  by_cases hreach : Nonempty ((intersectionGraph S).Walk i j)
  · exact Or.inl (route_of_connected_regions R S C hlocal hreach u v hu hv)
  · right
    let A : Set ι := {k | Nonempty ((intersectionGraph S).Walk i k)}
    refine ⟨A, ⟨.nil⟩, hreach, ?_⟩
    intro a ha b hb z hza hzb
    obtain ⟨p⟩ := ha
    obtain ⟨q⟩ := shared_point_walk S hza hzb
    exact hb ⟨p.append q⟩

/-- In a polyhedral application, cuts must be bridged by actual parent
vertices lying in both faces, not merely by overlapping time intervals. -/
theorem route_of_extreme_face_cut_condition {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ k, IsExtreme ℝ P (F k)) (hD : ∀ k, DiamLE (F k) (B k))
    (i j : ι)
    (hcut : RegionCutCondition (fun k => extremePoints ℝ P ∩ F k) i j)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ P ∩ F i)
    (hv : v ∈ extremePoints ℝ P ∩ F j) :
    Route (Adj P) (∑ k, B k) u v := by
  exact route_of_region_cut_condition (Adj P) (fun k => extremePoints ℝ P ∩ F k) B
    (fun k => extreme_face_region P (F k) (B k) (hF k) (hD k)) i j hcut u v hu hv

/-- A one-sided integer potential supplies an independently checkable route
lower bound, including equality padding steps. -/
theorem potential_le_of_route {V : Type*} (R : V → V → Prop) (φ : V → ℕ)
    (hφ : ∀ x y, R x y → φ y ≤ φ x + 1)
    {B : ℕ} {u v : V} (hroute : Route R B u v) : φ v ≤ φ u + B := by
  obtain ⟨w, hw0, hwB, hs⟩ := hroute
  have hp : ∀ k, k ≤ B → φ (w k) ≤ φ u + k := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [hw0]
    | succ k ih =>
        intro hk
        have hi := ih (by omega)
        rcases hs k (by omega) with heq | hadj
        · rw [← heq]
          omega
        · have hstep := hφ (w k) (w (k + 1)) hadj
          omega
  simpa [hwB] using hp B (Nat.le_refl B)

#print axioms region_cut_condition_of_walk
#print axioms region_walk_iff_cut_condition
#print axioms route_of_region_cut_condition
#print axioms route_of_subfamily_cut_condition
#print axioms route_or_separating_region_cut
#print axioms route_of_extreme_face_cut_condition
#print axioms potential_le_of_route

end HirschRegionRoute
