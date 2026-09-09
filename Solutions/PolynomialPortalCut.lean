import Solutions.PolynomialMixedRegionRouting

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

namespace HirschRegionRoute

/-- A certified transition through one supplied region. This is not the
ambient edge relation: unlisted ambient edges are deliberately absent. -/
def RegionJump {V ι : Type*} (S : ι → Set V) (x y : V) : Prop :=
  ∃ i, x ∈ S i ∧ y ∈ S i

/-- Membership in a closed side of a cut is preserved by every supplied region. -/
def RegionClosed {V ι : Type*} (S : ι → Set V) (U : Set V) : Prop :=
  ∀ i, ∀ x ∈ S i, ∀ y ∈ S i, x ∈ U → y ∈ U

/-- A closed cut obstructs all routes in the supplied repair network, not
necessarily routes using additional edges of the ambient graph. -/
theorem region_route_preserves_closed_cut {V ι : Type*}
    (S : ι → Set V) (U : Set V) (hclosed : RegionClosed S U)
    {B : ℕ} {u v : V} (hroute : Route (RegionJump S) B u v)
    (hu : u ∈ U) : v ∈ U := by
  obtain ⟨w, hw0, hwB, hs⟩ := hroute
  have hmem : ∀ k, k ≤ B → w k ∈ U := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [hw0] using hu
    | succ k ih =>
        intro hkB
        have hk : w k ∈ U := ih (by omega)
        rcases hs k (by omega) with heq | hjump
        · rw [← heq]
          exact hk
        · obtain ⟨i, hki, hnext⟩ := hjump
          exact hclosed i (w k) hki (w (k + 1)) hnext hk
  simpa only [hwB] using hmem B (Nat.le_refl B)

/-- Either the finite family of internally routable regions gives a route
paying each available region at most once, or a vertex cut separates the
endpoints and no supplied region crosses it. No old sequence, interval
ordering, or chronological overlap hypothesis is needed.

The alternatives need not be exclusive for the ambient relation R: a cut
only certifies insufficiency of the supplied regions. -/
theorem route_or_region_closed_cut {V ι : Type*} [Fintype ι]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (u v : V) :
    Route R (∑ i, C i) u v ∨
      ∃ U : Set V, u ∈ U ∧ v ∉ U ∧ RegionClosed S U := by
  classical
  -- Zero-cost singleton terminals remove any endpoint-coverage assumptions.
  let T : Sum ι Bool → Set V :=
    Sum.elim S (fun c => {if c then v else u})
  let D : Sum ι Bool → ℕ := Sum.elim C (fun _ => 0)
  have hlocalT : ∀ i, ∀ x ∈ T i, ∀ y ∈ T i, Route R (D i) x y := by
    intro i
    cases i with
    | inl i => exact hlocal i
    | inr c =>
        intro x hx y hy
        change x ∈ ({if c then v else u} : Set V) at hx
        change y ∈ ({if c then v else u} : Set V) at hy
        change Route R 0 x y
        have hxy : x = y :=
          (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
        exact ⟨fun _ => x, rfl, hxy, fun k hk => by omega⟩
  have huT : u ∈ T (Sum.inr false) := by simp [T]
  have hvT : v ∈ T (Sum.inr true) := by simp [T]
  by_cases hreach : Nonempty
      ((intersectionGraph T).Walk (Sum.inr false) (Sum.inr true))
  · left
    have hr := route_of_connected_regions R T D hlocalT hreach u v huT hvT
    simpa [D, Fintype.sum_sum_type] using hr
  · right
    let U : Set V := {x | ∃ i : Sum ι Bool,
      Nonempty ((intersectionGraph T).Walk (Sum.inr false) i) ∧ x ∈ T i}
    refine ⟨U, ?_, ?_, ?_⟩
    · exact ⟨Sum.inr false, ⟨.nil⟩, huT⟩
    · intro hvU
      obtain ⟨i, hi, hvi⟩ := hvU
      obtain ⟨p⟩ := hi
      obtain ⟨q⟩ := shared_point_walk T hvi hvT
      exact hreach ⟨p.append q⟩
    · intro i x hx y hy hxU
      obtain ⟨j, hj, hxj⟩ := hxU
      obtain ⟨p⟩ := hj
      have hxi : x ∈ T (Sum.inl i) := hx
      obtain ⟨q⟩ := shared_point_walk T hxj hxi
      exact ⟨Sum.inl i, ⟨p.append q⟩, hy⟩

/-- Exact qualitative criterion for connectivity of the supplied region
network. The reverse implication also constructs a route with budget at
most the number of available regions. -/
theorem region_connectivity_iff_no_closed_cut {V ι : Type*} [Fintype ι]
    (S : ι → Set V) (u v : V) :
    (∃ B, Route (RegionJump S) B u v) ↔
      ∀ U : Set V, RegionClosed S U → u ∈ U → v ∈ U := by
  constructor
  · rintro ⟨B, hr⟩ U hc hu
    exact region_route_preserves_closed_cut S U hc hr hu
  · intro hcut
    have hlocal : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i,
        Route (RegionJump S) 1 x y := by
      intro i x hx y hy
      exact route_one (RegionJump S) (Or.inr ⟨i, hx, hy⟩)
    rcases route_or_region_closed_cut (RegionJump S) S (fun _ => 1)
        hlocal u v with hr | ⟨U, hu, hv, hc⟩
    · exact ⟨_, hr⟩
    · exact False.elim (hv (hcut U hc hu))

/-- Mixed repair certificate: a region costs C_i and a listed bidirectional
surviving edge costs one. A failure cut contains each region entirely on one
side and places both endpoints of every listed bridge on the same side. -/
theorem route_or_mixed_closed_cut {V ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (a b : κ → V) (hab : ∀ e, R (a e) (b e)) (hba : ∀ e, R (b e) (a e))
    (u v : V) :
    Route R ((∑ i, C i) + Fintype.card κ) u v ∨
      ∃ U : Set V, u ∈ U ∧ v ∉ U ∧ RegionClosed S U ∧
        ∀ e, (a e ∈ U ↔ b e ∈ U) := by
  let T : Sum ι κ → Set V := Sum.elim S (fun e => {a e, b e})
  let D : Sum ι κ → ℕ := Sum.elim C (fun _ => 1)
  have hlocalT : ∀ i, ∀ x ∈ T i, ∀ y ∈ T i, Route R (D i) x y := by
    intro i
    cases i with
    | inl i => exact hlocal i
    | inr e => exact pair_region R (a e) (b e) (hab e) (hba e)
  rcases route_or_region_closed_cut R T D hlocalT u v with hr | ⟨U, hu, hv, hc⟩
  · left
    simpa [D, Fintype.sum_sum_type] using hr
  · right
    refine ⟨U, hu, hv, ?_, ?_⟩
    · intro i x hx y hy hxu
      exact hc (Sum.inl i) x hx y hy hxu
    · intro e
      have ha : a e ∈ T (Sum.inr e) := by simp [T]
      have hb : b e ∈ T (Sum.inr e) := by simp [T]
      exact ⟨hc (Sum.inr e) (a e) ha (b e) hb,
        hc (Sum.inr e) (b e) hb (a e) ha⟩

/-- A cut-crossing criterion gives the quantitative mixed-region route
without requiring a pre-existing covered sequence. -/
theorem route_of_mixed_cut_crossing {V ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ u ∈ S i, ∀ v ∈ S i, Route R (C i) u v)
    (a b : κ → V) (hab : ∀ e, R (a e) (b e)) (hba : ∀ e, R (b e) (a e))
    (u v : V)
    (hcut : ∀ U : Set V, u ∈ U → v ∉ U →
      (∃ i, ∃ x ∈ S i, ∃ y ∈ S i, x ∈ U ∧ y ∉ U) ∨
      (∃ e, (a e ∈ U ∧ b e ∉ U) ∨ (b e ∈ U ∧ a e ∉ U))) :
    Route R ((∑ i, C i) + Fintype.card κ) u v := by
  rcases route_or_mixed_closed_cut R S C hlocal a b hab hba u v with
    hr | ⟨U, hu, hv, hc, he⟩
  · exact hr
  · rcases hcut U hu hv with ⟨i, x, hxi, y, hyi, hx, hy⟩ | ⟨e, habU | hbaU⟩
    · exact False.elim (hy (hc i x hxi y hyi hx))
    · exact False.elim (habU.2 ((he e).mp habU.1))
    · exact False.elim (hbaU.2 ((he e).mpr hbaU.1))

#print axioms region_route_preserves_closed_cut
#print axioms route_or_region_closed_cut
#print axioms region_connectivity_iff_no_closed_cut
#print axioms route_or_mixed_closed_cut
#print axioms route_of_mixed_cut_crossing

end HirschRegionRoute
