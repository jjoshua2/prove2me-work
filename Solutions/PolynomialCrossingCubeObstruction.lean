import Solutions.PolynomialRepairNetworkCuts

open scoped BigOperators
open Set

noncomputable section

namespace HirschRegionRoute

/-- The Boolean cube graph, represented by the set of coordinates equal to
one. An edge inserts or deletes exactly one coordinate. -/
def CubeAdj {d : ℕ} (x y : Finset (Fin d)) : Prop :=
  ∃ k, (k ∉ x ∧ y = insert k x) ∨ (k ∉ y ∧ x = insert k y)

lemma cubeAdj_symm {d : ℕ} {x y : Finset (Fin d)}
    (h : CubeAdj x y) : CubeAdj y x := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, h.elim Or.inr Or.inl⟩

lemma cubeAdj_card_step {d : ℕ} (x y : Finset (Fin d))
    (h : CubeAdj x y) : y.card ≤ x.card + 1 := by
  obtain ⟨k, h | h⟩ := h
  · obtain ⟨hk, rfl⟩ := h
    exact (Finset.card_insert_of_notMem hk).le
  · obtain ⟨hk, rfl⟩ := h
    rw [Finset.card_insert_of_notMem hk]
    omega

/-- Every padded cube route from all-zero to all-one has length at least d. -/
theorem cube_route_dimension_lower_bound {d B : ℕ}
    (h : Route (@CubeAdj d) B ∅ Finset.univ) : d ≤ B := by
  have hb := potential_le_of_route (@CubeAdj d) Finset.card cubeAdj_card_step h
  simpa using hb

/-- Two opposite parallel edges of the Boolean cube. -/
def cubeRepairRegion {d : ℕ} (k : Fin d) (b : Bool) : Set (Finset (Fin d)) :=
  if b then {Finset.univ.erase k, Finset.univ} else {∅, {k}}

lemma cube_low_edge {d : ℕ} (k : Fin d) : CubeAdj ∅ ({k} : Finset (Fin d)) := by
  exact ⟨k, Or.inl ⟨by simp, by simp⟩⟩

lemma cube_high_edge {d : ℕ} (k : Fin d) :
    CubeAdj (Finset.univ.erase k) (Finset.univ : Finset (Fin d)) := by
  exact ⟨k, Or.inl ⟨by simp, by simp⟩⟩

lemma cube_repair_regions_cost_one {d : ℕ} (k : Fin d) :
    ∀ b, ∀ x ∈ cubeRepairRegion k b, ∀ y ∈ cubeRepairRegion k b,
      Route (@CubeAdj d) 1 x y := by
  intro b
  cases b with
  | false =>
      exact pair_region (@CubeAdj d) ∅ {k} (cube_low_edge k)
        (cubeAdj_symm (cube_low_edge k))
  | true =>
      exact pair_region (@CubeAdj d) (Finset.univ.erase k) Finset.univ
        (cube_high_edge k) (cubeAdj_symm (cube_high_edge k))

/-- Chronological order is deliberately interleaved: low, high, low, high. -/
def cubeCrossingSequence {d : ℕ} (k : Fin d) (j : ℕ) : Finset (Fin d) :=
  if j = 0 then ∅ else if j = 1 then Finset.univ.erase k
  else if j = 2 then {k} else Finset.univ

/-- The half-open intervals [0,2) and [1,3) cover every old step index. -/
lemma crossing_intervals_cover (j : ℕ) (hj : j < 3) :
    (0 ≤ j ∧ j < 2) ∨ (1 ≤ j ∧ j < 3) := by omega

/-- Endpoint-only crossing interval certificates cannot imply the loose
L + sum B_i repair bound: L=3 and two cost-one blocks give budget five,
while the opposite cube vertices require at least d steps. This is a
Boolean-cube graph theorem; the Euclidean H-polytope identification is not
part of this Lean declaration. -/
theorem crossing_cube_endpoint_certificate_insufficient
    (d : ℕ) (hd : 6 ≤ d) :
    ∃ (w : ℕ → Finset (Fin d)) (S : Bool → Set (Finset (Fin d))),
      (∀ b, ∀ x ∈ S b, ∀ y ∈ S b, Route (@CubeAdj d) 1 x y) ∧
      w 0 ∈ S false ∧ w 2 ∈ S false ∧
      w 1 ∈ S true ∧ w 3 ∈ S true ∧
      (∀ j < 3, (0 ≤ j ∧ j < 2) ∨ (1 ≤ j ∧ j < 3)) ∧
      ¬ Route (@CubeAdj d) (3 + 2 * 1) (w 0) (w 3) := by
  let k : Fin d := ⟨0, by omega⟩
  refine ⟨cubeCrossingSequence k, cubeRepairRegion k,
    cube_repair_regions_cost_one k, ?_, ?_, ?_, ?_, crossing_intervals_cover, ?_⟩
  · simp [cubeCrossingSequence, cubeRepairRegion]
  · simp [cubeCrossingSequence, cubeRepairRegion]
  · simp [cubeCrossingSequence, cubeRepairRegion]
  · simp [cubeCrossingSequence, cubeRepairRegion]
  · intro h
    have hroute : Route (@CubeAdj d) 5 ∅ Finset.univ := by
      simpa [cubeCrossingSequence] using h
    have hbound := cube_route_dimension_lower_bound hroute
    omega

/-- Their time intervals overlap, but the two certified regions do not. -/
lemma cube_repair_regions_disjoint {d : ℕ} (hd : 3 ≤ d) (k : Fin d) :
    Disjoint (cubeRepairRegion k false) (cubeRepairRegion k true) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hx' : x = ∅ ∨ x = {k} := by simpa [cubeRepairRegion] using hx
  have hy' : x = Finset.univ.erase k ∨ x = Finset.univ := by
    simpa [cubeRepairRegion] using hy
  have hlo : x.card ≤ 1 := by
    rcases hx' with rfl | rfl <;> simp
  have hhi : d - 1 ≤ x.card := by
    rcases hy' with rfl | rfl
    · simp
    · simp
  omega

/-- The failed repair has an explicit cut certificate in the region graph. -/
theorem cube_crossing_has_separating_cut {d : ℕ} (hd : 3 ≤ d) (k : Fin d) :
    ¬ RegionCutCondition (cubeRepairRegion k) false true := by
  intro hcut
  obtain ⟨a, ha, b, hb, z, hza, hzb⟩ :=
    hcut ({false} : Set Bool) (by simp) (by simp)
  have ha' : a = false := by simpa using ha
  have hb' : b = true := by cases b <;> simp_all
  subst a
  subst b
  exact Set.disjoint_left.mp (cube_repair_regions_disjoint hd k) hza hzb

#print axioms cubeAdj_symm
#print axioms cubeAdj_card_step
#print axioms cube_route_dimension_lower_bound
#print axioms cube_low_edge
#print axioms cube_high_edge
#print axioms cube_repair_regions_cost_one
#print axioms crossing_intervals_cover
#print axioms crossing_cube_endpoint_certificate_insufficient
#print axioms cube_repair_regions_disjoint
#print axioms cube_crossing_has_separating_cut

end HirschRegionRoute
