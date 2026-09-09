import Solutions.PolynomialPortalCut

open Set HirschRegionRoute

namespace HirschPortalCounterexample

/-- The graph of a convex hexagon, labelled cyclically. The finite graph
proof below does not claim a Lean identification with an H-polytope hull. -/
def hexAdj (i j : Fin 6) : Prop :=
  (i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val

instance : DecidableRel hexAdj := fun i j =>
  inferInstanceAs (Decidable ((i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val))

/-- Two disjoint actual edges of the ambient six-cycle. -/
def regions (i : Fin 2) : Set (Fin 6) :=
  if i = 0 then {0, 1} else {2, 3}

/-- Endpoint-only damage records cross: first region at positions 0,2;
second region at positions 1,3. Interior positions need not belong to a region. -/
def oldSequence (k : ℕ) : Fin 6 :=
  if k = 0 then 0 else if k = 1 then 2 else if k = 2 then 1 else 3

lemma region_local_routes : ∀ i, ∀ x ∈ regions i, ∀ y ∈ regions i,
    Route hexAdj 1 x y := by
  intro i
  fin_cases i
  · change ∀ x ∈ ({0, 1} : Set (Fin 6)), ∀ y ∈ ({0, 1} : Set (Fin 6)),
      Route hexAdj 1 x y
    exact pair_region hexAdj 0 1 (by decide) (by decide)
  · change ∀ x ∈ ({2, 3} : Set (Fin 6)), ∀ y ∈ ({2, 3} : Set (Fin 6)),
      Route hexAdj 1 x y
    exact pair_region hexAdj 2 3 (by decide) (by decide)

lemma damage_endpoints_certified :
    oldSequence 0 ∈ regions 0 ∧ oldSequence 2 ∈ regions 0 ∧
    oldSequence 1 ∈ regions 1 ∧ oldSequence 3 ∈ regions 1 := by
  simp [oldSequence, regions]

lemma damage_intervals_cross : (0 : ℕ) < 1 ∧ (1 : ℕ) < 2 ∧ (2 : ℕ) < 3 := by
  decide

lemma damage_intervals_cover_all_steps : ∀ j : Fin 3,
    (0 ≤ j.val ∧ j.val < 2) ∨ (1 ≤ j.val ∧ j.val < 3) := by
  decide

lemma endpoint_regions_disjoint : Disjoint (regions 0) (regions 1) := by
  simp [regions, Set.disjoint_left]

/-- Even using every edge of the ambient hexagon, the claimed two-charge
budget is insufficient. This checks all possible middle vertices in Lean. -/
theorem no_two_step_ambient_route : ¬ Route hexAdj 2 (0 : Fin 6) 3 := by
  rintro ⟨w, hw0, hw2, hs⟩
  have hleft : (0 : Fin 6) = w 1 ∨ hexAdj 0 (w 1) := by
    simpa only [hw0] using hs 0 (by decide)
  have hright : w 1 = (3 : Fin 6) ∨ hexAdj (w 1) 3 := by
    simpa only [hw2] using hs 1 (by decide)
  have hnone : ∀ x : Fin 6,
      ¬ (((0 : Fin 6) = x ∨ hexAdj 0 x) ∧ (x = 3 ∨ hexAdj x 3)) := by
    decide
  exact hnone (w 1) ⟨hleft, hright⟩

theorem three_step_ambient_route : Route hexAdj 3 (0 : Fin 6) 3 := by
  refine ⟨fun k => if k = 0 then 0 else if k = 1 then 1 else
    if k = 2 then 2 else 3, rfl, rfl, ?_⟩
  intro k hk
  interval_cases k <;> decide

/-- A cut proving that the supplied two-region repair network is disconnected,
although its ambient six-cycle is connected. -/
def cutSide : Set (Fin 6) := {x | x.val < 2}

lemma regions_preserve_cut : RegionClosed regions cutSide := by
  intro i x hx y hy hxu
  fin_cases i
  · have hy' : y = 0 ∨ y = 1 := by simpa [regions] using hy
    rcases hy' with rfl | rfl <;> norm_num [cutSide]
  · have hx' : x = 2 ∨ x = 3 := by simpa [regions] using hx
    rcases hx' with rfl | rfl <;> norm_num [cutSide] at hxu

/-- No amount of repeated use of these two regions bridges the missing portal. -/
theorem no_region_only_route (B : ℕ) :
    ¬ Route (RegionJump regions) B (0 : Fin 6) 3 := by
  intro hr
  have h := region_route_preserves_closed_cut regions cutSide
    regions_preserve_cut hr (by change (0 : ℕ) < 2; decide)
  exact (by change ¬ (3 : ℕ) < 2; decide) h

/-- The outside-step condition is vacuous for the crossing intervals [0,2),
[1,3); it supplies none of the missing transitions. -/
lemma no_uncovered_step : ¬ ∃ j : ℕ, j < 3 ∧
    (j < 0 ∨ 2 ≤ j) ∧ (j < 1 ∨ 3 ≤ j) := by
  omega

#print axioms region_local_routes
#print axioms damage_endpoints_certified
#print axioms damage_intervals_cross
#print axioms damage_intervals_cover_all_steps
#print axioms endpoint_regions_disjoint
#print axioms no_two_step_ambient_route
#print axioms three_step_ambient_route
#print axioms regions_preserve_cut
#print axioms no_region_only_route
#print axioms no_uncovered_step

end HirschPortalCounterexample
