import Solutions.PolynomialPortalCut

open Set

noncomputable section

namespace HirschPortalCounterexample

open HirschRegionRoute

/-- Six-cycle adjacency, expressed without arithmetic wraparound in the proof obligations. -/
def CycleAdj (x y : Fin 6) : Prop :=
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
  (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
  (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) ∨
  (x = 3 ∧ y = 4) ∨ (x = 4 ∧ y = 3) ∨
  (x = 4 ∧ y = 5) ∨ (x = 5 ∧ y = 4) ∨
  (x = 5 ∧ y = 0) ∨ (x = 0 ∧ y = 5)

/-- The deliberately broken old sequence. -/
def oldSeq : Fin 4 → Fin 6
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | 3 => 3

/-- Two crossing damage regions, each an actual edge of the ambient cycle. -/
def regions : Fin 2 → Set (Fin 6)
  | 0 => {0, 1}
  | 1 => {2, 3}

lemma region_local_routes :
    ∀ i, ∀ x ∈ regions i, ∀ y ∈ regions i, Route CycleAdj 1 x y := by
  intro i x hx y hy
  fin_cases i
  · have hx' : x = 0 ∨ x = 1 := by simpa [regions] using hx
    have hy' : y = 0 ∨ y = 1 := by simpa [regions] using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact ⟨fun _ => 0, rfl, rfl, by intro k hk; omega⟩
    · exact ⟨fun k => if k = 0 then 0 else 1, rfl, rfl, by
        intro k hk; interval_cases k <;> simp [CycleAdj]⟩
    · exact ⟨fun k => if k = 0 then 1 else 0, rfl, rfl, by
        intro k hk; interval_cases k <;> simp [CycleAdj]⟩
    · exact ⟨fun _ => 1, rfl, rfl, by intro k hk; omega⟩
  · have hx' : x = 2 ∨ x = 3 := by simpa [regions] using hx
    have hy' : y = 2 ∨ y = 3 := by simpa [regions] using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact ⟨fun _ => 2, rfl, rfl, by intro k hk; omega⟩
    · exact ⟨fun k => if k = 0 then 2 else 3, rfl, rfl, by
        intro k hk; interval_cases k <;> simp [CycleAdj]⟩
    · exact ⟨fun k => if k = 0 then 3 else 2, rfl, rfl, by
        intro k hk; interval_cases k <;> simp [CycleAdj]⟩
    · exact ⟨fun _ => 3, rfl, rfl, by intro k hk; omega⟩

/-- Each chronological damage interval has endpoints certified by one region. -/
lemma damage_endpoints_certified :
    oldSeq 0 ∈ regions 0 ∧ oldSeq 2 ∈ regions 0 ∧
    oldSeq 1 ∈ regions 1 ∧ oldSeq 3 ∈ regions 1 := by
  simp [oldSeq, regions]

lemma damage_intervals_cross : 0 < 1 ∧ 1 < 2 ∧ 2 < 3 := by omega

lemma damage_intervals_cover_all_steps :
    ∀ j < 3, (0 ≤ j ∧ j < 2) ∨ (1 ≤ j ∧ j < 3) := by
  intro j hj
  omega

lemma endpoint_regions_disjoint : Disjoint (regions 0) (regions 1) := by
  simp [regions, Set.disjoint_left]

/-- The ambient endpoints cannot be joined in two steps. -/
theorem no_two_step_ambient_route : ¬ Route CycleAdj 2 (0 : Fin 6) 3 := by
  intro h
  rcases h with ⟨q, h0, h2, hs⟩
  have hstep0 := hs 0 (by decide)
  have hstep1 := hs 1 (by decide)
  rw [h0] at hstep0
  rw [h2] at hstep1
  fin_cases hq : q 1 <;> simp [hq, CycleAdj] at hstep0 hstep1

/-- The ambient cycle does have a three-step route. -/
theorem three_step_ambient_route : Route CycleAdj 3 (0 : Fin 6) 3 := by
  refine ⟨fun k => if k = 0 then 0 else if k = 1 then 1 else
    if k = 2 then 2 else 3, rfl, rfl, ?_⟩
  intro k hk
  interval_cases k <;> simp [CycleAdj]

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
  have h3 : (3 : Fin 6) ∉ cutSide := by
    change ¬ (3 : ℕ) < 2
    decide
  exact h3 h

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
