import Solutions.PolynomialMixedRegionRouting

open Set

namespace HirschCrossingObstruction

open HirschRegionRoute

/-- The undirected sixteen-cycle, written without a graph-library convention. -/
def cycleStep (a b : Fin 16) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val ∨
    (a.val = 0 ∧ b.val = 15) ∨ (a.val = 15 ∧ b.val = 0)

/-- Distance-to-zero potential. Each edge can increase it by at most one. -/
def cyclePotential (a : Fin 16) : ℕ := min a.val (16 - a.val)

lemma cycle_potential_step {a b : Fin 16} (h : a = b ∨ cycleStep a b) :
    cyclePotential b ≤ cyclePotential a + 1 := by
  have ha := a.isLt
  have hb := b.isLt
  rcases h with hab | h
  · subst b
    omega
  · simp only [cycleStep] at h
    rcases h with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      dsimp [cyclePotential] <;> omega

/-- The potential lower-bounds every padded route, not just simple paths. -/
lemma cycle_route_potential_bound {B : ℕ} {u v : Fin 16}
    (h : Route cycleStep B u v) : cyclePotential v ≤ cyclePotential u + B := by
  obtain ⟨w, hw0, hwB, hs⟩ := h
  have hpot : ∀ j, j ≤ B → cyclePotential (w j) ≤ cyclePotential u + j := by
    intro j
    induction j with
    | zero =>
        intro _
        simp [hw0]
    | succ j ih =>
        intro hj
        have hprev := ih (by omega)
        have hstep := cycle_potential_step (hs j (by omega))
        omega
  simpa only [hwB] using hpot B (Nat.le_refl B)

def crossingSequence : ℕ → Fin 16
  | 0 => 0
  | 1 => 8
  | 2 => 1
  | _ => 9

def crossingStart (i : Fin 2) : ℕ := i.val

def crossingEnd (i : Fin 2) : ℕ := i.val + 2

def crossingRegion (i : Fin 2) : Set (Fin 16) :=
  if i = 0 then {0, 1} else {8, 9}

lemma crossing_covers_all_steps :
    ∀ k < 3, ∃ i : Fin 2, crossingStart i ≤ k ∧ k + 1 ≤ crossingEnd i := by
  intro k hk
  interval_cases k
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩

lemma crossing_endpoints_in_regions :
    ∀ i, crossingSequence (crossingStart i) ∈ crossingRegion i ∧
      crossingSequence (crossingEnd i) ∈ crossingRegion i := by
  intro i
  fin_cases i <;> norm_num [crossingSequence, crossingStart, crossingEnd, crossingRegion]

lemma crossing_local_cost_one :
    ∀ i, ∀ u ∈ crossingRegion i, ∀ v ∈ crossingRegion i, Route cycleStep 1 u v := by
  intro i
  fin_cases i
  · simpa [crossingRegion] using
      pair_region cycleStep (0 : Fin 16) 1
        (by norm_num [cycleStep]) (by norm_num [cycleStep])
  · simpa [crossingRegion] using
      pair_region cycleStep (8 : Fin 16) 9
        (by norm_num [cycleStep]) (by norm_num [cycleStep])

lemma crossing_regions_disjoint : Disjoint (crossingRegion 0) (crossingRegion 1) := by
  rw [Set.disjoint_left]
  intro x hx hy
  simp [crossingRegion] at hx hy
  rcases hx with rfl | rfl <;> norm_num at hy

lemma crossing_no_route_below_seven {B : ℕ} (hB : B < 7) :
    ¬ Route cycleStep B (crossingSequence 0) (crossingSequence 3) := by
  intro h
  have hbound := cycle_route_potential_bound h
  norm_num [crossingSequence, cyclePotential] at hbound
  omega

def shortestSequence : ℕ → Fin 16
  | 0 => 0
  | 1 => 15
  | 2 => 14
  | 3 => 13
  | 4 => 12
  | 5 => 11
  | 6 => 10
  | _ => 9

lemma crossing_route_seven :
    Route cycleStep 7 (crossingSequence 0) (crossingSequence 3) := by
  refine ⟨shortestSequence, rfl, rfl, ?_⟩
  intro j hj
  interval_cases j <;> norm_num [shortestSequence, cycleStep]

/-- Two crossing endpoint-supported intervals cover all three old steps, and
each region has cost one, but the endpoints cannot be joined even in the loose
budget 3+1+1=5. Thus time-interval coverage alone is not a repair certificate.
This is a finite graph theorem; the accompanying exact integer-hull regression
realizes this graph and these regions as a convex polygon and two of its edges. -/
theorem crossing_interval_cover_counterexample :
    (∀ k < 3, ∃ i : Fin 2, crossingStart i ≤ k ∧ k + 1 ≤ crossingEnd i) ∧
    (∀ i, crossingSequence (crossingStart i) ∈ crossingRegion i ∧
      crossingSequence (crossingEnd i) ∈ crossingRegion i) ∧
    (∀ i, ∀ u ∈ crossingRegion i, ∀ v ∈ crossingRegion i, Route cycleStep 1 u v) ∧
    Disjoint (crossingRegion 0) (crossingRegion 1) ∧
    ¬ Route cycleStep 5 (crossingSequence 0) (crossingSequence 3) :=
  ⟨crossing_covers_all_steps, crossing_endpoints_in_regions,
    crossing_local_cost_one, crossing_regions_disjoint,
    crossing_no_route_below_seven (by decide)⟩

#print axioms cycle_potential_step
#print axioms cycle_route_potential_bound
#print axioms crossing_covers_all_steps
#print axioms crossing_endpoints_in_regions
#print axioms crossing_local_cost_one
#print axioms crossing_regions_disjoint
#print axioms crossing_no_route_below_seven
#print axioms crossing_route_seven
#print axioms crossing_interval_cover_counterexample

end HirschCrossingObstruction
