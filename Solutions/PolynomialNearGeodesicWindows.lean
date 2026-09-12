import Solutions.PolynomialGeodesicRowIncidence

/-!
# Controlled detours preserve an all-row incidence budget

The path may revisit labels. If its length exceeds endpoint distance by at
most k, any graph vertex contacts at most k+3 POSITIONS. Counting positions,
not distinct labels, is essential for the later portal optimizer.

New source candidate: separate pinned Lean/axiom verification required.
-/
open scoped BigOperators
open Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace HirschRegionRoute

/-- A shortcut can save at most the admitted additive slack. -/
theorem near_geodesic_index_gap_le_walk
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (k : ℕ) (hp : p.length ≤ G.dist u v + k)
    (r s : ℕ) (hrs : r ≤ s) (hs : s ≤ p.length)
    (q : G.Walk (p.getVert r) (p.getVert s)) :
    s ≤ r + q.length + k := by
  have hr : r ≤ p.length := hrs.trans hs
  let shortcut : G.Walk u v := ((p.take r).append q).append (p.drop s)
  have hdist := SimpleGraph.dist_le shortcut
  have hlen : shortcut.length = r + q.length + (p.length-s) := by
    simp [shortcut, hr]
  rw [hlen] at hdist
  omega

/-- This concerns positions, including multiple visits to the same label. -/
theorem near_geodesic_closedNear_span
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (k : ℕ) (hp : p.length ≤ G.dist u v + k)
    (z : V) (r s : ℕ) (hrs : r ≤ s) (hs : s ≤ p.length)
    (hzr : ClosedNear G z (p.getVert r))
    (hzs : ClosedNear G z (p.getVert s)) : s ≤ r + k + 2 := by
  obtain ⟨q₁, h₁⟩ := closedNear_short_walk hzr.symm
  obtain ⟨q₂, h₂⟩ := closedNear_short_walk hzs
  have h := near_geodesic_index_gap_le_walk p k hp r s hrs hs (q₁.append q₂)
  simp only [SimpleGraph.Walk.length_append] at h
  omega

def contactPositions {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (z : V) : Finset ℕ := by
  classical
  exact (Finset.range (p.length+1)).filter (fun j => ClosedNear G z (p.getVert j))

/-- At most k+3 contacts even without a simple-path or chordless premise. -/
theorem contactPositions_card_le
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (k : ℕ) (hp : p.length ≤ G.dist u v + k) (z : V) :
    (contactPositions p z).card ≤ k+3 := by
  classical
  by_cases hn : (contactPositions p z).Nonempty
  · obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image (contactPositions p z) id hn
    have hzr : ClosedNear G z (p.getVert r) := (Finset.mem_filter.mp hr).2
    have hsub : contactPositions p z ⊆ Finset.Icc r (r+k+2) := by
      intro s hs
      have hrs : r ≤ s := hmin s hs
      have hsrange : s < p.length+1 :=
        Finset.mem_range.mp (Finset.mem_filter.mp hs).1
      have hzs := (Finset.mem_filter.mp hs).2
      have hspan := near_geodesic_closedNear_span p k hp z r s hrs (by omega) hzr hzs
      exact Finset.mem_Icc.mpr ⟨hrs, hspan⟩
    have hc : (Finset.Icc r (r+k+2)).card = k+3 := by
      simp only [Nat.card_Icc]
      omega
    exact (Finset.card_le_card hsub).trans_eq hc
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

/-- Occurrence-indexed double counting. Repeated selected labels are NOT
silently deduplicated: each actual charged position remains in the sum. -/
theorem near_geodesic_total_position_load
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (k : ℕ) (hp : p.length ≤ G.dist u v + k)
    (available : Finset V) (positions : Finset ℕ)
    (hpos : positions ⊆ Finset.range (p.length+1)) :
    (∑ j ∈ positions, availableContactLoad G available (p.getVert j)) ≤
      (k+3) * available.card := by
  classical
  have hswap : (∑ j ∈ positions, availableContactLoad G available (p.getVert j)) =
      ∑ z ∈ available, (positions.filter (fun j => ClosedNear G z (p.getVert j))).card := by
    simp only [availableContactLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap]
  have hcol : ∀ z ∈ available,
      (positions.filter (fun j => ClosedNear G z (p.getVert j))).card ≤ k+3 := by
    intro z _
    have hsub : positions.filter (fun j => ClosedNear G z (p.getVert j)) ⊆
        contactPositions p z := by
      intro j hj
      exact Finset.mem_filter.mpr
        ⟨hpos (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
    exact (Finset.card_le_card hsub).trans (contactPositions_card_le p k hp z)
  simpa [Nat.mul_comm] using Finset.sum_le_sum hcol

#print axioms near_geodesic_index_gap_le_walk
#print axioms near_geodesic_closedNear_span
#print axioms contactPositions_card_le
#print axioms near_geodesic_total_position_load
end HirschRegionRoute
