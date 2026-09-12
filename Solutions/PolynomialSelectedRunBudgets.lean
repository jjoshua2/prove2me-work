import Solutions.PolynomialExactSelectedSupport
import Solutions.PolynomialSupportDeficitRouting

/-! Exact degree sums from starts of the selected runs on the fixed path. -/
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
attribute [local instance] Classical.propDecidable
namespace HirschRegionRoute

def earlierSelectedNeighborFinset
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) (i : V) : Finset V :=
  (selectedNeighborFinset p cuts i).filter
    (fun j => p.support.idxOf j < p.support.idxOf i)

/-- Starts of selected runs: selected labels with no earlier selected neighbor
in the fixed support order. For a chordless path these are exactly run starts. -/
def selectedRunStartFinset
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) : Finset V :=
  cuts.filter (fun i => (earlierSelectedNeighborFinset p cuts i).card = 0)

theorem selectedNeighborFinset_eq_filter
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) (hcuts : cuts ⊆ p.support.toFinset) (i : V) :
    selectedNeighborFinset p cuts i = cuts.filter (G.Adj i) := by
  ext j
  simp only [selectedNeighborFinset, supportNeighborFinset, Finset.mem_inter,
    Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hcuts h.1, h.2⟩⟩

theorem earlierSelectedNeighborFinset_card_le_one
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hchord : WalkChordless p)
    (cuts : Finset V) (hcuts : cuts ⊆ p.support.toFinset)
    (i : V) (hi : i ∈ cuts) :
    (earlierSelectedNeighborFinset p cuts i).card ≤ 1 := by
  have his : i ∈ p.support := List.mem_toFinset.mp (hcuts hi)
  have hstep : ∀ j ∈ earlierSelectedNeighborFinset p cuts i,
      p.support.idxOf j + 1 = p.support.idxOf i := by
    intro j hj
    obtain ⟨hjn, hlt⟩ := Finset.mem_filter.mp hj
    rw [selectedNeighborFinset_eq_filter p cuts hcuts i] at hjn
    obtain ⟨hjc, hadj⟩ := Finset.mem_filter.mp hjn
    have hjs : j ∈ p.support := List.mem_toFinset.mp (hcuts hjc)
    have hile : p.support.idxOf i ≤ p.length := by
      have h := List.idxOf_lt_length_of_mem his
      rw [p.length_support] at h
      omega
    by_contra hne
    have hno := hchord (p.support.idxOf j) (p.support.idxOf i) (by omega) hile
    apply hno
    simpa [p.getVert_support_idxOf his, p.getVert_support_idxOf hjs] using hadj.symm
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjstep := hstep j hj
  have hkstep := hstep k hk
  have hjc : j ∈ cuts := (Finset.mem_inter.mp (Finset.mem_filter.mp hj).1).1
  have hkc : k ∈ cuts := (Finset.mem_inter.mp (Finset.mem_filter.mp hk).1).1
  have hjs := p.getVert_support_idxOf (List.mem_toFinset.mp (hcuts hjc))
  have hks := p.getVert_support_idxOf (List.mem_toFinset.mp (hcuts hkc))
  have heq : p.support.idxOf j = p.support.idxOf k := by omega
  rw [← hjs, ← hks, heq]

/-- Nontruncated forest degree identity, with components represented by their
unique start in the fixed selected-run order. Empty selections are included. -/
theorem sum_selected_degrees_add_twice_runStarts
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hchord : WalkChordless p)
    (cuts : Finset V) (hcuts : cuts ⊆ p.support.toFinset) :
    (∑ i ∈ cuts, (selectedNeighborFinset p cuts i).card) +
      2 * (selectedRunStartFinset p cuts).card = 2 * cuts.card := by
  let later := fun i => cuts.filter
    (fun j => G.Adj j i ∧ p.support.idxOf i < p.support.idxOf j)
  have hback : ∀ i, earlierSelectedNeighborFinset p cuts i =
      cuts.filter (fun j => G.Adj i j ∧ p.support.idxOf j < p.support.idxOf i) := by
    intro i
    rw [earlierSelectedNeighborFinset, selectedNeighborFinset_eq_filter p cuts hcuts]
    ext j
    simp [and_assoc]
  have hsplit : ∀ i ∈ cuts, (selectedNeighborFinset p cuts i).card =
      (earlierSelectedNeighborFinset p cuts i).card + (later i).card := by
    intro i hi
    rw [selectedNeighborFinset_eq_filter p cuts hcuts, hback]
    simp only [later, Finset.card_eq_sum_ones, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases ha : G.Adj i j
    · have hne : p.support.idxOf i ≠ p.support.idxOf j := by
        intro heq
        apply ha.ne
        have hi' := p.getVert_support_idxOf (List.mem_toFinset.mp (hcuts hi))
        have hj' := p.getVert_support_idxOf (List.mem_toFinset.mp (hcuts hj))
        rw [← hi', ← hj', heq]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [ha, ha.symm, hlt, Nat.not_lt_of_ge hlt.le]
      · simp [ha, ha.symm, hgt, Nat.not_lt_of_ge hgt.le]
    · have hna : ¬ G.Adj j i := fun h => ha h.symm
      simp [ha, hna]
  have hswap : (∑ i ∈ cuts, (later i).card) =
      ∑ i ∈ cuts, (earlierSelectedNeighborFinset p cuts i).card := by
    simp only [hback, later, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have htotal : (∑ i ∈ cuts, (selectedNeighborFinset p cuts i).card) =
      2 * ∑ i ∈ cuts, (earlierSelectedNeighborFinset p cuts i).card := by
    calc
      _ = ∑ i ∈ cuts, ((earlierSelectedNeighborFinset p cuts i).card + (later i).card) :=
        Finset.sum_congr rfl hsplit
      _ = _ := by rw [Finset.sum_add_distrib, hswap, two_mul]
  have hstarts : (∑ i ∈ cuts, (earlierSelectedNeighborFinset p cuts i).card) +
      (selectedRunStartFinset p cuts).card = cuts.card := by
    have hpoint : ∀ i ∈ cuts,
        (earlierSelectedNeighborFinset p cuts i).card +
          (if (earlierSelectedNeighborFinset p cuts i).card = 0 then 1 else 0) = 1 := by
      intro i hi
      have hle := earlierSelectedNeighborFinset_card_le_one p hchord cuts hcuts i hi
      split_ifs <;> omega
    have hs := Finset.sum_congr rfl hpoint
    simpa [Finset.sum_add_distrib, selectedRunStartFinset] using hs
  omega

theorem sum_selected_budgets_with_run_correction
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hchord : WalkChordless p)
    (cuts : Finset V) (hcuts : cuts ⊆ p.support.toFinset)
    (excess : V → ℕ) (e : ℕ) (he : cuts.card ≤ e)
    (hbudget : ∀ i ∈ cuts, excess i + cuts.card ≤
      e + 1 + (selectedNeighborFinset p cuts i).card) :
    (∑ i ∈ cuts, excess i) + 2 * (selectedRunStartFinset p cuts).card ≤
      cuts.card * (e - cuts.card + 3) := by
  have hs := sum_exact_selected_budgets cuts excess
    (fun i => (selectedNeighborFinset p cuts i).card) e hbudget
  have hd := sum_selected_degrees_add_twice_runStarts p hchord cuts hcuts
  have heq : e = (e - cuts.card) + cuts.card := by omega
  nlinarith

#print axioms earlierSelectedNeighborFinset_card_le_one
#print axioms sum_selected_degrees_add_twice_runStarts
#print axioms sum_selected_budgets_with_run_correction
end HirschRegionRoute

open scoped RealInnerProductSpace
open Set Hirsch HirschRegionRoute HirschCircuitLocalization HirschPolynomialAccess
namespace HirschRadial
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Number of selected cut runs, represented by their starts on the same
chordless mixed path retained by the clipping certificate. -/
def DeferredClipCertificate.selectedCutRunCount
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {aj : ι → EuclideanSpace ℝ (Fin d)} {bj : ι → ℝ}
    {u v : EuclideanSpace ℝ (Fin d)} (c : DeferredClipCertificate P aj bj D u v) : ℕ :=
  (selectedRunStartFinset c.path
    (c.cutSupport.image (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2))))).card

/-- The run correction is a bound on the SUM OF ACTUAL carrier excesses of
the certificate, not just a bound for an arbitrary assignment on path labels. -/
theorem DeferredClipCertificate.sum_carrier_excess_with_run_correction
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (gap : ℕ) (hgap : c.cutSupport.card + gap = n-d) :
    ((clipRepairCutLegs c.legs).map fun leg =>
      commonFacePresentationExcess a b leg.entry leg.exit).sum +
      2*c.selectedCutRunCount ≤ c.cutSupport.card*(gap+3) := by
  classical
  let cuts := c.cutSupport.image (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2)))
  let labels := (clipRepairCutLegs c.legs).map
    (fun leg => (Sum.inl leg.label : Sum ι (Sum (Fin D) (Fin 2))))
  have hlabels : labels.toFinset = cuts := by
    ext k
    simp only [labels, cuts, DeferredClipCertificate.cutSupport, List.mem_toFinset,
      List.mem_map, Finset.mem_image]
    aesop
  have hnodup : labels.Nodup := by
    change ((clipRepairCutLegs c.legs).map
      ((Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2))) ∘ RegionLeg.label)).Nodup
    rw [← List.map_map]
    exact (clipRepairCutLeg_labels_nodup c.nodup).map Sum.inl_injective
  have hcsub : cuts ⊆ c.path.support.toFinset := by
    intro k hk
    rw [← hlabels] at hk
    obtain ⟨leg, hleg, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    have hm := (cut_leg_mem_iff c leg).mp hleg
    have hl : Sum.inl leg.label ∈ c.legs.map RegionLeg.label :=
      List.mem_map.mpr ⟨_, hm, rfl⟩
    rw [c.labels] at hl
    exact List.mem_toFinset.mpr hl
  have hcount : cuts.card = c.cutSupport.card :=
    Finset.card_image_of_injective _ Sum.inl_injective
  have hdegreeSum : (∑ k ∈ cuts, (selectedNeighborFinset c.path cuts k).card) =
      ((clipRepairCutLegs c.legs).map fun leg => c.selectedCutDegree leg.label).sum := by
    rw [← hlabels, List.sum_toFinset _ hnodup]
    rw [hlabels]
    simp only [labels, List.map_map]
    rfl
  have hdeg := sum_selected_degrees_add_twice_runStarts c.path c.chordless cuts hcsub
  rw [hcount, hdegreeSum] at hdeg
  have hsum : ∀ ls : List (RegionLeg ι (EuclideanSpace ℝ (Fin d))),
      (∀ leg ∈ ls, commonFacePresentationExcess a b leg.entry leg.exit +
        c.cutSupport.card ≤ (n-d)+1+c.selectedCutDegree leg.label) →
      (ls.map fun leg => commonFacePresentationExcess a b leg.entry leg.exit).sum +
        ls.length*c.cutSupport.card ≤ ls.length*((n-d)+1) +
          (ls.map fun leg => c.selectedCutDegree leg.label).sum := by
    intro ls
    induction ls with
    | nil => simp
    | cons leg rest ih =>
      intro h
      have hhead := h leg (by simp)
      have htail := ih (fun x hx => h x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have hs := hsum (clipRepairCutLegs c.legs)
    (fun leg hleg => c.used_carrier_exact_selected_budget a b row hinj hbd o hstrict leg hleg)
  rw [← c.cutSupport_card] at hs
  change ((clipRepairCutLegs c.legs).map fun leg => c.selectedCutDegree leg.label).sum +
    2*c.selectedCutRunCount = 2*c.cutSupport.card at hdeg
  nlinarith

/-- In the small-excess selected-degree regime, the corrected excess sum
also bounds the actual parent-edge routing cost. -/
theorem DeferredClipCertificate.route_with_run_corrected_cost
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (gap : ℕ) (hgap : c.cutSupport.card + gap = n-d)
    (hdegree : ∀ leg ∈ clipRepairCutLegs c.legs, gap+c.selectedCutDegree leg.label ≤ 2) :
    Route (Adj (Hpoly a b))
      (D + (c.cutSupport.card*(gap+3) - 2*c.selectedCutRunCount)) u v := by
  have hsum := c.sum_carrier_excess_with_run_correction a b row hinj hbd o hstrict gap hgap
  obtain ⟨⟨w, hw0, hwB, hs⟩, _⟩ :=
    c.route_of_support_gap_selected_degree hsmall a b row hinj hbd o hstrict gap hgap hdegree
  exact HirschProduct.pad_walk _ (by omega) w hw0 hwB hs

#print axioms DeferredClipCertificate.sum_carrier_excess_with_run_correction
#print axioms DeferredClipCertificate.route_with_run_corrected_cost
end HirschRadial
