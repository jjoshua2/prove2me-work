import Solutions.PolynomialChordlessCarrierExcessTradeoff
import Solutions.PolynomialMaximalSupportClipping

/-!
# Exact selected-neighbor budgets for the actual clipping certificate

Continuation of merged #200, retaining the actual selected-neighbor count.

Do not replace the actual blocked-label count by its upper bound three.
For r selected labels and selected degree deg(i), the exact geometric saving is

  carrierExcess(i) + r <= (n-d) + 1 + deg(i).

Consequently a certificate with r + g = n-d is entirely in the established
small-excess regime whenever g + deg(i) <= 2 for every actually selected pair.
Besides maximal support, this covers deficit one with selected degree <= 1,
and deficit two with selected degree zero. No unused-pair route is assumed.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section

namespace HirschRegionRoute

/-- Neighbors among the selected labels, not among every mixed path label. -/
def selectedNeighborFinset
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) (i : V) : Finset V :=
  cuts ∩ supportNeighborFinset p i

theorem blockedSelectedFinset_eq_insert_selectedNeighbor
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) (i : V) (hi : i ∈ cuts) :
    blockedSelectedFinset p cuts i = insert i (selectedNeighborFinset p cuts i) := by
  ext x
  simp only [blockedSelectedFinset, selectedNeighborFinset,
    Finset.mem_inter, Finset.mem_insert]
  aesop

theorem blockedSelectedFinset_card_eq_selectedDegree_add_one
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) (i : V) (hi : i ∈ cuts) :
    (blockedSelectedFinset p cuts i).card =
      (selectedNeighborFinset p cuts i).card + 1 := by
  classical
  have hnot : i ∉ selectedNeighborFinset p cuts i := by
    intro h
    have hneigh := (Finset.mem_inter.mp h).2
    have hadj := (Finset.mem_filter.mp hneigh).2
    exact hadj.ne rfl
  rw [blockedSelectedFinset_eq_insert_selectedNeighbor p cuts i hi,
    Finset.card_insert_of_notMem hnot]

/-- This identity is exact, including one-label and empty-neighbor cases. -/
theorem nonneighbor_card_add_selectedDegree_add_one
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) (i : V) (hi : i ∈ cuts) :
    (nonneighborSelectedFinset p cuts i).card +
      ((selectedNeighborFinset p cuts i).card + 1) = cuts.card := by
  have hsub : blockedSelectedFinset p cuts i ⊆ cuts := Finset.inter_subset_left
  have hsplit := Finset.card_sdiff_add_card_eq_card hsub
  rw [blockedSelectedFinset_card_eq_selectedDegree_add_one p cuts i hi] at hsplit
  simpa [nonneighborSelectedFinset] using hsplit

theorem selectedNeighborFinset_card_le_two
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hchord : WalkChordless p)
    (cuts : Finset V) (i : V) (hi : i ∈ p.support) :
    (selectedNeighborFinset p cuts i).card ≤ 2 := by
  have hsub : selectedNeighborFinset p cuts i ⊆ supportNeighborFinset p i :=
    Finset.inter_subset_right
  exact (Finset.card_le_card hsub).trans
    (supportNeighborFinset_card_le_two p hchord i hi)

/-- A reusable nontruncated summed resource inequality. This does not assert
that carrier excess is a routing cost outside the small-excess regime. -/
theorem sum_exact_selected_budgets
    {V : Type*} (cuts : Finset V) (excess degree : V → ℕ) (e : ℕ)
    (h : ∀ i ∈ cuts, excess i + cuts.card ≤ e + 1 + degree i) :
    (∑ i ∈ cuts, excess i) + cuts.card * cuts.card ≤
      cuts.card * (e + 1) + ∑ i ∈ cuts, degree i := by
  have hs := Finset.sum_le_sum h
  simpa [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] using hs

/-- A high-excess call at support deficit one must have TWO selected neighbors.
At deficit two, it must have at least one. These are localization statements,
not lower bounds on the actual graph distance. -/
theorem high_excess_forces_selected_degree
    (delta r e degree gap : ℕ)
    (hbudget : delta + r ≤ e + 1 + degree)
    (hgap : r + gap = e) (hhigh : 4 ≤ delta) :
    3 ≤ gap + degree := by
  omega

end HirschRegionRoute

namespace HirschCircuitLocalization
open HirschRegionRoute

/-- Exact version of #193's carrier saving. Chordlessness is not needed for
this inequality: it is needed only to bound the actual selected degree by two.
The proof retains the whole disjoint-row family that #193 already constructs. -/
theorem commonFace_minExcess_add_selected_le_exact_degree_budget
    {d n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact (Hpoly a b))
    (hF : ∀ k, IsExtreme ℝ (Hpoly a b) (F k))
    (hclosed : ∀ k, IsClosed (F k))
    (row : ι → Fin n) {s t : ι}
    (path : (intersectionGraph
      (fun k => extremePoints ℝ (Hpoly a b) ∩ F k)).Walk s t)
    (cuts : Finset ι) (hcuts : cuts ⊆ path.support.toFinset)
    (hrowinj : Set.InjOn row (↑cuts : Set ι))
    (hface : ∀ k, k ∈ cuts → F k = hpolyRowFace a b (row k))
    (i : ι) (hi : i ∈ cuts)
    (p q : EuclideanSpace ℝ (Fin d))
    (hp : p ∈ extremePoints ℝ (Hpoly a b))
    (hq : q ∈ extremePoints ℝ (Hpoly a b))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hai : a (row i) ≠ 0)
    (hpi : ⟪a (row i), p⟫ = b (row i))
    (hqi : ⟪a (row i), q⟫ = b (row i)) :
    commonFacePresentationExcess a b p q + cuts.card ≤
      (n - d) + 1 + (selectedNeighborFinset path cuts i).card := by
  classical
  let S : Finset ι := nonneighborSelectedFinset path cuts i
  let J : Finset (Fin n) := S.image row
  have hScuts : S ⊆ cuts := by
    intro k hk
    exact (mem_nonneighborSelectedFinset path cuts hcuts i k hk).1
  have hSinj : Set.InjOn row (↑S : Set ι) := by
    intro x hx y hy hxy
    exact hrowinj (hScuts hx) (hScuts hy) hxy
  have hJcard : J.card = S.card := Finset.card_image_iff.mpr hSinj
  have hJdisj : ∀ j, j ∈ J →
      Disjoint (hpolyRowFace a b (row i)) (hpolyRowFace a b j) := by
    intro j hj
    obtain ⟨k, hkS, hrow⟩ := Finset.mem_image.mp hj
    have hkInfo := mem_nonneighborSelectedFinset path cuts hcuts i k hkS
    have hkcut : k ∈ cuts := hkInfo.1
    have hki : i ≠ k := hkInfo.2.1.symm
    have hdisjF : Disjoint (F i) (F k) :=
      closed_extreme_faces_disjoint_of_region_nonadj
        (Hpoly a b) F hP hF hclosed hki hkInfo.2.2
    rw [hface i hi, hface k hkcut] at hdisjF
    simpa [hrow] using hdisjF
  have hsave := commonFace_minExcess_add_disjoint_rowFaces_le
    a b p q hp hq hbd (row i) hai hpi hqi J hJdisj
  rw [hJcard] at hsave
  have hsplit := nonneighbor_card_add_selectedDegree_add_one path cuts i hi
  change S.card + ((selectedNeighborFinset path cuts i).card + 1) = cuts.card at hsplit
  unfold commonFacePresentationExcess
  omega

end HirschCircuitLocalization

namespace HirschRadial
open HirschRegionRoute HirschCircuitLocalization

variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Degree in the actual selected cut support of this exact certificate. -/
def DeferredClipCertificate.selectedCutDegree
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {aj : ι → EuclideanSpace ℝ (Fin d)} {bj : ι → ℝ}
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate P aj bj D u v) (i : ι) : ℕ :=
  (selectedNeighborFinset c.path
    (c.cutSupport.image (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2))))
    (Sum.inl i)).card

/-- The exact inequality applies to the same portal pair and path that the
clipping callback charges; no new path or new portal choices are made. -/
theorem DeferredClipCertificate.used_carrier_exact_selected_budget
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (leg : RegionLeg ι (EuclideanSpace ℝ (Fin d)))
    (hleg : leg ∈ clipRepairCutLegs c.legs) :
    commonFacePresentationExcess a b leg.entry leg.exit + c.cutSupport.card ≤
      (n - d) + 1 + c.selectedCutDegree leg.label := by
  classical
  let F := clipRepairPathRegion (D := D) (Hpoly a b)
    (fun i => a (row i)) (fun i => b (row i)) c.trace u v
  let cuts := c.cutSupport.image (Sum.inl : ι → Sum ι (Sum (Fin D) (Fin 2)))
  let rows : Sum ι (Sum (Fin D) (Fin 2)) → Fin n :=
    fun k => match k with | .inl i => row i | .inr _ => row leg.label
  have hcsub : cuts ⊆ c.path.support.toFinset := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨l, hl, hli⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
    have hm := (cut_leg_mem_iff c l).mp hl
    have hlabel : Sum.inl l.label ∈ c.legs.map RegionLeg.label :=
      List.mem_map.mpr ⟨_, hm, rfl⟩
    rw [c.labels] at hlabel
    exact List.mem_toFinset.mpr (by simpa [hli] using hlabel)
  have hcnum : cuts.card = c.cutSupport.card :=
    Finset.card_image_of_injective _ Sum.inl_injective
  have hrows : Set.InjOn rows (↑cuts : Set (Sum ι (Sum (Fin D) (Fin 2)))) := by
    intro x hx y hy he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact congrArg Sum.inl (hinj he)
  have hfaces : ∀ k ∈ cuts, F k = hpolyRowFace a b (rows k) := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    rfl
  have hi : Sum.inl leg.label ∈ cuts :=
    Finset.mem_image.mpr ⟨leg.label, List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨leg, hleg, rfl⟩), rfl⟩
  have hfit := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
  have hp : leg.entry ∈ extremePoints ℝ (Hpoly a b) := hfit.1.1
  have hq : leg.exit ∈ extremePoints ℝ (Hpoly a b) := hfit.2.1.1
  have hpi : ⟪a (row leg.label), leg.entry⟫ = b (row leg.label) := hfit.1.2.2
  have hqi : ⟪a (row leg.label), leg.exit⟫ = b (row leg.label) := hfit.2.1.2.2
  have hn := row_ne_zero_of_tight_and_strict a b (row leg.label) leg.entry o
    hpi (hstrict leg.label)
  have htrade := commonFace_minExcess_add_selected_le_exact_degree_budget
    a b F (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hpoly_isClosed a b, hbd⟩)
    c.facesExtreme c.facesClosed rows c.path cuts hcsub hrows hfaces
    (.inl leg.label) hi leg.entry leg.exit hp hq hbd hn hpi hqi
  rw [hcnum] at htrade
  exact htrade

/-- Generalized easy-support regime. `gap=0` covers maximal support;
`gap=1` covers a selected matching; `gap=2` covers independent selected cuts.
The result gives an exact additive ordinary-edge route AND its safe 3r bound.
The hypothesis concerns only selected adjacency, not any local route cost. -/
theorem DeferredClipCertificate.route_of_support_gap_selected_degree
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (gap : ℕ) (hgap : c.cutSupport.card + gap = n - d)
    (hdegree : ∀ leg ∈ clipRepairCutLegs c.legs,
      gap + c.selectedCutDegree leg.label ≤ 2) :
    Route (Adj (Hpoly a b))
      (D + ((clipRepairCutLegs c.legs).map fun leg =>
        commonFacePresentationExcess a b leg.entry leg.exit).sum) u v ∧
    ((clipRepairCutLegs c.legs).map fun leg =>
      commonFacePresentationExcess a b leg.entry leg.exit).sum ≤ 3 * c.cutSupport.card := by
  have heasy : ∀ leg ∈ clipRepairCutLegs c.legs,
      commonFacePresentationExcess a b leg.entry leg.exit ≤ 3 := by
    intro leg hleg
    have ht := c.used_carrier_exact_selected_budget a b row hinj hbd o hstrict leg hleg
    have hd := hdegree leg hleg
    omega
  have hlocal : ∀ leg ∈ clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b))
        (commonFacePresentationExcess a b leg.entry leg.exit) leg.entry leg.exit := by
    intro leg hleg
    have hf := c.fits _ ((cut_leg_mem_iff c leg).mp hleg)
    have hdiam := commonFace_diamLE_minPresentationExcess_of_le_three
      hsmall a b leg.entry leg.exit hbd hf.1.1.1 (heasy leg hleg)
    exact extreme_face_region (Hpoly a b) (commonFace a b leg.entry leg.exit)
      (commonFacePresentationExcess a b leg.entry leg.exit)
      (commonFace_isExtreme a b leg.entry leg.exit) hdiam
      leg.entry ⟨hf.1.1, commonFace_u_mem a b _ _ hf.1.1.1⟩
      leg.exit ⟨hf.2.1.1, commonFace_x_mem a b _ _ hf.2.1.1.1⟩
  refine ⟨c.assemble (fun _ p q => commonFacePresentationExcess a b p q) hlocal, ?_⟩
  have hsum : ∀ ls : List (RegionLeg ι (EuclideanSpace ℝ (Fin d))),
      (∀ leg ∈ ls, commonFacePresentationExcess a b leg.entry leg.exit ≤ 3) →
      (ls.map fun leg => commonFacePresentationExcess a b leg.entry leg.exit).sum ≤
        3 * ls.length := by
    intro ls
    induction ls with
    | nil => simp
    | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have hxs := ih (fun leg hleg => h leg (by simp [hleg]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  rw [c.cutSupport_card]
  exact hsum _ heasy

end HirschRadial

#print axioms HirschRegionRoute.blockedSelectedFinset_card_eq_selectedDegree_add_one
#print axioms HirschRegionRoute.nonneighbor_card_add_selectedDegree_add_one
#print axioms HirschRegionRoute.selectedNeighborFinset_card_le_two
#print axioms HirschRegionRoute.sum_exact_selected_budgets
#print axioms HirschRegionRoute.high_excess_forces_selected_degree
#print axioms HirschCircuitLocalization.commonFace_minExcess_add_selected_le_exact_degree_budget
#print axioms HirschRadial.DeferredClipCertificate.used_carrier_exact_selected_budget
#print axioms HirschRadial.DeferredClipCertificate.route_of_support_gap_selected_degree

namespace HirschRadial
open Set Hirsch HirschRegionRoute HirschCircuitLocalization
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem DeferredClipCertificate.selectedCutDegree_le_two
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {aj : ι → EuclideanSpace ℝ (Fin d)} {bj : ι → ℝ}
    {u v : EuclideanSpace ℝ (Fin d)} (c : DeferredClipCertificate P aj bj D u v)
    (leg : RegionLeg ι (EuclideanSpace ℝ (Fin d)))
    (hleg : leg ∈ clipRepairCutLegs c.legs) : c.selectedCutDegree leg.label ≤ 2 := by
  have hm := (cut_leg_mem_iff c leg).mp hleg
  have hl : Sum.inl leg.label ∈ c.legs.map RegionLeg.label :=
    List.mem_map.mpr ⟨_, hm, rfl⟩
  rw [c.labels] at hl
  exact selectedNeighborFinset_card_le_two c.path c.chordless _ _ hl

/-- Deficit-one high calls have exactly excess four and selected degree two.
This is a localization of the small-excess cutoff, not a distance obstruction. -/
theorem DeferredClipCertificate.excess_four_and_degree_two_of_deficit_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i, ⟪a (row i), o⟫ < b (row i))
    (hgap : c.cutSupport.card + 1 = n-d)
    (leg : RegionLeg ι (EuclideanSpace ℝ (Fin d)))
    (hleg : leg ∈ clipRepairCutLegs c.legs)
    (hh : 4 ≤ commonFacePresentationExcess a b leg.entry leg.exit) :
    commonFacePresentationExcess a b leg.entry leg.exit = 4 ∧
      c.selectedCutDegree leg.label = 2 := by
  have hb := c.used_carrier_exact_selected_budget a b row hinj hbd o hstrict leg hleg
  have hd := c.selectedCutDegree_le_two leg hleg
  omega


#print axioms DeferredClipCertificate.selectedCutDegree_le_two
#print axioms DeferredClipCertificate.excess_four_and_degree_two_of_deficit_one
end HirschRadial
