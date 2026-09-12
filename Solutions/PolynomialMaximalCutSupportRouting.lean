import Mathlib
import Solutions.PolynomialChordlessCarrierExcessTradeoff
import Solutions.PolynomialMinCarrierExcessRouting
import Solutions.PolynomialSimultaneousClipDeferredPairLegs

/-!
# Maximal used cut support closes by exact small-carrier costs

This is the algebra/routing composition after deferred clipping.  It assumes the
shortest/chordless mixed face path, the selected cut labels, the actual cut
portal pairs, and the deferred route callback have already been chosen.  If the
selected cut support has the full ambient row-excess size `n-d`, the verified
chordless-support theorem forces every charged portal-pair carrier to have
minimum-presentation excess at most three.  The verified exact small-carrier
routing theorem then discharges precisely those local calls.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschMaxSupport

open HirschPolynomialAccess HirschCircuitLocalization HirschRegionRoute HirschRadial

private theorem list_sum_le_three_mul_length
    {α : Type*} (l : List α) (C : α → ℕ)
    (hC : ∀ x ∈ l, C x ≤ 3) :
    (l.map C).sum ≤ 3 * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : C x ≤ 3 := hC x (by simp)
      have hxs : ∀ y ∈ xs, C y ≤ 3 := by
        intro y hy
        exact hC y (by simp [hy])
      have ht := ih hxs
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- Abstract maximum-support composition for a deferred clipping path.

`mixed` is the mixed cut/old-edge/singleton region index.  The supplied `cuts`
are the selected cut-region labels on the chordless path, injectively mapped to
original rows.  Actual projected cut legs point back into `cuts`.  If the cut
support uses all `n-d` units of ambient row excess, then every selected cut leg
has carrier excess at most three and can be routed at its exact intrinsic
minimum-presentation excess.  Consequently the deferred global route has exact
cost `D + sum e_leg` and padded cost at most `D + 3*(n-d)`.
-/
theorem route_of_maximal_chordless_cut_support
    (hsmall : SmallExcessHpolyBound)
    {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (F : κ → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact (Hpoly a b))
    (hF : ∀ k, IsExtreme ℝ (Hpoly a b) (F k))
    (hclosed : ∀ k, IsClosed (F k))
    (row : κ → Fin n)
    {s t : κ}
    (p : (intersectionGraph (fun k => extremePoints ℝ (Hpoly a b) ∩ F k)).Walk s t)
    (hchord : WalkChordless p)
    (cuts : Finset κ)
    (hcuts : cuts ⊆ p.support.toFinset)
    (hrowinj : Set.InjOn row (↑cuts : Set κ))
    (hface : ∀ k, k ∈ cuts → F k = hpolyRowFace a b (row k))
    (hnonzero : ∀ k, k ∈ cuts → a (row k) ≠ 0)
    (hmax : cuts.card = n - d)
    (legs : List (RegionLeg ι (EuclideanSpace ℝ (Fin d))))
    (mixedLabel : ι → κ)
    (hlegCut : ∀ leg ∈ legs, mixedLabel leg.label ∈ cuts)
    (hlegCount : legs.length ≤ cuts.card)
    (hlegValid : ∀ leg ∈ legs,
      leg.entry ∈ extremePoints ℝ (Hpoly a b) ∧
      ⟪a (row (mixedLabel leg.label)), leg.entry⟫ = b (row (mixedLabel leg.label)) ∧
      leg.exit ∈ extremePoints ℝ (Hpoly a b) ∧
      ⟪a (row (mixedLabel leg.label)), leg.exit⟫ = b (row (mixedLabel leg.label)))
    (u v : EuclideanSpace ℝ (Fin d))
    (hdeferred :
      ∀ (C : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ),
        (∀ leg ∈ legs,
          Route (Adj (Hpoly a b)) (C leg.label leg.entry leg.exit)
            leg.entry leg.exit) →
        Route (Adj (Hpoly a b))
          (D + ((legs.map fun leg => C leg.label leg.entry leg.exit).sum)) u v) :
    ∃ exactCost : ℕ,
      exactCost =
        ((legs.map fun leg =>
          commonFacePresentationExcess a b leg.entry leg.exit).sum) ∧
      Route (Adj (Hpoly a b)) (D + exactCost) u v ∧
      D + exactCost ≤ D + 3 * (n - d) := by
  classical
  have heasy : ∀ leg ∈ legs,
      commonFacePresentationExcess a b leg.entry leg.exit ≤ 3 := by
    intro leg hleg
    have hk : mixedLabel leg.label ∈ cuts := hlegCut leg hleg
    obtain ⟨hp, hpi, hq, hqi⟩ := hlegValid leg hleg
    have hthree :=
      commonFace_minExcess_le_three_of_chordless_maximal_rowFace_support
        a b F hP hF hclosed row p hchord cuts hcuts hrowinj hface hmax
        (mixedLabel leg.label) hk leg.entry leg.exit hp hq hbd
        (hnonzero _ hk) hpi hqi
    simpa [commonFacePresentationExcess] using hthree
  let C : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ :=
    fun _ x y => commonFacePresentationExcess a b x y
  have hlocal : ∀ leg ∈ legs,
      Route (Adj (Hpoly a b)) (C leg.label leg.entry leg.exit)
        leg.entry leg.exit := by
    intro leg hleg
    obtain ⟨hp, _hpi, hq, _hqi⟩ := hlegValid leg hleg
    have hD := commonFace_diamLE_minPresentationExcess_of_le_three
      hsmall a b leg.entry leg.exit hbd hp.1 (heasy leg hleg)
    exact extreme_face_region (Hpoly a b)
      (commonFace a b leg.entry leg.exit)
      (commonFacePresentationExcess a b leg.entry leg.exit)
      (commonFace_isExtreme a b leg.entry leg.exit) hD
      leg.entry ⟨hp, commonFace_u_mem a b _ _ hp.1⟩
      leg.exit ⟨hq, commonFace_x_mem a b _ _ hq.1⟩
  have hr := hdeferred C hlocal
  let exactCost :=
    (legs.map fun leg => commonFacePresentationExcess a b leg.entry leg.exit).sum
  have hsum3 : exactCost ≤ 3 * legs.length := by
    dsimp [exactCost]
    exact list_sum_le_three_mul_length legs
      (fun leg => commonFacePresentationExcess a b leg.entry leg.exit) heasy
  have hcost : exactCost ≤ 3 * (n - d) := by
    calc
      exactCost ≤ 3 * legs.length := hsum3
      _ ≤ 3 * cuts.card := Nat.mul_le_mul_left 3 hlegCount
      _ = 3 * (n - d) := by rw [hmax]
  refine ⟨exactCost, rfl, ?_, ?_⟩
  · simpa [C, exactCost] using hr
  · omega

#print axioms route_of_maximal_chordless_cut_support

end HirschMaxSupport
