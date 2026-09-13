import Solutions.PolynomialMinkowskiExposedEdges
import Solutions.PolynomialGeodesicMassRouting

/-!
# Certified dual sweeps as solved leaves of the actual clipping construction

Support inequalities and exact exposed segments give ordinary edges. These
are geometric certificates, not a supplied diameter or graph-isomorphism
hypothesis. The finite Minkowski lemma discharges their step conditions.
For coordinate-simplex sums, the paper proof supplies 2L <= h(h+1).
This module assembles the SAME selected pairs under that explicit count bound.

New Lean candidates; the generating algorithm and intrinsic dictionary-count
proof are not silently claimed formalized by the certificate interface.
-/
open Set Hirsch HirschMinkowski HirschRegionRoute HirschPolynomialAccess
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace HirschDualSweep
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A step is certified by a supporting functional and its exact segment
slice. No knowledge of the vertex graph is part of the input certificate. -/
structure SweepCertificate (P : Set E) (x y : E) (L : ℕ) where
  points : ℕ → E
  first : points 0=x
  last : points L=y
  step : ∀ j<L, points j=points (j+1) ∨
    ∃ (f : E →ₗ[ℝ] ℝ) (β : ℝ),
      (∀ z∈P, f z≤β) ∧
      supportFace P f β=segment ℝ (points j) (points (j+1))

theorem SweepCertificate.route {P : Set E} {x y : E} {L : ℕ}
    (c : SweepCertificate P x y L) : Route (Adj P) L x y := by
  refine ⟨c.points,c.first,c.last,?_⟩
  intro j hj
  by_cases he : c.points j=c.points (j+1)
  · exact Or.inl he
  · rcases c.step j hj with h | ⟨f,β,hb,hf⟩
    · exact False.elim (he h)
    · exact Or.inr (adj_of_supportFace_eq_segment P f β _ _ he hb hf)

/-- Occurrence-indexed accounting for the root-direction count. -/
theorem sum_quadratic_direction_cost
    {α : Type*} (ls : List α) (cost dim : α → ℕ) (H : ℕ)
    (hcost : ∀ x∈ls, 2*cost x≤dim x*(dim x+1))
    (hdim : ∀ x∈ls, dim x≤H) :
    2*(ls.map cost).sum ≤ (H+1)*(ls.map dim).sum := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    have hx := hcost x (by simp)
    have hh := hdim x (by simp)
    have hprod := Nat.mul_le_mul_left (dim x) (Nat.add_le_add_right hh 1)
    have hx' : 2*cost x≤(H+1)*dim x := by nlinarith
    have ht := ih (fun y hy => hcost y (by simp [hy]))
      (fun y hy => hdim y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,Nat.mul_add]
    omega
end HirschDualSweep

namespace HirschRadial
open HirschDualSweep HirschCircuitLocalization
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual chosen carrier sweeps, without a uniform whole-face route premise.
The half-integral budget is returned subtraction-free alongside the exact
ordinary-edge route; a caller can pad it to its integral upper bound. -/
theorem DeferredClipCertificate.route_and_quadratic_sweep_budget
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i,⟪a (row i),o⟫<b (row i))
    (hall : Fintype.card ι=n-d)
    (cost : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hsweep : ∀ leg∈clipRepairCutLegs c.legs,
      SweepCertificate (commonFace a b leg.entry leg.exit) leg.entry leg.exit
        (cost leg.label leg.entry leg.exit))
    (hcount : ∀ leg∈clipRepairCutLegs c.legs,
      2*cost leg.label leg.entry leg.exit ≤
        commonFaceDim a b leg.entry leg.exit*(commonFaceDim a b leg.entry leg.exit+1))
    (H : ℕ) (hH : ∀ leg∈clipRepairCutLegs c.legs,commonFaceDim a b leg.entry leg.exit≤H) :
    Route (Adj (Hpoly a b))
      (D+((clipRepairCutLegs c.legs).map fun leg => cost leg.label leg.entry leg.exit).sum) u v ∧
    2*((clipRepairCutLegs c.legs).map fun leg => cost leg.label leg.entry leg.exit).sum ≤
      3*(n-d)*(H+1) := by
  have hlocal : ∀ leg∈clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (cost leg.label leg.entry leg.exit) leg.entry leg.exit := by
    intro leg hleg
    obtain ⟨w,hw0,hwL,hstep⟩ := (hsweep leg hleg).route
    refine ⟨w,hw0,hwL,?_⟩
    intro j hj
    rcases hstep j hj with h | h
    · exact Or.inl h
    · exact Or.inr (commonFace_adj_to_parent a b leg.entry leg.exit h)
  have hm := (c.carrier_size_mass_le a b row hinj hbd o hstrict 0 (by omega)).1
  have hm' : ((clipRepairCutLegs c.legs).map fun leg =>
      commonFaceDim a b leg.entry leg.exit).sum≤3*(n-d) := by simpa [hall] using hm
  have hs := sum_quadratic_direction_cost (clipRepairCutLegs c.legs)
    (fun leg => cost leg.label leg.entry leg.exit)
    (fun leg => commonFaceDim a b leg.entry leg.exit) H hcount hH
  refine ⟨c.assemble cost hlocal,?_⟩
  have h := hs.trans (Nat.mul_le_mul_left (H+1) hm')
  nlinarith

#print axioms DeferredClipCertificate.route_and_quadratic_sweep_budget
end HirschRadial
#print axioms HirschDualSweep.SweepCertificate.route
#print axioms HirschDualSweep.sum_quadratic_direction_cost
