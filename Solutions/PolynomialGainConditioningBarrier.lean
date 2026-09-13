import Solutions.PolynomialGeodesicMassRouting

/-!
# Affine-invariant conditioning obstruction and actual quartic carrier costs

The cross-ratio identity rules out uniformly conditioning every independent
row pair even by arbitrary invertible linear maps. It is a conditioning
obstruction, NOT a graph-diameter lower bound. The final route wrapper keeps
actual local routes and their quartic count premise explicit; it does not
import the external wide-normal-cone theorem as an axiom.
NEW UNCOMPILED candidates; see the exact geometric scope in the proof note.
-/
open Set Hirsch HirschRegionRoute HirschCircuitLocalization HirschPolynomialAccess
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschGainBarrier

def det2 (u v : Fin 2 → ℝ) : ℝ := u 0*v 1-u 1*v 0

/-- Taking u,v to be the rows of ANY invertible preconditioner preserves the
same identity for e1,e2,e1+e2,e1+(1+epsilon)e2. -/
theorem cross_ratio_determinant_identity (u v : Fin 2 → ℝ) (ε : ℝ) :
    det2 (u+v) (u+(1+ε) • v)*det2 u v =
      -ε*det2 u (u+v)*det2 v (u+(1+ε) • v) := by
  simp only [det2,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Normalized areas are sines in [0,1]. The determinant identity cancels
all four row norms and forces delta^2<=epsilon. The Euclidean normalization
bridge is in the paper argument, not hidden in an extra geometric axiom. -/
theorem cross_ratio_forces_small_separation (s t u v δ ε : ℝ)
    (hs : 0≤s) (ht : 0≤t) (hu : 0≤u) (hv : 0≤v)
    (hu1 : u≤1) (hv1 : v≤1) (hδ : 0≤δ) (hε : 0≤ε)
    (hδs : δ≤s) (hδt : δ≤t) (he : s*t=ε*u*v) : δ^2≤ε := by
  have hl := mul_le_mul hδs hδt hδ hs
  have huv : u*v≤1 := by
    have h := mul_le_mul hu1 hv1 hv (by norm_num : (0:ℝ)≤1)
    simpa using h
  have hr := mul_le_mul_of_nonneg_left huv hε
  nlinarith

/-- Exact occurrence-indexed accounting for degree-four local solved costs. -/
theorem sum_quartic_cost_le_dimension_mass {α : Type*}
    (ls : List α) (cost dim : α → ℕ) (K H : ℕ)
    (hcost : ∀ x∈ls,cost x≤K*(dim x)^4)
    (hdim : ∀ x∈ls,dim x≤H) :
    (ls.map cost).sum≤K*H^3*(ls.map dim).sum := by
  apply list_cost_sum_le_scaled_mass
  intro x hx
  have hd := hdim x hx
  have h₂ := Nat.mul_le_mul hd hd
  have h₃ := Nat.mul_le_mul h₂ hd
  have h₄ := Nat.mul_le_mul_right (dim x) h₃
  have hK := Nat.mul_le_mul_left K h₄
  have hc := hcost x hx
  nlinarith

#print axioms cross_ratio_determinant_identity
#print axioms cross_ratio_forces_small_separation
#print axioms sum_quartic_cost_le_dimension_mass
end HirschGainBarrier

namespace HirschRadial
open HirschGainBarrier
variable {d n D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each actual carrier needs its own certified intrinsic bound. Calibrating
an ambient gain model does NOT automatically give the same h^4 bound with its
smaller face dimension; the inherited bound retains the ambient parameter. -/
theorem DeferredClipCertificate.route_of_quantized_gain_costs
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (row : ι → Fin n) (hinj : Function.Injective row)
    {u v : EuclideanSpace ℝ (Fin d)}
    (c : DeferredClipCertificate (Hpoly a b) (fun i => a (row i))
      (fun i => b (row i)) D u v)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (o : EuclideanSpace ℝ (Fin d)) (hstrict : ∀ i,⟪a (row i),o⟫<b (row i))
    (hall : Fintype.card ι=n-d)
    (cost : ι → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℕ)
    (hroute : ∀ leg∈clipRepairCutLegs c.legs,
      Route (Adj (Hpoly a b)) (cost leg.label leg.entry leg.exit) leg.entry leg.exit)
    (R H : ℕ)
    (hcost : ∀ leg∈clipRepairCutLegs c.legs,
      cost leg.label leg.entry leg.exit≤360*R^2*(commonFaceDim a b leg.entry leg.exit)^4)
    (hH : ∀ leg∈clipRepairCutLegs c.legs,commonFaceDim a b leg.entry leg.exit≤H) :
    Route (Adj (Hpoly a b)) (D+1080*R^2*H^3*(n-d)) u v := by
  have hm := (c.carrier_size_mass_le a b row hinj hbd o hstrict 0 (by omega)).1
  have hm' : ((clipRepairCutLegs c.legs).map fun leg =>
      commonFaceDim a b leg.entry leg.exit).sum≤3*(n-d) := by simpa [hall] using hm
  have hs := sum_quartic_cost_le_dimension_mass (clipRepairCutLegs c.legs)
    (fun leg => cost leg.label leg.entry leg.exit)
    (fun leg => commonFaceDim a b leg.entry leg.exit) (360*R^2) H hcost hH
  have hb : ((clipRepairCutLegs c.legs).map fun leg =>
      cost leg.label leg.entry leg.exit).sum≤1080*R^2*H^3*(n-d) := by
    have h := hs.trans (Nat.mul_le_mul_left (360*R^2*H^3) hm')
    nlinarith
  obtain ⟨w,hw0,hwL,hstep⟩ := c.assemble cost hroute
  exact HirschProduct.pad_walk _ (Nat.add_le_add_left hb D) w hw0 hwL hstep

#print axioms DeferredClipCertificate.route_of_quantized_gain_costs
end HirschRadial
