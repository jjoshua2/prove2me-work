import Solutions.PolynomialRegionRouting

/-!
# Cross-level accounting for finite ordinary-edge repair certificates

A node records its actual first edge and child repairs. Leaves are stationary
or actual edges, not a conjectural diameter oracle. Its charge is the POSITIVE
increase of 1+sum(child dimension*excess) over parent dimension*excess.
The theorem proves both an actual assembled route and its telescoping bound.
Dimension drops ensure the intended geometric recursion is well founded.

New proof candidate. No Lean compilation or platform acceptance is asserted.
-/
open scoped BigOperators
open Set Hirsch HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace HirschAmortized

variable {V : Type*} (R : V → V → Prop)

lemma append_routes {a b c : V} {A B : ℕ}
    (h₁ : Route R A a b) (h₂ : Route R B b c) : Route R (A+B) a c := by
  obtain ⟨w, hw0, hwA, hws⟩ := h₁
  obtain ⟨z, hz0, hzB, hzs⟩ := h₂
  exact HirschProduct.append_walk R w z hw0 hwA hz0 hzB hws hzs

lemma single_route {a b : V} (h : a=b ∨ R a b) : Route R 1 a b := by
  refine ⟨fun j => if j=0 then a else b, by simp, by simp, ?_⟩
  intro j hj
  have he : j=0 := by omega
  simpa [he] using h

/-- Finite chain adapter with different costs at each actual pair. -/
theorem route_chain (n : ℕ) (p : ℕ → V) (cost : Fin n → ℕ)
    (h : ∀ i : Fin n, Route R (cost i) (p i.val) (p (i.val+1))) :
    Route R (∑ i, cost i) (p 0) (p n) := by
  induction n generalizing p with
  | zero =>
    simpa using (show Route R 0 (p 0) (p 0) from
      ⟨fun _ => p 0, rfl, rfl, by intro j hj; omega⟩)
  | succ n ih =>
    have ht := ih (fun j => p (j+1)) (fun i => cost i.succ)
      (fun i => by simpa [Nat.add_assoc] using h i.succ)
    have hf := h (0 : Fin (n+1))
    have ha := append_routes R hf ht
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using ha

/-- This is a FINITE route certificate, not the assertion of a diameter bound.
Indices are: endpoints, dimension, excess, assembled cost, total charge. -/
inductive PortalRepair (R : V → V → Prop) : V → V → ℕ → ℕ → ℕ → ℕ → Prop
  | stationary (x : V) (h e : ℕ) : PortalRepair R x x h e 0 0
  | edge (x y : V) (h e : ℕ) (hh : 1 ≤ h) (he : 1 ≤ e)
      (hxy : x=y ∨ R x y) : PortalRepair R x y h e 1 0
  | node (h e n : ℕ) (u : V) (p : ℕ → V)
      (dims masses costs charges : Fin n → ℕ)
      (hfirst : u=p 0 ∨ R u (p 0))
      (hdrop : ∀ i, dims i < h)
      (children : ∀ i, PortalRepair R (p i.val) (p (i.val+1))
        (dims i) (masses i) (costs i) (charges i)) :
      PortalRepair R u (p n) h e (1+∑ i, costs i)
        ((∑ i, charges i) + ((1+∑ i, dims i*masses i) - h*e))

/-- Ordinary edges plus exact telescoping; there is no per-level multiplier. -/
theorem PortalRepair.sound {x y : V} {h e cost charge : ℕ}
    (cert : PortalRepair R x y h e cost charge) :
    Route R cost x y ∧ cost ≤ h*e+charge := by
  induction cert with
  | stationary x h e =>
    exact ⟨⟨fun _ => x, rfl, rfl, by intro j hj; omega⟩, by omega⟩
  | edge x y h e hh he hxy =>
    refine ⟨single_route R hxy, ?_⟩
    have hm := Nat.mul_le_mul hh he
    simpa using hm
  | node h e n u p dims masses costs charges hfirst hdrop children ih =>
    have ht := route_chain R n p costs (fun i => (ih i).1)
    have hr := append_routes R (single_route R hfirst) ht
    have hs : (∑ i, costs i) ≤ (∑ i, dims i*masses i) + ∑ i, charges i := by
      simpa only [Finset.sum_add_distrib] using
        Finset.sum_le_sum (fun i _ => (ih i).2)
    refine ⟨hr, ?_⟩
    omega

/-- A zero-charge geometric repair tree has the quadratic d*e route bound. -/
theorem PortalRepair.route_le_dimension_mul_excess
    {x y : V} {h e cost : ℕ}
    (cert : PortalRepair R x y h e cost 0) : Route R (h*e) x y := by
  obtain ⟨⟨w, hw0, hwC, hws⟩, hcost⟩ := cert.sound
  exact HirschProduct.pad_walk R (by simpa using hcost) w hw0 hwC hws

/-- The local charge vanishes under the stronger, easily checked mass-
conservation condition. It may also vanish WITHOUT mass conservation. -/
theorem local_charge_zero_of_mass_conservation
    (h e n : ℕ) (dims masses : Fin n → ℕ)
    (hh : 1 ≤ h) (he : 1 ≤ e)
    (hdrop : ∀ i, dims i < h) (hmass : (∑ i, masses i) ≤ e) :
    (1+(∑ i, dims i*masses i))-h*e = 0 := by
  have hsum : (∑ i, dims i*masses i) ≤ (h-1)*(∑ i, masses i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      Nat.mul_le_mul_right (masses i) (by have hi := hdrop i; omega))
  have hbound := hsum.trans (Nat.mul_le_mul_left (h-1) hmass)
  have hid : (h-1)*e+e = h*e := by
    have ht : h-1+1=h := by omega
    calc
      _ = (h-1+1)*e := by ring
      _ = h*e := by rw [ht]
  have hle : 1+(∑ i, dims i*masses i) ≤ h*e := by omega
  exact Nat.sub_eq_zero_of_le hle

#print axioms route_chain
#print axioms PortalRepair.sound
#print axioms PortalRepair.route_le_dimension_mul_excess
#print axioms local_charge_zero_of_mass_conservation
end HirschAmortized
