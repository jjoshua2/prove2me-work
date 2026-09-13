import Solutions.PolynomialAmortizedPortalRoutes

/-!
# Bounded additive excess overspending does not multiply across levels

Suppose each child excess is at most its parent's e, siblings total at most
 e+b, and dimensions strictly drop. Stop at excess <=b, with known leaf rate C.
Then actual edge cost is at most

  C*e + (1+b*C)*h*(e-b).

Natural subtraction truncates. The proof conserves SHIFTED excess on the
large-child skeleton; it does not multiply a factor-three bound per level.
The geometric availability of such splits is not asserted universally.
New source: no local Lean or Prove2Me verdict is claimed.
-/
open scoped BigOperators
open Hirsch HirschRegionRoute HirschAmortized
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace HirschAdditiveAllowance

/-- At most one large child is controlled by monotonicity. At least two are
controlled by the sibling sum; subtracting b per large child pays the spill. -/
theorem shifted_child_excess_conserved
    (n e b : ℕ) (mass : Fin n → ℕ)
    (hmono : ∀ i, mass i ≤ e) (hsum : (∑ i, mass i) ≤ e+b) :
    (∑ i, (mass i-b)) ≤ e-b := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => b < mass i)
  have hshift : (∑ i, (mass i-b)) = ∑ i ∈ S, (mass i-b) := by
    symm
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : b < mass i
    · simp [hi]
    · have hle : mass i ≤ b := by omega
      simp [hi, Nat.sub_eq_zero_of_le hle]
  by_cases hsmall : S.card ≤ 1
  · by_cases hn : S.Nonempty
    · obtain ⟨i, hi⟩ := hn
      have heq : S = {i} := by
        ext j
        constructor
        · intro hj
          exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hsmall) j hj i hi)
        · intro hj
          have hji := Finset.mem_singleton.mp hj
          simpa [hji] using hi
      rw [hshift, heq]
      simpa using Nat.sub_le_sub_right (hmono i) b
    · have heq := Finset.not_nonempty_iff_eq_empty.mp hn
      rw [hshift, heq]
      simp
  · have hcard : 2 ≤ S.card := by omega
    have hsplit : (∑ i ∈ S, (mass i-b)) + S.card*b = ∑ i ∈ S, mass i := by
      calc
        (∑ i ∈ S, (mass i-b)) + S.card*b = ∑ i ∈ S, ((mass i-b)+b) := by
          simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ = ∑ i ∈ S, mass i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Nat.sub_add_cancel (le_of_lt (Finset.mem_filter.mp hi).2)
    have hsub : (∑ i ∈ S, mass i) ≤ ∑ i, mass i := by
      simp only [S, Finset.sum_filter]
      exact Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    have htwice : 2*b ≤ S.card*b := Nat.mul_le_mul_right b hcard
    have ht := hsub.trans hsum
    rw [← hsplit] at ht
    rw [hshift]
    omega

def allowanceBudget (C b h e : ℕ) : ℕ := C*e+(1+b*C)*h*(e-b)

/-- The whole recurrence closes with a fixed polynomial once additive
overspending b and the small-leaf rate C are fixed. -/
theorem additive_allowance_node_bound
    (n h e b C : ℕ) (dims mass costs : Fin n → ℕ)
    (he : b < e) (hh : 0 < h)
    (hdrop : ∀ i, dims i < h) (hmono : ∀ i, mass i ≤ e)
    (hsum : (∑ i, mass i) ≤ e+b)
    (hcost : ∀ i, costs i ≤ allowanceBudget C b (dims i) (mass i)) :
    1+(∑ i, costs i) ≤ allowanceBudget C b h e := by
  have hshift := shifted_child_excess_conserved n e b mass hmono hsum
  have hweighted : (∑ i, dims i*(mass i-b)) ≤ (h-1)*(e-b) := by
    have hs : (∑ i, dims i*(mass i-b)) ≤ (h-1)*(∑ i, (mass i-b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right (mass i-b)
        (by have hi := hdrop i; omega))
    exact hs.trans (Nat.mul_le_mul_left (h-1) hshift)
  have hc : (∑ i, costs i) ≤ C*(∑ i, mass i) + (1+b*C)*(∑ i, dims i*(mass i-b)) := by
    have hs : (∑ i, costs i) ≤ ∑ i, allowanceBudget C b (dims i) (mass i) :=
      Finset.sum_le_sum (fun i _ => hcost i)
    simpa [allowanceBudget, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_assoc] using hs
  have hm := Nat.mul_le_mul_left C hsum
  have hw := Nat.mul_le_mul_left (1+b*C) hweighted
  have hz : 1 ≤ e-b := by omega
  have hpay : 1+b*C ≤ (1+b*C)*(e-b) := by
    simpa using Nat.mul_le_mul_left (1+b*C) hz
  have hid : (1+b*C)*(h-1)*(e-b)+(1+b*C)*(e-b) = (1+b*C)*h*(e-b) := by
    have hh' : h-1+1=h := by omega
    calc
      (1+b*C)*(h-1)*(e-b)+(1+b*C)*(e-b) = (1+b*C)*(h-1+1)*(e-b) := by ring
      _ = (1+b*C)*h*(e-b) := by rw [hh']
  simp only [Nat.mul_add] at hm
  rw [Nat.mul_comm C b] at hm
  unfold allowanceBudget
  simp only [Nat.mul_assoc] at hw hid ⊢
  omega

variable {V : Type*}

/-- Small leaves carry an actual certified route. Only their established
excess-threshold bound is used; no high-dimensional routing oracle is added. -/
inductive AdditiveRepair (R : V → V → Prop) (b C : ℕ) :
    V → V → ℕ → ℕ → ℕ → Prop
  | leaf (x y : V) (h e cost : ℕ) (he : e ≤ b)
      (hr : Route R cost x y) (hc : cost ≤ C*e) : AdditiveRepair R b C x y h e cost
  | node (h e n : ℕ) (u : V) (p : ℕ → V)
      (dims mass costs : Fin n → ℕ)
      (he : b < e) (hh : 0 < h) (hfirst : u=p 0 ∨ R u (p 0))
      (hdrop : ∀ i, dims i < h) (hmono : ∀ i, mass i ≤ e)
      (hsum : (∑ i, mass i) ≤ e+b)
      (children : ∀ i, AdditiveRepair R b C (p i.val) (p (i.val+1))
        (dims i) (mass i) (costs i)) :
      AdditiveRepair R b C u (p n) h e (1+∑ i, costs i)

theorem AdditiveRepair.sound
    {R : V → V → Prop} {b C h e cost : ℕ} {x y : V}
    (cert : AdditiveRepair R b C x y h e cost) :
    Route R cost x y ∧ cost ≤ allowanceBudget C b h e := by
  induction cert with
  | leaf x y h e cost he hr hc =>
    exact ⟨hr, by simpa [allowanceBudget, Nat.sub_eq_zero_of_le he] using hc⟩
  | node h e n u p dims mass costs he hh hfirst hdrop hmono hsum children ih =>
    refine ⟨append_routes R (single_route R hfirst)
      (route_chain R n p costs (fun i => (ih i).1)), ?_⟩
    exact additive_allowance_node_bound n h e b C dims mass costs he hh hdrop hmono hsum
      (fun i => (ih i).2)

#print axioms shifted_child_excess_conserved
#print axioms additive_allowance_node_bound
#print axioms AdditiveRepair.sound
end HirschAdditiveAllowance
