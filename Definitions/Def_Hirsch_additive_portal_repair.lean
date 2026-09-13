import Mathlib
open scoped BigOperators
namespace HirschRegionRoute
def Route {V : Type*} (R : V → V → Prop) (B : ℕ) (u v : V) : Prop :=
  ∃ w : ℕ → V, w 0 = u ∧ w B = v ∧
    ∀ j < B, w j = w (j + 1) ∨ R (w j) (w (j + 1))

end HirschRegionRoute
namespace HirschAdditiveAllowance
open HirschRegionRoute
variable {V : Type*}
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

end HirschAdditiveAllowance
