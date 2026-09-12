import Solutions.PolynomialPortalSignatureMass
import Solutions.PolynomialRegionRouting

/-!
# A cross-level invariant: edge count = endpoint rank + portal debt

Every tree leaf is an actual edge or stationary step, not a diameter oracle.
The splice charge is the triangle gap in the active-facet entry metric.
No disjointness of charges at different nodes is assumed. Geodesic portal
chains identify the sum of splice charges with their neutral-facet count.

New candidate. The simple-polytope fact "one facet enters across an edge"
and the geometric portal-chain recognition remain explicit interfaces.
-/
open Set HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschPortalDebt

universe u
variable {V : Type u} {α : Type*} [DecidableEq α]

/-- A finite, constructive assembly tree with certified edge leaves. -/
inductive EdgeTree (R : V → V → Prop) : V → V → Type u
  | stationary (v : V) : EdgeTree R v v
  | edge {u v : V} (h : R u v) : EdgeTree R u v
  | splice {u z v : V} (left : EdgeTree R u z) (right : EdgeTree R z v) : EdgeTree R u v

namespace EdgeTree
variable {R : V → V → Prop}

def length {u v : V} : EdgeTree R u v → ℕ
  | .stationary _ => 0
  | .edge _ => 1
  | .splice l r => l.length + r.length

/-- Geometric charge at a portal. It can be positive even when the same
original facet was already charged higher in the tree. -/
def debt (sig : V → Finset α) {u v : V} : EdgeTree R u v → ℕ
  | .stationary _ => 0
  | .edge _ => 0
  | @EdgeTree.splice _ _ u z v l r =>
      (entries (sig u) (sig z) + entries (sig z) (sig v) - entries (sig u) (sig v)) +
      l.debt sig + r.debt sig

/-- The exact global invariant is additive; repeated charges are retained. -/
theorem length_eq_entries_add_debt
    (sig : V → Finset α) (hedge : ∀ u v, R u v → entries (sig u) (sig v) = 1)
    {u v : V} (t : EdgeTree R u v) :
    t.length = entries (sig u) (sig v) + t.debt sig := by
  induction t with
  | stationary v => simp [length,debt,entries]
  | @edge u v h => simp [length,debt,hedge u v h]
  | @splice u z v l r ihl ihr =>
    have htri := entries_triangle (sig u) (sig z) (sig v)
    simp only [length,debt]
    omega

/-- Actual edge routes assemble independently of the accounting proof. -/
theorem route {u v : V} (t : EdgeTree R u v) : Route R t.length u v := by
  induction t with
  | stationary v => exact ⟨fun _ => v,rfl,rfl,by simp [length]⟩
  | @edge u v h =>
    refine ⟨fun k => if k=0 then u else v,by simp,by simp [length],?_⟩
    intro k hk
    have hk0 : k=0 := by change k<1 at hk; omega
    subst k
    simpa using (Or.inr h : u = v ∨ R u v)
  | @splice u z v l r ihl ihr =>
    obtain ⟨a,ha0,haN,has⟩ := ihl
    obtain ⟨b,hb0,hbN,hbs⟩ := ihr
    obtain ⟨w,hw0,hwN,hws⟩ := HirschProduct.append_walk R a b ha0 haN hb0 hbN has hbs
    exact ⟨w,hw0,hwN,hws⟩

/-- A bound on independently computed geometric debt becomes an actual
route bound. The theorem does not assert a universal bound on that debt. -/
theorem route_of_debt_le
    (sig : V → Finset α) (hedge : ∀ u v, R u v → entries (sig u) (sig v) = 1)
    {u v : V} (t : EdgeTree R u v) (B : ℕ) (hb : t.debt sig ≤ B) :
    Route R (entries (sig u) (sig v) + B) u v := by
  have hlen : t.length ≤ entries (sig u) (sig v) + B := by
    rw [t.length_eq_entries_add_debt sig hedge]
    omega
  obtain ⟨w,hw0,hwN,hws⟩ := t.route
  exact HirschProduct.pad_walk R hlen w hw0 hwN hws

#print axioms length_eq_entries_add_debt
#print axioms route
#print axioms route_of_debt_le
end EdgeTree
end HirschPortalDebt
