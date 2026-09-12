import Mathlib
open scoped BigOperators
open Set
theorem Hirsch.geodesic_joint_budget_of_all_available_contacts {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (hp : p.length = G.dist u v)
    (available : Finset V) (labels : List V) (hnd : labels.Nodup)
    (hsub : ∀ i ∈ labels, i ∈ p.support) (delta : V → ℕ) (e : ℕ)
    (hbudget : ∀ i ∈ labels, delta i + available.card ≤ e +
      (available.filter (fun j => j = i ∨ G.Adj j i)).card) :
    (labels.map delta).sum + labels.length * available.card ≤
      labels.length * e + 3 * available.card := by sorry
