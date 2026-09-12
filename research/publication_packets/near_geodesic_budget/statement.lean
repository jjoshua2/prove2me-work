import Mathlib
open scoped BigOperators
open Set
theorem Hirsch.near_geodesic_occurrence_carrier_budget {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q)
    (available : Finset V) (positions : Finset ℕ)
    (hpositions : ∀ k ∈ positions, k ≤ p.length) (delta : ℕ → ℕ) (e : ℕ)
    (hbudget : ∀ k ∈ positions, delta k + available.card ≤ e +
      (available.filter (fun z => z = p.getVert k ∨ G.Adj z (p.getVert k))).card) :
    (∑ k ∈ positions, delta k) + positions.card * available.card ≤
      positions.card * e + (q+3)*available.card := by sorry
