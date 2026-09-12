import Mathlib

theorem Hirsch.shortest_region_path_with_deferred_pair_costs
    {V ι : Type*} (S : ι → Set V) (G : SimpleGraph ι)
    (hoverlap : ∀ i j, G.Adj i j → ∃ z, z ∈ S i ∧ z ∈ S j)
    {i j : ι} (hreach : G.Reachable i j)
    (u v : V) (hu : u ∈ S i) (hv : v ∈ S j) :
    ∃ p : G.Walk i j,
      p.length = G.dist i j ∧ p.IsPath ∧
      (∀ r s : ℕ, r + 1 < s → s ≤ p.length →
        ¬ G.Adj (p.getVert r) (p.getVert s)) ∧
      ∃ legs : List (ι × V × V),
        legs.map Prod.fst = p.support ∧
        (legs.map Prod.fst).Nodup ∧
        (∀ leg ∈ legs, leg.2.1 ∈ S leg.1 ∧ leg.2.2 ∈ S leg.1) ∧
        ∀ (H : SimpleGraph V) (C : ι → V → V → ℕ),
          (∀ leg ∈ legs, ∃ q : H.Walk leg.2.1 leg.2.2,
            q.length ≤ C leg.1 leg.2.1 leg.2.2) →
          ∃ q : H.Walk u v,
            q.length ≤ (legs.map fun leg => C leg.1 leg.2.1 leg.2.2).sum := by sorry
