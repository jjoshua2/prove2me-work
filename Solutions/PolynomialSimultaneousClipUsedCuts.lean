import Solutions.PolynomialSimultaneousClipUsedLabels

/-!
Project the path-sensitive simultaneous-clipping region support to the actual
cut-face labels.

A simple used-region list can contain three kinds of labels:
* cut faces, charged by `B i`;
* old-walk edge regions, charged one each;
* endpoint singleton regions, charged zero.

Because the whole region list is `Nodup`, the used old-edge labels are distinct
elements of `Fin D`; hence their total unit charge is at most `D`.  The cut
labels are also distinct.  Therefore one repaired clipped route costs at most

`D + sum_{i in usedCuts} B i`

for a `Nodup` list of actually used cut labels, instead of charging every
available cut face.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section
namespace HirschRadial

variable {ι : Type*}

/-- Keep only actual cut-face labels from a combined repair-region list. -/
def clipUsedCutLabels {D : ℕ}
    (l : List (Sum ι (Sum (Fin D) (Fin 2)))) : List ι :=
  l.filterMap (fun
    | .inl i => some i
    | .inr _ => none)

/-- Keep only old-walk edge labels from a combined repair-region list. -/
def clipUsedOldLabels {D : ℕ}
    (l : List (Sum ι (Sum (Fin D) (Fin 2)))) : List (Fin D) :=
  l.filterMap (fun
    | .inl _ => none
    | .inr (.inl k) => some k
    | .inr (.inr _) => none)

/-- Projecting a `Nodup` combined label list to cut labels preserves `Nodup`. -/
theorem clipUsedCutLabels_nodup {D : ℕ}
    {l : List (Sum ι (Sum (Fin D) (Fin 2)))}
    (hl : l.Nodup) : (clipUsedCutLabels l).Nodup := by
  refine hl.filterMap ?_
  intro a a' z hz hz'
  rcases a with i | r <;> rcases a' with j | r' <;> simp_all [clipUsedCutLabels]

/-- Projecting a `Nodup` combined label list to old-edge labels preserves
`Nodup`. -/
theorem clipUsedOldLabels_nodup {D : ℕ}
    {l : List (Sum ι (Sum (Fin D) (Fin 2)))}
    (hl : l.Nodup) : (clipUsedOldLabels l).Nodup := by
  refine hl.filterMap ?_
  intro a a' z hz hz'
  rcases a with i | r <;> rcases a' with j | r' <;>
    rcases r with k | t <;> try rcases r' with k' | t' <;>
    simp_all [clipUsedOldLabels]

/-- Exact decomposition of combined repair-region cost into used cut cost plus
the number of used old-walk edge regions. Singleton regions cost zero. -/
theorem clipUsedRegionCost_sum_eq_cut_old {D : ℕ}
    (B : ι → ℕ) (l : List (Sum ι (Sum (Fin D) (Fin 2)))) :
    (l.map (clipUsedRegionCost B)).sum =
      ((clipUsedCutLabels l).map B).sum + (clipUsedOldLabels l).length := by
  induction l with
  | nil => simp [clipUsedCutLabels, clipUsedOldLabels]
  | cons z l ih =>
      rcases z with i | r
      · simp [clipUsedRegionCost, clipUsedCutLabels, clipUsedOldLabels, ih,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · rcases r with k | t
        · simp [clipUsedRegionCost, clipUsedCutLabels, clipUsedOldLabels, ih,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        · simp [clipUsedRegionCost, clipUsedCutLabels, clipUsedOldLabels, ih]

/-- Distinct old-edge labels are a list of elements of `Fin D`, so at most D
can occur. -/
theorem clipUsedOldLabels_length_le {D : ℕ}
    {l : List (Sum ι (Sum (Fin D) (Fin 2)))}
    (hl : l.Nodup) : (clipUsedOldLabels l).length ≤ D := by
  have hnd := clipUsedOldLabels_nodup (ι := ι) hl
  simpa using hnd.length_le_card

/-- Convert the exact combined-label cost into a cut-only path-sensitive bound.
The returned cut labels are distinct and are exactly selected from the route's
simple repair-region support. -/
theorem route_clip_of_lifted_endpoints_with_parent_routes_used_cuts
    {d D : ℕ} [Fintype ι]
    (Q : Set (EuclideanSpace ℝ (Fin d))) (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (B : ι → ℕ)
    (hFaces : ∀ i, ∀ p ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, p⟫ = b i → ∀ q ∈ extremePoints ℝ (clipSet Q a b),
      ⟪a i, q⟫ = b i → Route (Adj (clipSet Q a b)) (B i) p q)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ Q)
    (hstrict : ∀ i, ⟪a i, o⟫ < b i)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (clipSet Q a b))
    (hv : v ∈ extremePoints ℝ (clipSet Q a b))
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ Q) (hy : y ∈ extremePoints ℝ Q)
    (hux : u = x ∨ ∃ i, ⟪a i, u⟫ = b i ∧ b i ≤ ⟪a i, x⟫)
    (hvy : v = y ∨ ∃ i, ⟪a i, v⟫ = b i ∧ b i ≤ ⟪a i, y⟫)
    (hwalk : Route (Adj Q) D x y) :
    ∃ cuts : List ι,
      cuts.Nodup ∧
      Route (Adj (clipSet Q a b)) (D + (cuts.map B).sum) u v := by
  classical
  obtain ⟨l, hnd, hr⟩ :=
    route_clip_of_lifted_endpoints_with_parent_routes_used_labels
      Q hQc hQ a b D B hFaces o ho hstrict u v hu hv x y hx hy hux hvy hwalk
  let cuts := clipUsedCutLabels l
  have hcuts : cuts.Nodup := clipUsedCutLabels_nodup hnd
  have hold : (clipUsedOldLabels l).length ≤ D :=
    clipUsedOldLabels_length_le hnd
  have hcostEq := clipUsedRegionCost_sum_eq_cut_old B l
  have hcost : (l.map (clipUsedRegionCost B)).sum ≤ D + (cuts.map B).sum := by
    dsimp [cuts]
    rw [hcostEq]
    omega
  obtain ⟨w, hw0, hwL, hs⟩ := hr
  refine ⟨cuts, hcuts, ?_⟩
  exact HirschProduct.pad_walk (Adj (clipSet Q a b)) hcost w hw0 hwL hs

#print axioms clipUsedCutLabels_nodup
#print axioms clipUsedOldLabels_nodup
#print axioms clipUsedRegionCost_sum_eq_cut_old
#print axioms clipUsedOldLabels_length_le
#print axioms route_clip_of_lifted_endpoints_with_parent_routes_used_cuts

end HirschRadial
