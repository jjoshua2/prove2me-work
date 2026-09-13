import Solutions.PolynomialNearGeodesicWindows
import Solutions.PolynomialGeodesicRowIncidence

/-!
# Reuse concurrent #207's occurrence windows in #206's geometric interface

The positional graph theorem was independently prepared in #207 while this
continuation was running. Reuse that implementation instead of introducing a
second file with the same name or duplicating its graph proof. The remaining
geometric adapter counts repeated portal occurrences exactly as before.
New candidate; #206 and #207 must be integrated before this module builds.
-/
open scoped BigOperators
open Set
set_option autoImplicit false
noncomputable section
namespace HirschRegionRoute

/-- #207's position load is definitionally the all-available contact load
used by #206. No no-revisit premise or label deduplication is introduced. -/
theorem near_geodesic_total_position_load
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (k : ℕ) (hp : p.length ≤ G.dist u v + k)
    (available : Finset V) (positions : Finset ℕ)
    (hpos : positions ⊆ Finset.range (p.length+1)) :
    (∑ j ∈ positions, availableContactLoad G available (p.getVert j)) ≤
      (k+3)*available.card := by
  have h := HirschPortalDebt.total_position_load_le p k hp available positions
    (by intro j hj; have hj' := Finset.mem_range.mp (hpos hj); omega)
  simpa only [availableContactLoad, HirschPortalDebt.positionLoad,
    ClosedNear, HirschPortalDebt.Contact] using h

#print axioms near_geodesic_total_position_load
end HirschRegionRoute
