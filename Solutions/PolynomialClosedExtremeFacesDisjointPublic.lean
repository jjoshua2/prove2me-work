import Mathlib
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Public compact extreme-face disjointness theorem

This standalone theorem isolates the geometric contrapositive used by the
shortest-region Polynomial Hirsch repair line.  Two closed extreme faces of a
compact parent cannot intersect without sharing a parent extreme point.
Equivalently, if they share no parent extreme point, they are disjoint.

The source intentionally imports no private `Solutions.*` module so it can be
audited and published independently to Prove2Me.
-/

open scoped RealInnerProductSpace
open Set

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Hirsch

/-- Two closed extreme subsets of a compact parent which share no parent
extreme point are disjoint. -/
theorem closed_extreme_faces_disjoint_of_no_shared_parent_extreme
    {d : ℕ}
    (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P)
    (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (hno : ¬ ∃ v : EuclideanSpace ℝ (Fin d),
      v ∈ extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G) :
    Disjoint F G := by
  rw [Set.disjoint_left]
  intro x hxF hxG
  have hFGc : IsClosed (F ∩ G) := hFc.inter hGc
  have hFGe : IsExtreme ℝ P (F ∩ G) := hF.inter hG
  have hFGcompact : IsCompact (F ∩ G) :=
    hP.of_isClosed_subset hFGc hFGe.subset
  obtain ⟨v, hv⟩ :=
    hFGcompact.extremePoints_nonempty ⟨x, hxF, hxG⟩
  have hvP : v ∈ extremePoints ℝ P :=
    hFGe.extremePoints_subset_extremePoints hv
  exact hno ⟨v, hvP, hv.1.1, hv.1.2⟩

#print axioms closed_extreme_faces_disjoint_of_no_shared_parent_extreme

end Hirsch
