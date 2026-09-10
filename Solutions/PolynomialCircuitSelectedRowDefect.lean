import Mathlib
import Solutions.PolynomialCommonFaceEffectiveRows

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Row-level defect/excess budget for a vertex-to-vertex ambient row circuit.

Let `W` be the direction space of the minimal common face of `u,v`, let `E` be
the ambient rows that restrict nontrivially to `W`, and choose any `F ⊆ E`.
The neutral-rank defect left after retaining only the rows of `F` is charged by
the rows of `E` that were discarded. Combining this with the common-face row
count gives the subtraction-free inequality

`|F| + defect(F) + d ≤ n + dim W`.

If a later geometric lemma chooses one row of `F` for each true facet of the
common face, this specializes exactly to `(f-h)+delta ≤ n-d`. -/
theorem rowCircuit_selectedEffectiveRows_defect_budget
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b u v)) :
    F.card +
        ((commonFaceDim a b u v - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (v - u))).domRestrict
              (commonDirection a b u v)).range)) +
        d ≤
      n + commonFaceDim a b u v := by
  classical
  let W := commonDirection a b u v
  let E := effectiveRowsOnSubspace a W
  let Z := circuitNeutralRows a (v - u)
  let T := Z ∩ E
  let S := F ∩ Z
  have hST : S ⊆ T := by
    intro i hiS
    have hi := Finset.mem_inter.1 hiS
    exact Finset.mem_inter.2 ⟨hi.2, hF hi.1⟩
  have hfull :
      Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) =
        Module.finrank ℝ W - 1 := by
    simpa [T, Z, E, W, commonFaceDim] using
      rowCircuit_effectiveNeutral_rank_on_commonDirection_eq_faceDim_sub_one
        a b u v hu hcirc
  have hdef :
      (Module.finrank ℝ W - 1) -
          Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
        (T \ S).card :=
    restricted_rowEval_defect_le_deleted a W S T hST hfull
  have hdelSub : T \ S ⊆ E \ F := by
    intro i hi
    have hiTS := Finset.mem_sdiff.1 hi
    have hiT := Finset.mem_inter.1 hiTS.1
    apply Finset.mem_sdiff.2
    refine ⟨hiT.2, ?_⟩
    intro hiFmem
    apply hiTS.2
    exact Finset.mem_inter.2 ⟨hiFmem, hiT.1⟩
  have hdel : (T \ S).card ≤ (E \ F).card :=
    Finset.card_le_card hdelSub
  have hdefE :
      (Module.finrank ℝ W - 1) -
          Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
        (E \ F).card :=
    hdef.trans hdel
  have hbudget : E.card + d ≤ n + Module.finrank ℝ W := by
    simpa [E, W, commonFaceDim] using
      commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b u v
  have hF' : F ⊆ E := by simpa [E, W] using hF
  have hcard : (E \ F).card + F.card = E.card :=
    Finset.card_sdiff_add_card_eq_card hF'
  have hmain :
      F.card +
          ((Module.finrank ℝ W - 1) -
            Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range)) +
          d ≤
        n + Module.finrank ℝ W := by
    omega
  simpa [S, Z, W, commonFaceDim] using hmain

/-- Rearranged form of `rowCircuit_selectedEffectiveRows_defect_budget`, stated
in the traditional facet-excess style. The premise `d ≤ n` avoids ambiguity
from truncated subtraction on the ambient excess. -/
theorem rowCircuit_selectedEffectiveRows_excess_defect
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b u v))
    (hdn : d ≤ n) :
    (F.card - commonFaceDim a b u v) +
        ((commonFaceDim a b u v - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (v - u))).domRestrict
              (commonDirection a b u v)).range)) ≤
      n - d := by
  have h := rowCircuit_selectedEffectiveRows_defect_budget
    a b u v hu hcirc F hF
  omega

#print axioms rowCircuit_selectedEffectiveRows_defect_budget
#print axioms rowCircuit_selectedEffectiveRows_excess_defect

end HirschCircuitLocalization
