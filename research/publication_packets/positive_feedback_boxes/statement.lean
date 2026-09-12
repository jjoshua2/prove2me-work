import Mathlib
import Definitions.Def_Hirsch_model
open Set Hirsch
open scoped BigOperators
theorem Hirsch.positive_feedback_box_diameter_le_dimension {d : ℕ} (C : Fin d → Fin d → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (b w : Fin d → ℝ) (hb : ∀ i, 0 < b i) (hw : ∀ i, 0 < w i)
    (hcw : ∀ i, (∑ j, C i j * w j) < w i) :
    DiamLE {x : Fin d → ℝ | (∀ i, 0 ≤ x i) ∧
      ∀ i, x i ≤ b i + ∑ j, C i j * x j} d := by sorry
