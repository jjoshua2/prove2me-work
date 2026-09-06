import Mathlib
import Definitions.Def_Hirsch_model

/-!
Walk-transfer lemmas adapted from `hirsch_contribution/HirschReductionDraft.lean`
to the mission's `DiamLE` predicate. These are local infrastructure, not a
Prove2Me submission.
-/

open Hirsch

variable {E F : Type*}

/-- An exact-length walk allowing stationary steps. -/
inductive PaddedWalk {V : Type*} (Adj : V → V → Prop) : V → V → ℕ → Prop where
  | nil (x : V) : PaddedWalk Adj x x 0
  | step {x y z : V} {n : ℕ} :
      (x = y ∨ Adj x y) → PaddedWalk Adj y z n → PaddedWalk Adj x z (n + 1)

/-- Map a walk through a function that sends an edge to an edge or a point. -/
theorem PaddedWalk.map
    {V W : Type*}
    {AdjV : V → V → Prop} {AdjW : W → W → Prop}
    (f : V → W)
    (hedge : ∀ {x y : V}, AdjV x y → f x = f y ∨ AdjW (f x) (f y))
    {x y : V} {n : ℕ} (h : PaddedWalk AdjV x y n) :
    PaddedWalk AdjW (f x) (f y) n := by
  induction h with
  | nil x => exact PaddedWalk.nil (f x)
  | @step x y z n hxy _ ih =>
      refine PaddedWalk.step ?_ ih
      rcases hxy with heq | hadj
      · exact Or.inl (congrArg f heq)
      · exact hedge hadj

/-- Diameter bounds descend along a vertex-surjective map that sends edges to
edges or stationary steps. This is the `graphDiamLE_of_surjective` argument
from the contribution draft, specialized to `DiamLE`. -/
theorem diamLE_of_extreme_map [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (P : Set E) (Q : Set F) (f : E → F)
    (_hvert : ∀ x ∈ Set.extremePoints ℝ P, f x ∈ Set.extremePoints ℝ Q)
    (hsection : ∀ y ∈ Set.extremePoints ℝ Q, ∃ x ∈ Set.extremePoints ℝ P, f x = y)
    (hedge : ∀ {x y : E}, Adj P x y → f x = f y ∨ Adj Q (f x) (f y))
    {n : ℕ} (hP : DiamLE P n) : DiamLE Q n := by
  intro u hu v hv
  obtain ⟨u', hu', rfl⟩ := hsection u hu
  obtain ⟨v', hv', rfl⟩ := hsection v hv
  obtain ⟨w, hw0, hwn, hs⟩ := hP u' hu' v' hv'
  refine ⟨fun i => f (w i), ?_, ?_, ?_⟩
  · simp [hw0]
  · simp [hwn]
  · intro i hi
    rcases hs i hi with heq | hadj
    · exact Or.inl (congrArg f heq)
    · exact hedge hadj
