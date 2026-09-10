import Mathlib
import Theorems.Thm_Hirsch_larman_bound
import Solutions.PolynomialUnboundedCutCore

open scoped RealInnerProductSpace
open Set Hirsch HirschCut HirschClip

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschUnboundedCut

variable {d n : ℕ}

lemma hpoly_convex
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy α β hα hβ hαβ i
  change ⟪a i, α • x + β • y⟫ ≤ b i
  rw [inner_combo]
  calc
    α * ⟪a i, x⟫ + β * ⟪a i, y⟫ ≤ α * b i + β * b i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) hα)
        (mul_le_mul_of_nonneg_left (hy i) hβ)
    _ = b i := by rw [← add_mul, hαβ, one_mul]

/-- A bounded clipped H-polyhedron has a connected vertex graph even if the
outer H-polyhedron is unbounded. Larman is applied only to the n+1-row clip;
its numerical bound is used for existence and discarded by the routing core. -/
lemma bounded_hpoly_clip_connected
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β})) :
    ∃ D : ℕ, Walk (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) D u v := by
  let a' : Fin (n + 1) → EuclideanSpace ℝ (Fin d) := Fin.lastCases c a
  let b' : Fin (n + 1) → ℝ := Fin.lastCases β b
  have hclip : Hpoly a' b' = Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β} := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro i
        simpa [a', b'] using hx i.castSucc
      · simpa [a', b'] using hx (Fin.last n)
    · rintro ⟨hx, hcut⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [a', b'] using hcut
      · simpa [a', b'] using hx j
  have hne' : (Hpoly a' b').Nonempty := by
    rw [hclip]
    exact ⟨u, hu.1⟩
  have hbd' : Bornology.IsBounded (Hpoly a' b') := by rwa [hclip]
  have hdiam := Hirsch.larman_bound d (n + 1) a' b' hne' hbd'
  rw [hclip] at hdiam
  exact ⟨(n + 1) * 2 ^ (d - 3), hdiam u hu v hv⟩

end HirschUnboundedCut
