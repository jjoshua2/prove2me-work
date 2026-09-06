import Mathlib

/-!
UNCOMPILED DRAFT. This file is generic logical scaffolding, NOT a Prove2Me
submission and NOT a proof of the Polynomial Hirsch Conjecture.

`PaddedWalk` below is a local model, not the mission's downloaded definition.
In `polynomial_from_balanced`, `Poly d n` is intended to package an n-row
H-polytope in ambient dimension d together with nonemptiness and boundedness.
The geometric balancing theorem and the balanced polynomial bound are explicit
hypotheses. The latter is conjectural. No statement below discharges it.

The file has not been checked with a Lean compiler. To use it, compile in the
server-pinned environment and adapt it to the actual mission definitions.
-/

namespace HirschReductionDraft

universe u v

/-- An exact-length walk allowing stationary steps. -/
inductive PaddedWalk {V : Type u} (Adj : V → V → Prop) : V → V → ℕ → Prop where
  | nil (x : V) : PaddedWalk Adj x x 0
  | step {x y z : V} {n : ℕ} :
      (x = y ∨ Adj x y) → PaddedWalk Adj y z n → PaddedWalk Adj x z (n + 1)

/-- Map a walk through a function that sends an edge to an edge or a point. -/
theorem PaddedWalk.map
    {V : Type u} {W : Type v}
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

/-- A generic padded-walk diameter predicate on a vertex type. -/
def GraphDiamLE {V : Type u} (Adj : V → V → Prop) (n : ℕ) : Prop :=
  ∀ x y : V, PaddedWalk Adj x y n

/-- Vertex-surjective maps with the edge-or-point property transfer bounds. -/
theorem graphDiamLE_of_surjective
    {V : Type u} {W : Type v}
    {AdjV : V → V → Prop} {AdjW : W → W → Prop}
    (f : V → W) (hsurj : Function.Surjective f)
    (hedge : ∀ {x y : V}, AdjV x y → f x = f y ∨ AdjW (f x) (f y))
    {n : ℕ} (hdiam : GraphDiamLE AdjV n) : GraphDiamLE AdjW n := by
  intro x y
  obtain ⟨x', hx⟩ := hsurj x
  obtain ⟨y', hy⟩ := hsurj y
  have hw := PaddedWalk.map f hedge (hdiam x' y')
  simpa only [hx, hy] using hw

/-- The ambient dimension after enough wedges, with natural subtraction. -/
def balancingDimension (d n : ℕ) : ℕ := d + (n - 2 * d)

theorem balancingDimension_le (d n : ℕ) :
    balancingDimension d n ≤ n + d := by
  unfold balancingDimension
  omega

theorem balancingDimension_eq_max (d n : ℕ) :
    balancingDimension d n = max d (n - d) := by
  unfold balancingDimension
  omega

theorem balanced_count_of_excess (d n : ℕ) (h : 2 * d ≤ n) :
    n + (n - 2 * d) = 2 * balancingDimension d n := by
  unfold balancingDimension
  omega

/--
Generic composition only: neither the geometric balancing theorem nor the
balanced polynomial bound is proved here. `Poly` and `Diam` are parameters.
-/
theorem polynomial_from_balanced
    (Poly : ℕ → ℕ → Type u)
    (Diam : ∀ {d n : ℕ}, Poly d n → ℕ → Prop)
    (mono : ∀ {d n : ℕ} (P : Poly d n) {a b : ℕ},
      a ≤ b → Diam P a → Diam P b)
    (balance : ∀ {d n : ℕ} (P : Poly d n),
      ∃ D : ℕ, D ≤ n + d ∧
        ∃ Q : Poly D (2 * D), ∀ L : ℕ, Diam Q L → Diam P L)
    (critical : ∃ C k : ℕ, ∀ D : ℕ, ∀ Q : Poly D (2 * D),
      Diam Q (C * D ^ k)) :
    ∃ C k : ℕ, ∀ d n : ℕ, ∀ P : Poly d n,
      Diam P (C * (n + d) ^ k) := by
  rcases critical with ⟨C, k, hcritical⟩
  refine ⟨C, k, ?_⟩
  intro d n P
  rcases balance P with ⟨D, hD, Q, htransfer⟩
  have hbound : C * D ^ k ≤ C * (n + d) ^ k := by
    gcongr <;> omega
  exact mono P hbound (htransfer (C * D ^ k) (hcritical D Q))

/-- The converse restriction changes the coefficient but not the exponent. -/
theorem balanced_from_polynomial
    (Poly : ℕ → ℕ → Type u)
    (Diam : ∀ {d n : ℕ}, Poly d n → ℕ → Prop)
    (general : ∃ C k : ℕ, ∀ d n : ℕ, ∀ P : Poly d n,
      Diam P (C * (n + d) ^ k)) :
    ∃ C k : ℕ, ∀ D : ℕ, ∀ Q : Poly D (2 * D),
      Diam Q (C * D ^ k) := by
  rcases general with ⟨C, k, hgeneral⟩
  refine ⟨C * 3 ^ k, k, ?_⟩
  intro D Q
  have h := hgeneral D (2 * D) Q
  have heq : C * (2 * D + D) ^ k = (C * 3 ^ k) * D ^ k := by
    rw [show 2 * D + D = 3 * D by omega, mul_pow]
    ac_rfl
  simpa only [heq] using h

end HirschReductionDraft
