import Mathlib
import Definitions.Def_Hirsch_model

/-! Finite geometric certificates for recursive projective product routing.
Only geometric data appear in constructors; no graph-distance premise occurs.
Each proper split uses every row and every coordinate exactly once. -/
open Set Hirsch
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
noncomputable section
namespace HirschRecursiveProducts

/-- A finite geometry certificate, not a diameter hypothesis. Proper positive-
dimensional factors prevent a split from merely restating the same instance.
Affine steps cover translations/recentering without changing n or d. -/
inductive ProductTree : {d n : ℕ} →
    (Fin n → EuclideanSpace ℝ (Fin d)) → (Fin n → ℝ) → Prop
  | leaf {d n : ℕ}
      {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
      (hbd : Bornology.IsBounded (Hpoly a b)) (hcount : n ≤ d + 3) :
      ProductTree a b
  | affine {d n : ℕ}
      {a a' : Fin n → EuclideanSpace ℝ (Fin d)} {b b' : Fin n → ℝ}
      (f : EuclideanSpace ℝ (Fin d) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin d))
      (himage : f '' Hpoly a b = Hpoly a' b')
      (prior : ProductTree a b) : ProductTree a' b'
  | split {d n k : ℕ}
      (dims counts : Fin k → ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
      (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
        (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
      (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
      (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
      (hrows : ∀ z i j, ⟪a (e ⟨i,j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
      (hcount : ∀ i, dims i ≤ counts i)
      (hk : 2 ≤ k) (hdim : ∀ i, 0 < dims i)
      (c : EuclideanSpace ℝ (Fin d))
      (hsource : ∀ x ∈ Hpoly a b, 0 < 1 + ⟪c, x⟫)
      (htarget : ∀ y ∈ Hpoly (fun i => a i + b i • c) b, 0 < 1 + -⟪c, y⟫)
      (children : ∀ i, ProductTree (A i) (fun j => b (e ⟨i,j⟩))) :
      ProductTree (fun i => a i + b i • c) b

end HirschRecursiveProducts
