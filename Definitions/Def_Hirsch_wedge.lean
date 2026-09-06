import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open WithLp EuclideanSpace

namespace Hirsch

/-- Concatenate a last coordinate onto a vector in $\mathbb{R}^d$. -/
noncomputable def embed {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  toLp 2 (Fin.snoc (ofLp x) t)

/-- Drop the last coordinate. -/
noncomputable def proj {d : ℕ} (z : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin d) :=
  toLp 2 (Fin.init (ofLp z))

/-- Outward normals of the Klee--Walkup wedge of an H-polytope over inequality `i0`.
The first `n` normals are the original normals with last coordinate `1` on the foot
and `0` otherwise; the last normal is $-e_{d+1}$, cutting out $t\ge 0$. -/
noncomputable def wedgeA {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (i0 : Fin n) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)) :=
  Fin.snoc (fun i => embed (a i) (if i = i0 then (1 : ℝ) else 0)) (embed 0 (-1))

/-- Right-hand sides of the Klee--Walkup wedge: the original bounds, plus $0$ for $t\ge 0$. -/
noncomputable def wedgeB {n : ℕ} (b : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc b 0

/-- The wedge over `i0`, with inequality `i1` tilted by `ε` in the new coordinate.

This is the polar of Santos' one-point-suspension-plus-perturbation
(Annals of Mathematics 176 (2012), Theorem 2.6 / Figure 3; cf. Holt,
arXiv:1311.0581, §3.1). -/
noncomputable def perturbWedgeA {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (i0 i1 : Fin n) (ε : ℝ) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)) :=
  fun j => if j = i1.castSucc then embed (a i1) ε else wedgeA a i0 j

end Hirsch
