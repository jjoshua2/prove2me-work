import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open WithLp

namespace Hirsch

/-- Coordinate vector in $\mathbb{R}^5$. -/
noncomputable def vec5 (x0 x1 x2 x3 x4 : ℝ) : EuclideanSpace ℝ (Fin 5) :=
  EuclideanSpace.single (0 : Fin 5) x0 + EuclideanSpace.single 1 x1 +
    EuclideanSpace.single 2 x2 + EuclideanSpace.single 3 x3 +
    EuclideanSpace.single 4 x4

/-- The 28 vertices of the Matschke--Santos--Weibel prismatoid $Q_{28}$
(arXiv:1202.4701, Corollary 2.9), used as outward normals of the polar. -/
noncomputable def q28A (i : Fin 28) : EuclideanSpace ℝ (Fin 5) :=
  match i.val with
  | 0 => vec5 18 0 0 0 1
  | 1 => vec5 (-18) 0 0 0 1
  | 2 => vec5 0 0 30 0 1
  | 3 => vec5 0 0 (-30) 0 1
  | 4 => vec5 0 0 0 30 1
  | 5 => vec5 0 0 0 (-30) 1
  | 6 => vec5 0 5 0 25 1
  | 7 => vec5 0 5 0 (-25) 1
  | 8 => vec5 0 (-5) 0 25 1
  | 9 => vec5 0 (-5) 0 (-25) 1
  | 10 => vec5 0 0 18 18 1
  | 11 => vec5 0 0 18 (-18) 1
  | 12 => vec5 0 0 (-18) 18 1
  | 13 => vec5 0 0 (-18) (-18) 1
  | 14 => vec5 0 0 18 0 (-1)
  | 15 => vec5 0 0 (-18) 0 (-1)
  | 16 => vec5 0 30 0 0 (-1)
  | 17 => vec5 0 (-30) 0 0 (-1)
  | 18 => vec5 30 0 0 0 (-1)
  | 19 => vec5 (-30) 0 0 0 (-1)
  | 20 => vec5 25 0 0 5 (-1)
  | 21 => vec5 25 0 0 (-5) (-1)
  | 22 => vec5 (-25) 0 0 5 (-1)
  | 23 => vec5 (-25) 0 0 (-5) (-1)
  | 24 => vec5 18 18 0 0 (-1)
  | 25 => vec5 18 (-18) 0 0 (-1)
  | 26 => vec5 (-18) 18 0 0 (-1)
  | _ => vec5 (-18) (-18) 0 0 (-1)

noncomputable def q28B : Fin 28 → ℝ := fun _ => 1

/-- Apex corresponding to the base $x_5=1$. -/
noncomputable def q28U : EuclideanSpace ℝ (Fin 5) := EuclideanSpace.single 4 (1 : ℝ)

/-- Apex corresponding to the base $x_5=-1$. -/
noncomputable def q28V : EuclideanSpace ℝ (Fin 5) := EuclideanSpace.single 4 (-1 : ℝ)

end Hirsch
