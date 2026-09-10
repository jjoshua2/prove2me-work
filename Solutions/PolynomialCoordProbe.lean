import Mathlib
import Solutions.PolynomialCommonFace

open scoped RealInnerProductSpace InnerProduct
open Set Hirsch

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}
variable (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
variable (u x : EuclideanSpace ℝ (Fin d))

local notation "W" => commonDirection a b u x
local notation "D" => Module.finrank ℝ W

#check stdOrthonormalBasis
#check (stdOrthonormalBasis ℝ W).repr
#check (stdOrthonormalBasis ℝ W).repr.symm
#check W.subtypeₗᵢ
#check W.subtypeL
#check LinearIsometry.toContinuousLinearMap
#check LinearIsometryEquiv.toContinuousLinearEquiv
#check ContinuousLinearMap.adjoint
#check ContinuousLinearMap.adjoint_inner_right
#check ContinuousLinearMap.adjoint_inner_left

noncomputable def probeLift : EuclideanSpace ℝ (Fin D) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  W.subtypeₗᵢ.comp (stdOrthonormalBasis ℝ W).repr.symm.toLinearIsometry

#check probeLift
#check (probeLift a b u x).toContinuousLinearMap
#check (ContinuousLinearMap.adjoint (probeLift a b u x).toContinuousLinearMap)

end HirschPolynomialAccess
