import Solutions.PolynomialPairedBasisRouting

/-!
# Coupled boxes with nonnegative feedback

One checkable vector w>0, Cw<w replaces exponentially many complementary-basis
checks. No acyclicity, small row sum, projective separator, recursive diameter
input, or small-excess theorem is assumed. New source awaits Lean verification.
-/
open Set Hirsch HirschPairedBases
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschPositiveBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A weighted maximum principle. This is the nonsingular M-matrix argument
in elementary ordered-linear form; it is not claimed as new classical theory. -/
theorem nonpos_of_le_positive_map
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (z : Vec ι) (hz : z ≤ C z) : z ≤ 0 := by
  classical
  by_contra hn
  have hn' : ¬ ∀ i, z i≤0 := hn
  push_neg at hn'
  obtain ⟨i,hi⟩ := hn'
  obtain ⟨j,_hj,hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset ι) (fun k => z k/w k) ⟨i,Finset.mem_univ i⟩
  let t : ℝ := z j/w j
  have ht : 0<t := (div_pos hi (hw i)).trans_le (hmax i (Finset.mem_univ i))
  have hbound : z ≤ t•w := by
    intro k
    change z k≤t*w k
    apply (div_le_iff₀ (hw k)).mp
    exact hmax k (Finset.mem_univ k)
  have hC := hmono hbound j
  have hstrict := mul_lt_mul_of_pos_left (hcw j) ht
  have he : t*w j=z j := div_mul_cancel₀ _ (ne_of_gt (hw j))
  simp only [map_smul,Pi.smul_apply,smul_eq_mul] at hC
  have hzj := hz j
  linarith

lemma nonneg_of_id_sub_nonneg
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (z : Vec ι) (hz : 0 ≤ (LinearMap.id-C) z) : 0 ≤ z := by
  have hn : -z ≤ C (-z) := by
    intro i
    have hi := hz i
    change 0≤z i-C z i at hi
    simp only [map_neg,Pi.neg_apply]
    linarith
  have h := nonpos_of_le_positive_map C hmono w hw hcw (-z) hn
  intro i
  have hi := h i
  change -z i≤0 at hi
  linarith

lemma id_sub_injective
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i) :
    Function.Injective (LinearMap.id-C) := by
  intro x y hxy
  have hz : (LinearMap.id-C) (x-y)=0 := by
    rw [map_sub,hxy,sub_self]
  have hp := nonneg_of_id_sub_nonneg C hmono w hw hcw (x-y) (by rw [hz])
  have hm := nonneg_of_id_sub_nonneg C hmono w hw hcw (-(x-y))
    (by rw [map_neg,hz,neg_zero])
  funext i
  have hpi := hp i
  have hmi := hm i
  change 0≤x i-y i at hpi
  change 0≤-(x i-y i) at hmi
  linarith

def inverseBasis
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i) :
    Vec ι ≃ₗ[ℝ] Vec ι :=
  LinearEquiv.ofBijective (LinearMap.id-C)
    ⟨id_sub_injective C hmono w hw hcw,
      LinearMap.surjective_of_injective (id_sub_injective C hmono w hw hcw)⟩

def maskMap (s : ι → Bool) : Vec ι →ₗ[ℝ] Vec ι where
  toFun x i := if s i then x i else 0
  map_add' x y := by funext i; cases s i <;> simp
  map_smul' a x := by funext i; cases s i <;> simp

lemma masked_monotone (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C) (s : ι → Bool) :
    Monotone ((maskMap s).comp C) := by
  intro x y hxy i
  change (if s i then C x i else 0) ≤ (if s i then C y i else 0)
  cases s i
  · exact le_rfl
  · exact hmono hxy i

lemma masked_weight (C : Vec ι →ₗ[ℝ] Vec ι)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i) (s : ι → Bool) :
    ∀ i, ((maskMap s).comp C) w i<w i := by
  intro i
  change (if s i then C w i else 0)<w i
  cases s i
  · exact hw i
  · exact hcw i

/-- ALL complementary bases, positive solutions and disjoint pairs follow
from the single weighted positivity witness. -/
def positiveFeedbackModel
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (b : Vec ι) (hb : ∀ i, 0<b i) : PairedBasisModel (LinearMap.id-C) b := by
  let basis := fun s => inverseBasis ((maskMap s).comp C)
    (masked_monotone C hmono s) w hw (masked_weight C w hw hcw s)
  have hspec : ∀ s x i, basis s x i = if s i then (LinearMap.id-C) x i else x i := by
    intro s x i
    change x i-(if s i then C x i else 0)=_
    cases s i <;> simp
  refine ⟨basis,hspec,?_,?_⟩
  · intro s
    let x := (basis s).symm (rhs b s)
    have he : (LinearMap.id-(maskMap s).comp C) x=rhs b s :=
      (basis s).apply_symm_apply _
    have hnonneg : 0≤x := by
      apply nonneg_of_id_sub_nonneg ((maskMap s).comp C)
        (masked_monotone C hmono s) w hw (masked_weight C w hw hcw s) x
      rw [he]
      intro i
      simp only [rhs]
      cases s i
      · exact le_rfl
      · exact (hb i).le
    have hCx : 0≤C x := by simpa only [map_zero] using hmono hnonneg
    refine ⟨hnonneg,?_⟩
    intro i
    have hei := congrFun he i
    change x i-(if s i then C x i else 0)=rhs b s i at hei
    change x i-C x i≤b i
    cases hs : s i
    · have hx0 : x i=0 := by simpa [hs,rhs] using hei
      have hc := hCx i
      rw [hx0]
      linarith [hb i]
    · have hxtop : x i-C x i=b i := by simpa [hs,rhs] using hei
      exact hxtop.le
  · intro x hx i hxi
    have hCx : 0≤C x := by simpa only [map_zero] using hmono hx.1
    change x i-C x i<b i
    rw [hxi]
    have hci := hCx i
    linarith [hb i]

/-- Direct ordinary-edge diameter theorem; no recursive geometric input. -/
theorem positive_feedback_diamLE {d : ℕ}
    (C : Vec (Fin d) →ₗ[ℝ] Vec (Fin d)) (hmono : Monotone C)
    (w : Vec (Fin d)) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (b : Vec (Fin d)) (hb : ∀ i, 0<b i) :
    DiamLE (pairedPoly (LinearMap.id-C) b) d :=
  paired_basis_diamLE (positiveFeedbackModel C hmono w hw hcw b hb)

/-- The all-upper solution is a coordinatewise upper bound for the entire
polytope, not just for its vertices. -/
theorem positive_feedback_le_top
    (C : Vec ι →ₗ[ℝ] Vec ι) (hmono : Monotone C)
    (w : Vec ι) (hw : ∀ i, 0<w i) (hcw : ∀ i, C w i<w i)
    (b : Vec ι) (hb : ∀ i, 0<b i)
    (x : Vec ι) (hx : x ∈ pairedPoly (LinearMap.id-C) b) :
    x ≤ (positiveFeedbackModel C hmono w hw hcw b hb).point (fun _ => true) := by
  let m := positiveFeedbackModel C hmono w hw hcw b hb
  let v := m.point (fun _ => true)
  have hz : x-v ≤ C (x-v) := by
    intro i
    have hv := m.point_upper (fun _ => true) i rfl
    have hx' := hx.2 i
    change v i-C v i=b i at hv
    change x i-C x i≤b i at hx'
    simp only [map_sub,Pi.sub_apply]
    linarith
  have h := nonpos_of_le_positive_map C hmono w hw hcw (x-v) hz
  intro i
  have hi := h i
  change x i-v i≤0 at hi
  exact sub_nonpos.mp hi

def matrixMap (C : ι → ι → ℝ) : Vec ι →ₗ[ℝ] Vec ι where
  toFun x i := ∑ j, C i j*x j
  map_add' x y := by funext i; simp [mul_add,Finset.sum_add_distrib]
  map_smul' a x := by funext i; simp [Finset.mul_sum,mul_assoc,mul_left_comm]

lemma matrixMap_monotone (C : ι → ι → ℝ) (hC : ∀ i j, 0≤C i j) :
    Monotone (matrixMap C) := by
  intro x y hxy i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hC i j))

/-- Explicit finite matrix criterion consumed by the rational checker. -/
theorem matrix_positive_feedback_diamLE {d : ℕ}
    (C : Fin d → Fin d → ℝ) (hC : ∀ i j, 0≤C i j)
    (b w : Fin d → ℝ) (hb : ∀ i, 0<b i) (hw : ∀ i, 0<w i)
    (hcw : ∀ i, (∑ j, C i j*w j)<w i) :
    DiamLE {x : Fin d → ℝ | (∀ i, 0≤x i) ∧ ∀ i, x i≤b i+∑ j, C i j*x j} d := by
  have h := positive_feedback_diamLE (matrixMap C) (matrixMap_monotone C hC) w hw hcw b hb
  have he : pairedPoly (LinearMap.id-matrixMap C) b =
      {x : Fin d → ℝ | (∀ i, 0≤x i) ∧ ∀ i, x i≤b i+∑ j, C i j*x j} := by
    ext x
    simp only [pairedPoly,Set.mem_setOf_eq]
    constructor <;> rintro ⟨hx,hbnd⟩ <;> refine ⟨hx,?_⟩ <;> intro i
    · have hi := hbnd i
      change x i-(∑ j, C i j*x j)≤b i at hi
      linarith
    · have hi := hbnd i
      change x i-(∑ j, C i j*x j)≤b i
      linarith
  rwa [he] at h

#print axioms nonpos_of_le_positive_map
#print axioms id_sub_injective
#print axioms positive_feedback_diamLE
#print axioms positive_feedback_le_top
#print axioms matrix_positive_feedback_diamLE
end HirschPositiveBoxes
