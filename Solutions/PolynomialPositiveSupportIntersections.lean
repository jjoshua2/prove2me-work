import Solutions.PolynomialMinkowskiExposedEdges

/-!
# Positive supporting combinations identify the WHOLE base face

This is the geometric bridge used by the implicit-H Minkowski route lift.
A positive combination of valid inequalities exposes exactly their common
maximum slice. Interior objective interpolation intersects the exposed faces.
Thus interpolation between two consecutive edge normals keeps the intervening
base vertex, while each corner exposes the actual base edge.

NEW UNCOMPILED candidates. The rational rank/edge-normal constructor and the
normal-fan refinement existence arguments remain in the accompanying proof.
-/
open Set HirschMinkowski
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschSupportInterpolation
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Equality in a positively weighted sum of upper bounds is termwise equality.
The index set contains just the rows with positive coefficients. -/
theorem weighted_support_eq_iff
    (P : Set E) (a : ι → E →ₗ[ℝ] ℝ) (b w : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hb : ∀ i, ∀ x ∈ P, a i x ≤ b i)
    (x : E) (hx : x ∈ P) :
    (∑ i, w i * a i x) = (∑ i, w i * b i) ↔ ∀ i, a i x = b i := by
  classical
  constructor
  · intro he i
    by_contra hn
    have hi : a i x < b i := lt_of_le_of_ne (hb i x hx) hn
    have hs : (∑ j, w j * a j x) < ∑ j, w j * b j := by
      apply Finset.sum_lt_sum
      · intro j _
        exact mul_le_mul_of_nonneg_left (hb j x hx) (hw j).le
      · exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hw i)⟩
    linarith
  · intro h
    exact Finset.sum_congr rfl (fun i _ => by rw [h i])

/-- This is exact exposed-face equality, not merely a direction certificate. -/
theorem positive_sum_supportFace
    (P : Set E) (a : ι → E →ₗ[ℝ] ℝ) (b w : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hb : ∀ i, ∀ x ∈ P, a i x ≤ b i) :
    supportFace P (∑ i, w i • a i) (∑ i, w i*b i) =
      {x | x ∈ P ∧ ∀ i, a i x = b i} := by
  ext x
  simp only [supportFace, Set.mem_setOf_eq, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hx, (weighted_support_eq_iff P a b w hw hb x hx).mp he⟩
  · rintro ⟨hx, he⟩
    exact ⟨hx, (weighted_support_eq_iff P a b w hw hb x hx).mpr he⟩

/-- The scalar form handles arbitrary strict interpolation coefficients. -/
theorem strict_convex_top_iff (a b A B t : ℝ)
    (ha : a ≤ A) (hb : b ≤ B) (ht : 0 < t) (ht1 : t < 1) :
    (1-t)*a+t*b = (1-t)*A+t*B ↔ a=A ∧ b=B := by
  constructor
  · intro he
    have h₁ : 0 ≤ (1-t)*(A-a) := mul_nonneg (by linarith) (by linarith)
    have h₂ : 0 ≤ t*(B-b) := mul_nonneg ht.le (by linarith)
    have hz₁ : (1-t)*(A-a)=0 := by nlinarith
    have hz₂ : t*(B-b)=0 := by nlinarith
    constructor
    · have h := (mul_eq_zero.mp hz₁).resolve_left (by linarith : 1-t≠0)
      linarith
    · have h := (mul_eq_zero.mp hz₂).resolve_left (ne_of_gt ht)
      linarith
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Interior objective interpolation exposes the intersection of the two
endpoint slices. In the lift, two incident distinct edges intersect at one
actual vertex, so no unlisted parent graph transition can occur here. -/
theorem interpolated_supportFace
    (P : Set E) (f g : E →ₗ[ℝ] ℝ) (A B t : ℝ)
    (hf : ∀ x ∈ P, f x ≤ A) (hg : ∀ x ∈ P, g x ≤ B)
    (ht : 0 < t) (ht1 : t < 1) :
    supportFace P ((1-t) • f+t • g) ((1-t)*A+t*B) =
      supportFace P f A ∩ supportFace P g B := by
  ext x
  simp only [supportFace, Set.mem_setOf_eq, Set.mem_inter_iff,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨hx, he⟩
    obtain ⟨ha,hb⟩ := (strict_convex_top_iff (f x) (g x) A B t
      (hf x hx) (hg x hx) ht ht1).mp he
    exact ⟨⟨hx,ha⟩,⟨hx,hb⟩⟩
  · rintro ⟨⟨hx,ha⟩,⟨_,hb⟩⟩
    exact ⟨hx, (strict_convex_top_iff (f x) (g x) A B t
      (hf x hx) (hg x hx) ht ht1).mpr ⟨ha,hb⟩⟩

#print axioms weighted_support_eq_iff
#print axioms positive_sum_supportFace
#print axioms strict_convex_top_iff
#print axioms interpolated_supportFace
end HirschSupportInterpolation
