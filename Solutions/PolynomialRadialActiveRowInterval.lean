import Mathlib
import Solutions.PolynomialRadialRetraction

/-!
# Convexity of radial active-row cells

For a fixed strict radial centre, each normalized row score is affine in the
ambient point.  A row is active when its score attains the finite radial scale,
which is the maximum of all row scores and the constant one.  Therefore the set
where one fixed row is active is convex.

Along any segment, if the same row is active at both endpoints then it remains
active throughout the segment.  Its radial image consequently stays on that
same final cut face.  This is the direct one-dimensional upper-envelope
structure needed to reason about the chronological cut sequence on an
endpoint-lift spoke; it is stronger than merely simplifying a region graph to
a duplicate-free label path.
-/

open scoped RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace HirschRadial

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A normalized row score respects affine combinations whose coefficients sum
to one. -/
theorem normalizedRow_affine_combo
    (a : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (o x y : EuclideanSpace ℝ (Fin d))
    (s t : ℝ) (hst : s + t = 1) :
    normalizedRow a b o (s • x + t • y) =
      s * normalizedRow a b o x + t * normalizedRow a b o y := by
  unfold normalizedRow
  simp only [inner_add_right, inner_smul_right]
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  have hnum :
      s * ⟪a, x⟫ + t * ⟪a, y⟫ - ⟪a, o⟫ =
        s * (⟪a, x⟫ - ⟪a, o⟫) + t * (⟪a, y⟫ - ⟪a, o⟫) := by
    calc
      s * ⟪a, x⟫ + t * ⟪a, y⟫ - ⟪a, o⟫ =
          s * ⟪a, x⟫ + t * ⟪a, y⟫ - (s + t) * ⟪a, o⟫ := by
            rw [hst, one_mul]
      _ = s * (⟪a, x⟫ - ⟪a, o⟫) +
          t * (⟪a, y⟫ - ⟪a, o⟫) := by ring
  exact congrArg (fun r : ℝ => r / (b - ⟪a, o⟫)) hnum

/-- If one row attains the radial scale at two points, then it attains the scale
at every convex combination of those points. -/
theorem scale_eq_row_on_combo_of_endpoints
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x y : EuclideanSpace ℝ (Fin d)) (i : ι)
    (hx : scale (fun j => normalizedRow (a j) (b j) o x) =
      normalizedRow (a i) (b i) o x)
    (hy : scale (fun j => normalizedRow (a j) (b j) o y) =
      normalizedRow (a i) (b i) o y)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    scale (fun j => normalizedRow (a j) (b j) o (s • x + t • y)) =
      normalizedRow (a i) (b i) o (s • x + t • y) := by
  let rx : ι → ℝ := fun j => normalizedRow (a j) (b j) o x
  let ry : ι → ℝ := fun j => normalizedRow (a j) (b j) o y
  let z := s • x + t • y
  have hix1 : 1 ≤ rx i := by
    dsimp [rx]
    rw [← hx]
    exact one_le_scale _
  have hiy1 : 1 ≤ ry i := by
    dsimp [ry]
    rw [← hy]
    exact one_le_scale _
  have hrow : ∀ j,
      normalizedRow (a j) (b j) o z ≤ normalizedRow (a i) (b i) o z := by
    intro j
    have hxj : rx j ≤ rx i := by
      calc
        rx j ≤ scale rx := le_scale rx j
        _ = rx i := by simpa [rx] using hx
    have hyj : ry j ≤ ry i := by
      calc
        ry j ≤ scale ry := le_scale ry j
        _ = ry i := by simpa [ry] using hy
    rw [normalizedRow_affine_combo (a j) (b j) o x y s t hst,
      normalizedRow_affine_combo (a i) (b i) o x y s t hst]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hxj hs)
      (mul_le_mul_of_nonneg_left hyj ht)
  have hone : 1 ≤ normalizedRow (a i) (b i) o z := by
    rw [normalizedRow_affine_combo (a i) (b i) o x y s t hst]
    calc
      1 = s * 1 + t * 1 := by rw [← add_mul, hst, one_mul]
      _ ≤ s * rx i + t * ry i :=
        add_le_add
          (mul_le_mul_of_nonneg_left hix1 hs)
          (mul_le_mul_of_nonneg_left hiy1 ht)
      _ = s * normalizedRow (a i) (b i) o x +
          t * normalizedRow (a i) (b i) o y := by rfl
  apply le_antisymm
  · exact scale_le _ hone hrow
  · exact le_scale
      (fun j => normalizedRow (a j) (b j) o (s • x + t • y)) i

/-- The cell on which one fixed row attains the radial maximum. -/
def activeRowCell
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (i : ι) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | scale (fun j => normalizedRow (a j) (b j) o x) =
    normalizedRow (a i) (b i) o x}

/-- Every active-row cell is convex.  Equivalently on a line, one row cannot
leave the upper envelope and later re-enter it. -/
theorem activeRowCell_convex
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (i : ι) :
    Convex ℝ (activeRowCell a b o i) := by
  intro x hx y hy s t hs ht hst
  exact scale_eq_row_on_combo_of_endpoints a b o x y i hx hy s t hs ht hst

/-- An active row cuts the radial image exactly on its final supporting
hyperplane. -/
theorem retract_mem_active_cut_of_mem_activeRowCell
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x : EuclideanSpace ℝ (Fin d)) (i : ι)
    (hstrict : ⟪a i, o⟫ < b i)
    (hx : x ∈ activeRowCell a b o i) :
    ⟪a i, retract a b o x⟫ = b i := by
  change ⟪a i,
    point o x (scale (fun j => normalizedRow (a j) (b j) o x))⟫ = b i
  exact point_mem_active_final_face (row (a i)) (b i) o x hstrict
    (one_le_scale _) hx

/-- Segment form: if the same row is active at both segment endpoints, the
entire radial image of that segment stays on that row's final cut face. -/
theorem retract_image_segment_subset_active_cut
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (o x y : EuclideanSpace ℝ (Fin d)) (i : ι)
    (hstrict : ⟪a i, o⟫ < b i)
    (hx : x ∈ activeRowCell a b o i)
    (hy : y ∈ activeRowCell a b o i) :
    retract a b o '' segment ℝ x y ⊆
      {z | ⟪a i, z⟫ = b i} := by
  rintro z ⟨w, hw, rfl⟩
  have hcell : w ∈ activeRowCell a b o i :=
    (activeRowCell_convex a b o i).segment_subset hx hy hw
  exact retract_mem_active_cut_of_mem_activeRowCell a b o w i hstrict hcell

#print axioms normalizedRow_affine_combo
#print axioms scale_eq_row_on_combo_of_endpoints
#print axioms activeRowCell_convex
#print axioms retract_mem_active_cut_of_mem_activeRowCell
#print axioms retract_image_segment_subset_active_cut

end HirschRadial
