import Solutions.PolynomialMinkowskiExposedEdges

open Set HirschMinkowski
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace HirschEnvelopeCrossing
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! From finite affine-envelope comparisons to an ENTIRE exposed edge.
The generic-objective theorem supplies the parallel-ties hypothesis after
indexing nonzero within-factor differences. No whole supporting slice or
nondegeneracy of the summed endpoints is assumed here. -/

private lemma displacement (e : E) (τ : E →ₗ[ℝ] ℝ) (hτ : τ e = 1)
    (x y : E) (h : x-y ∈ Submodule.span ℝ ({e} : Set E)) :
    x = y + (τ x-τ y) • e := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have hval := congrArg τ ha
  simp only [map_smul, map_sub, smul_eq_mul, hτ, mul_one] at hval
  have heq : (τ x-τ y) • e = x-y := by rw [← hval]; exact ha
  rw [heq]
  abel

private lemma interval_member (p e : E) (η z : ℝ)
    (hη : 0 ≤ η) (hz : 0 ≤ z) (hzη : z ≤ η) :
    p + z • e ∈ segment ℝ p (p + η • e) := by
  rw [← intervalLine_eq_segment p e η hη]
  exact ⟨z, hz, hzη, rfl⟩

/-- A common tie line and finite left/right maximizing comparisons determine
both endpoints of every ENTIRE support face, including stationary factors. -/
theorem crossing_support_segments
    (m : ℕ) (S : Fin m → Finset E) (p q : Fin m → E)
    (left wall right : E →ₗ[ℝ] ℝ) (e : E)
    (hle : left e < 0) (hre : 0 < right e)
    (hp : ∀ i, p i ∈ S i) (hq : ∀ i, q i ∈ S i)
    (hl : ∀ i, ∀ x∈S i, left x ≤ left (p i))
    (hr : ∀ i, ∀ x∈S i, right x ≤ right (q i))
    (hw : ∀ i, ∀ x∈S i, wall x ≤ wall (p i))
    (hwq : ∀ i, wall (q i) = wall (p i))
    (hparallel : ∀ i, ∀ x∈S i, wall x = wall (p i) →
      x-p i ∈ Submodule.span ℝ ({e} : Set E)) :
    ∃ η : Fin m → ℝ, (∀ i, 0 ≤ η i) ∧
      (∀ i, q i = p i + η i • e) ∧
      ∀ i, supportFace (convexHull ℝ (S i : Set E)) wall (wall (p i)) =
        intervalLine (p i) e (η i) := by
  classical
  let τ : E →ₗ[ℝ] ℝ := (left e)⁻¹ • left
  have hτ : τ e = 1 := by
    change (left e)⁻¹ * left e = 1
    exact inv_mul_cancel₀ (ne_of_lt hle)
  let η : Fin m → ℝ := fun i => τ (q i)-τ (p i)
  have hqe : ∀ i, q i = p i + η i • e := by
    intro i
    exact displacement e τ hτ _ _ (hparallel i (q i) (hq i) (hwq i))
  have hη : ∀ i, 0 ≤ η i := by
    intro i
    have hv := hl i (q i) (hq i)
    rw [hqe i, map_add, map_smul] at hv
    simp only [smul_eq_mul] at hv
    by_contra hn
    have hneg : η i < 0 := lt_of_not_ge hn
    have hpos := mul_pos_of_neg_of_neg hneg hle
    linarith
  refine ⟨η, hη, hqe, ?_⟩
  intro i
  rw [intervalLine_eq_segment (p i) e (η i) (hη i), ← hqe i]
  apply convexHull_supportFace_eq_segment (S i : Set E) wall (wall (p i))
    (p i) (q i) (hp i) (hq i) rfl (hwq i) (hw i)
  intro x hx hxw
  let z : ℝ := τ x-τ (p i)
  have hxe : x = p i + z • e :=
    displacement e τ hτ _ _ (hparallel i x hx hxw)
  have hz : 0 ≤ z := by
    have hv := hl i x hx
    rw [hxe, map_add, map_smul] at hv
    simp only [smul_eq_mul] at hv
    by_contra hn
    have hneg : z < 0 := lt_of_not_ge hn
    have hpos := mul_pos_of_neg_of_neg hneg hle
    linarith
  have hzη : z ≤ η i := by
    have hv := hr i x hx
    rw [hxe, hqe i, map_add, map_add, map_smul, map_smul] at hv
    simp only [smul_eq_mul] at hv
    by_contra hn
    have hlt : η i < z := lt_of_not_ge hn
    have hp := mul_lt_mul_of_pos_right hlt hre
    linarith
  rw [hxe, hqe i]
  exact interval_member (p i) e (η i) z (hη i) hz hzη

/-- At an affine-envelope event, actual finite maximizing data and the
no-independent-ties property imply an ordinary exposed edge of the sum.
The theorem derives component slices and nondegeneracy; neither is supplied. -/
theorem affine_crossing_exposed_edge
    (m : ℕ) (S : Fin m → Finset E) (p q : Fin m → E)
    (f g : E →ₗ[ℝ] ℝ) (s u t : ℝ) (c : Fin m)
    (hp : ∀ i, p i ∈ S i) (hq : ∀ i, q i ∈ S i)
    (hpq : p c ≠ q c)
    (hleft : ∀ i, ∀ x∈S i, x ≠ p i →
      (f + s • g) x < (f + s • g) (p i))
    (hright : ∀ i, ∀ x∈S i, x ≠ q i →
      (f + t • g) x < (f + t • g) (q i))
    (hwall : ∀ i, ∀ x∈S i, (f + u • g) x ≤ (f + u • g) (p i))
    (hwallq : ∀ i, (f + u • g) (q i) = (f + u • g) (p i))
    (hties : ∀ i, ∀ x∈S i, ∀ y∈S i, x ≠ y →
      (f + u • g) x = (f + u • g) y →
      ∀ j, ∀ v∈S j, ∀ w∈S j,
        (f + u • g) v = (f + u • g) w →
        v-w ∈ Submodule.span ℝ ({x-y} : Set E)) :
    (∀ z ∈ sumSet (fun i => convexHull ℝ (S i : Set E)),
      (f + u • g) z ≤ (f + u • g) (∑ i, p i)) ∧
    supportFace (sumSet (fun i => convexHull ℝ (S i : Set E)))
      (f + u • g) ((f + u • g) (∑ i, p i)) =
        segment ℝ (∑ i, p i) (∑ i, q i) ∧
    Hirsch.Adj (sumSet (fun i => convexHull ℝ (S i : Set E)))
      (∑ i, p i) (∑ i, q i) := by
  classical
  let e : E := q c-p c
  have he : e ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  have hl : (f + s • g) e < 0 := by
    have h := hleft c (q c) (hq c) (Ne.symm hpq)
    change (f + s • g) (q c-p c) < 0
    rw [map_sub]
    exact sub_neg.mpr h
  have hr : 0 < (f + t • g) e := by
    have h := hright c (p c) (hp c) hpq
    change 0 < (f + t • g) (q c-p c)
    rw [map_sub]
    exact sub_pos.mpr h
  have hln : ∀ i, ∀ x∈S i, (f + s • g) x ≤ (f + s • g) (p i) := by
    intro i x hx
    by_cases heq : x = p i
    · exact le_of_eq (congrArg (f + s • g) heq)
    · exact (hleft i x hx heq).le
  have hrn : ∀ i, ∀ x∈S i, (f + t • g) x ≤ (f + t • g) (q i) := by
    intro i x hx
    by_cases heq : x = q i
    · exact le_of_eq (congrArg (f + t • g) heq)
    · exact (hright i x hx heq).le
  have hpar : ∀ i, ∀ x∈S i, (f + u • g) x = (f + u • g) (p i) →
      x-p i ∈ Submodule.span ℝ ({e} : Set E) := by
    intro i x hx hxe
    exact hties c (q c) (hq c) (p c) (hp c) (Ne.symm hpq) (hwallq c)
      i x hx (p i) (hp i) hxe
  obtain ⟨η, hη, hqe, hface⟩ := crossing_support_segments m S p q
    (f + s • g) (f + u • g) (f + t • g) e hl hr hp hq hln hrn hwall hwallq hpar
  have hηc : η c = 1 := by
    have h := hqe c
    have hv := congrArg (f + s • g) h
    have hel : (f + s • g) (q c)-(f + s • g) (p c) = (f + s • g) e := by
      exact ((f + s • g).map_sub (q c) (p c)).symm
    simp only [map_add, map_smul, smul_eq_mul] at hv
    have hm : (η c-1) * (f + s • g) e = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (ne_of_lt hl))
  have hsumpos : 0 < ∑ i, η i := by
    have hle := Finset.single_le_sum (fun i _ => hη i) (Finset.mem_univ c)
    rw [hηc] at hle
    linarith
  have hsum : (∑ i, q i) = (∑ i, p i)+(∑ i, η i) • e := by
    simp only [hqe, Finset.sum_add_distrib, Finset.sum_smul]
  have hne : (∑ i, p i) ≠ (∑ i, p i)+(∑ i, η i) • e := by
    intro h
    have hv := congrArg (f + s • g) h
    simp only [map_add, map_smul, smul_eq_mul] at hv
    have hneg := mul_neg_of_pos_of_neg hsumpos hl
    linarith
  have hb : ∀ i, ∀ x∈convexHull ℝ (S i : Set E),
      (f + u • g) x ≤ (f + u • g) (p i) := by
    intro i x hx
    exact (convexHull_support_contained (S i : Set E) Set.univ
      (f + u • g) ((f + u • g) (p i)) convex_univ
      (fun z hz => ⟨hwall i z hz, fun _ => Set.mem_univ _⟩) x hx).1
  have hglobal : ∀ z ∈ sumSet (fun i => convexHull ℝ (S i : Set E)),
      (f + u • g) z ≤ (f + u • g) (∑ i, p i) := by
    intro z hz
    simpa only [map_sum] using
      sumSet_support_bound (fun i => convexHull ℝ (S i : Set E))
        (f + u • g) (fun i => (f + u • g) (p i)) hb z hz
  have hglobalface : supportFace (sumSet (fun i => convexHull ℝ (S i : Set E)))
      (f + u • g) ((f + u • g) (∑ i, p i)) =
        segment ℝ (∑ i, p i) (∑ i, q i) := by
    rw [map_sum, sumSet_supportFace _ _ _ hb]
    have hf : (fun i => supportFace (convexHull ℝ (S i : Set E))
        (f + u • g) ((f + u • g) (p i))) =
        (fun i => intervalLine (p i) e (η i)) := funext hface
    rw [hf, sumSet_intervalLine p e η hη, hsum]
    exact intervalLine_eq_segment _ _ _ (Finset.sum_nonneg (fun i _ => hη i))
  refine ⟨hglobal, hglobalface, ?_⟩
  apply adj_of_supportFace_eq_segment _ (f + u • g) _ _ _
    (by simpa only [hsum] using hne) hglobal hglobalface

#print axioms crossing_support_segments
#print axioms affine_crossing_exposed_edge
end HirschEnvelopeCrossing
