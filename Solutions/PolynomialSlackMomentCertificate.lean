import Solutions.PolynomialAffineDiameterTransport
import Solutions.PolynomialExcessTwoDiameter

/-!
# Exact positive-slack certificates for two-moment normalization

The essential hypotheses are algebraic: an injective weighted row map, two
annihilating moments, and codimension two. No diameter bound is a hypothesis.
Existence of the positive normal relation for every bounded H-presentation is
not proved here. The exact image equality, unlike mere inclusion, justifies
transport of vertices, edges, and intrinsic row-support-face diameters.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschExcessTwo Module Submodule

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HirschSlackMoment

/-- The mass and moment linear map on slack coordinates. -/
def momentMap {n : ℕ} (t : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (ℝ × ℝ) where
  toFun s := (∑ i, s i, ∑ i, t i * s i)
  map_add' x y := by
    apply Prod.ext
    · change (∑ i, (x i + y i)) = (∑ i, x i) + ∑ i, y i
      simp only [Finset.sum_add_distrib]
    · change (∑ i, t i * (x i + y i)) =
        (∑ i, t i * x i) + ∑ i, t i * y i
      simp only [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    apply Prod.ext
    · change (∑ i, r * x i) = r * ∑ i, x i
      exact (Finset.mul_sum _ _ _).symm
    · change (∑ i, t i * (r * x i)) = r * ∑ i, t i * x i
      calc
        _ = ∑ i, r * (t i * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := (Finset.mul_sum _ _ _).symm

@[simp] lemma momentMap_apply {n : ℕ}
    (t : Fin n → ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    momentMap t s = (∑ i, s i, ∑ i, t i * s i) := rfl

lemma momentMap_singleton {n : ℕ} (t : Fin n → ℝ) (i : Fin n) :
    momentMap t (singletonPoint i) = (1, t i) := by
  have h := singletonPoint_mem t (t i) i rfl
  exact Prod.ext h.2.1 h.2.2

/-- Two different slopes make the two moment equations independent. -/
theorem momentMap_surjective {n : ℕ}
    (t : Fin n → ℝ) (ht : ∃ i j, t i ≠ t j) :
    Function.Surjective (momentMap t) := by
  obtain ⟨i, j, hij⟩ := ht
  have hden : t j - t i ≠ 0 := sub_ne_zero.mpr hij.symm
  rintro ⟨u, v⟩
  let A : ℝ := (t j * u - v) / (t j - t i)
  let B : ℝ := (v - t i * u) / (t j - t i)
  refine ⟨A • singletonPoint i + B • singletonPoint j, ?_⟩
  rw [map_add, map_smul, map_smul, momentMap_singleton, momentMap_singleton]
  apply Prod.ext
  · change A * 1 + B * 1 = u
    dsimp [A, B]
    field_simp [hden]
    ring
  · change A * t i + B * t j = v
    dsimp [A, B]
    field_simp [hden]
    ring

/-- Codimension, injectivity, and annihilation certify the WHOLE kernel. -/
theorem range_eq_moment_kernel_of_codimension_two {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : Fin n → ℝ) (hn : n = d + 2)
    (hL : Function.Injective L) (ht : ∃ i j, t i ≠ t j)
    (hzero : ∀ x, momentMap t (L x) = 0) :
    L.range = (momentMap t).ker := by
  have hsub : L.range ≤ (momentMap t).ker := by
    rintro y ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (hzero x)
  have hdimL : Module.finrank ℝ L.range = d := by
    have h := L.finrank_range_add_finrank_ker
    rw [LinearMap.ker_eq_bot.mpr hL, finrank_bot, add_zero] at h
    simpa only [finrank_euclideanSpace_fin] using h
  have hdimM : Module.finrank ℝ (momentMap t).range = 2 := by
    rw [LinearMap.range_eq_top.mpr (momentMap_surjective t ht)]
    simp
  have hdimK : Module.finrank ℝ (momentMap t).ker = d := by
    have h := (momentMap t).finrank_range_add_finrank_ker
    rw [hdimM, finrank_euclideanSpace_fin] at h
    omega
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [hdimL, hdimK]

/-- Affine offset minus the weighted row map. -/
def slackMap {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
  AffineMap.const ℝ (EuclideanSpace ℝ (Fin d)) v - L.toAffineMap

@[simp] lemma slackMap_apply {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin d)) :
    slackMap L v x = v - L x := rfl

/-- The feasible set described by nonnegative affine slacks. -/
def slackPoly {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, 0 ≤ (slackMap L v x) i}

theorem slackMap_injective {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (hL : Function.Injective L) :
    Function.Injective (slackMap L v) := by
  intro x y h
  apply hL
  have h' := congrArg (fun z => v - z) h
  simpa only [slackMap_apply, sub_sub_cancel] using h'

/-- Exact image, including every feasible point of the target moment slice. -/
theorem slackMap_image_eq_momentSlice {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) (mu : ℝ)
    (hrange : L.range = (momentMap t).ker)
    (hv : momentMap t v = (1, mu)) :
    slackMap L v '' slackPoly L v = momentSlice t mu := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hLx : momentMap t (L x) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← hrange]
      exact ⟨x, rfl⟩
    have hm : momentMap t (slackMap L v x) = (1, mu) := by
      rw [slackMap_apply, map_sub, hLx, sub_zero, hv]
    exact ⟨hx, congrArg Prod.fst hm, congrArg Prod.snd hm⟩
  · intro hs
    have hm : momentMap t s = (1, mu) := Prod.ext hs.2.1 hs.2.2
    have hz : v - s ∈ L.range := by
      rw [hrange]
      apply LinearMap.mem_ker.mpr
      rw [map_sub, hv, hm, sub_self]
    obtain ⟨x, hx⟩ := hz
    have hfx : slackMap L v x = s := by
      rw [slackMap_apply, hx]
      abel
    refine ⟨x, ?_, hfx⟩
    intro i
    rw [hfx]
    exact hs.1 i

/-- Exact affine slack certificates transfer diameter two, without assuming
any local or global diameter bound. -/
theorem slackPoly_diamLE_two {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) (mu : ℝ)
    (hL : Function.Injective L) (hrange : L.range = (momentMap t).ker)
    (hv : momentMap t v = (1, mu)) : DiamLE (slackPoly L v) 2 := by
  apply (Hirsch.affineMap_diamLE_image_iff_of_injective
    (slackMap L v) (slackMap_injective L v hL) (slackPoly L v) 2).mp
  rw [slackMap_image_eq_momentSlice L v t mu hrange hv]
  exact momentSlice_diamLE_two t mu

/-- A selected row-support face in original coordinates. -/
def slackSupportFace {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ slackPoly L v ∧ ∀ i, i ∉ S → (slackMap L v x) i = 0}

/-- Coordinate-zero support faces correspond exactly under the slack map. -/
theorem slackMap_image_supportFace {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) (mu : ℝ)
    (hrange : L.range = (momentMap t).ker)
    (hv : momentMap t v = (1, mu)) (S : Finset (Fin n)) :
    slackMap L v '' slackSupportFace L v S = supportFace t mu S := by
  have himage := slackMap_image_eq_momentSlice L v t mu hrange hv
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, hx.2⟩
    rw [← himage]
    exact ⟨x, hx.1, rfl⟩
  · intro hs
    have hsimage : s ∈ slackMap L v '' slackPoly L v := by
      rw [himage]
      exact hs.1
    obtain ⟨x, hx, hfx⟩ := hsimage
    refine ⟨x, ⟨hx, ?_⟩, hfx⟩
    intro i hi
    rw [hfx]
    exact hs.2 i hi

/-- Intrinsic, not merely ambient, diameter of each row-support face. -/
theorem slackSupportFace_diamLE_two {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) (mu : ℝ)
    (hL : Function.Injective L) (hrange : L.range = (momentMap t).ker)
    (hv : momentMap t v = (1, mu)) (S : Finset (Fin n)) :
    DiamLE (slackSupportFace L v S) 2 := by
  apply (Hirsch.affineMap_diamLE_image_iff_of_injective
    (slackMap L v) (slackMap_injective L v hL) (slackSupportFace L v S) 2).mp
  rw [slackMap_image_supportFace L v t mu hrange hv S]
  exact supportFace_diamLE_two t mu S

/-- Positive diagonal rescaling of the original row evaluation map. -/
def weightedRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (c : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => c i * ⟪a i, x⟫)
  map_add' x y := by
    ext i
    change c i * ⟪a i, x + y⟫ = c i * ⟪a i, x⟫ + c i * ⟪a i, y⟫
    rw [inner_add_right]
    ring
  map_smul' r x := by
    ext i
    change c i * ⟪a i, r • x⟫ = r * (c i * ⟪a i, x⟫)
    rw [inner_smul_right]
    ring

/-- Correspondingly scaled right-hand side. -/
def weightedOffset {n : ℕ} (b c : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => c i * b i)

lemma weighted_slack_apply {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    slackMap (weightedRows a c) (weightedOffset b c) x i =
      c i * (b i - ⟪a i, x⟫) := by
  change c i * b i - c i * ⟪a i, x⟫ = c i * (b i - ⟪a i, x⟫)
  ring

/-- Positive rescaling preserves the original inequalities exactly. -/
theorem slackPoly_weighted_eq_Hpoly {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) :
    slackPoly (weightedRows a c) (weightedOffset b c) = Hpoly a b := by
  ext x
  constructor
  · intro hx i
    have hi := hx i
    rw [weighted_slack_apply] at hi
    have hp : c i * ⟪a i, x⟫ ≤ c i * b i := by nlinarith only [hi]
    exact le_of_mul_le_mul_left hp (hc i)
  · intro hx i
    rw [weighted_slack_apply]
    exact mul_nonneg (hc i).le (sub_nonneg.mpr (hx i))

/-- Zero weighted slack means exactly original row tightness. -/
theorem weighted_slack_zero_iff {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    slackMap (weightedRows a c) (weightedOffset b c) x i = 0 ↔
      ⟪a i, x⟫ = b i := by
  rw [weighted_slack_apply]
  constructor
  · intro h
    have hz : b i - ⟪a i, x⟫ = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt (hc i))
    exact (sub_eq_zero.mp hz).symm
  · intro h
    rw [h, sub_self, mul_zero]

/-- A directly checkable codimension-two slack certificate gives the full
H-polytope diameter bound. All hypotheses concern linear algebra and positivity. -/
theorem hpoly_diamLE_two_of_positive_slack_certificate {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ) (mu : ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (hL : Function.Injective (weightedRows a c))
    (ht : ∃ i j, t i ≠ t j)
    (hzero : ∀ x, momentMap t (weightedRows a c x) = 0)
    (hoffset : momentMap t (weightedOffset b c) = (1, mu)) :
    DiamLE (Hpoly a b) 2 := by
  have hrange := range_eq_moment_kernel_of_codimension_two
    (weightedRows a c) t hn hL ht hzero
  have hdiam := slackPoly_diamLE_two
    (weightedRows a c) (weightedOffset b c) t mu hL hrange hoffset
  rw [slackPoly_weighted_eq_Hpoly a b c hc] at hdiam
  exact hdiam

/-- The same algebraic certificate bounds intrinsic diameters of arbitrary
selected original row-support faces. No ambient-only adjacency is substituted. -/
theorem row_support_diamLE_two_of_positive_slack_certificate {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ) (mu : ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (hL : Function.Injective (weightedRows a c))
    (ht : ∃ i j, t i ≠ t j)
    (hzero : ∀ x, momentMap t (weightedRows a c x) = 0)
    (hoffset : momentMap t (weightedOffset b c) = (1, mu))
    (S : Finset (Fin n)) :
    DiamLE {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} 2 := by
  have hrange := range_eq_moment_kernel_of_codimension_two
    (weightedRows a c) t hn hL ht hzero
  have heq : slackSupportFace (weightedRows a c) (weightedOffset b c) S =
      {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} := by
    ext x
    simp only [slackSupportFace, Set.mem_setOf_eq,
      slackPoly_weighted_eq_Hpoly a b c hc, weighted_slack_zero_iff a b c hc]
  rw [← heq]
  exact slackSupportFace_diamLE_two
    (weightedRows a c) (weightedOffset b c) t mu hL hrange hoffset S

#print axioms momentMap_surjective
#print axioms range_eq_moment_kernel_of_codimension_two
#print axioms slackMap_injective
#print axioms slackMap_image_eq_momentSlice
#print axioms slackPoly_diamLE_two
#print axioms slackMap_image_supportFace
#print axioms slackSupportFace_diamLE_two
#print axioms slackPoly_weighted_eq_Hpoly
#print axioms weighted_slack_zero_iff
#print axioms hpoly_diamLE_two_of_positive_slack_certificate
#print axioms row_support_diamLE_two_of_positive_slack_certificate

end HirschSlackMoment
