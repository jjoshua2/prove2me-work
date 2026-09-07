import Mathlib
import Solutions.CircuitAugmentation

open Set HirschSlack HirschCircuitProgress HirschAugment

set_option maxHeartbeats 6000000

noncomputable section

namespace HirschConformal

variable {n : ℕ}

/-- Reflect each coordinate according to the sign of the target displacement.
This preserves every support and turns sign compatibility into nonnegativity. -/
def reflect (v : Fin n → ℝ) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := if v i < 0 then -x i else x i
  invFun x i := if v i < 0 then -x i else x i
  left_inv x := by funext i; by_cases h : v i < 0 <;> simp [h]
  right_inv x := by funext i; by_cases h : v i < 0 <;> simp [h]
  map_add' x y := by funext i; by_cases h : v i < 0 <;> simp [h] <;> ring
  map_smul' t x := by funext i; by_cases h : v i < 0 <;> simp [h]

lemma reflect_apply (v x : Fin n → ℝ) (i : Fin n) :
    reflect v x i = if v i < 0 then -x i else x i := rfl

lemma reflect_support (v x : Fin n → ℝ) : support (reflect v x) = support x := by
  ext i
  change (reflect v x i ≠ 0) ↔ (x i ≠ 0)
  rw [reflect_apply]
  by_cases h : v i < 0 <;> simp [h]

lemma reflect_self_nonnegative (v : Fin n → ℝ) : ∀ i, 0 ≤ reflect v v i := by
  intro i
  rw [reflect_apply]
  split_ifs with h
  · linarith
  · exact le_of_not_gt h

lemma conformal_support_subset {g v : Fin n → ℝ} (hg : ConformalPart g v) :
    support g ⊆ support v := by
  intro i hgi
  by_contra hvi
  have hvzero : v i = 0 := not_not.mp hvi
  have hb := hg i
  simp only [hvzero, min_self, max_self] at hb
  exact hgi (le_antisymm hb.2 hb.1)

lemma conformal_complement {g v : Fin n → ℝ} (hg : ConformalPart g v) :
    ConformalPart (v - g) v := by
  intro i
  change min 0 (v i) ≤ v i - g i ∧ v i - g i ≤ max 0 (v i)
  by_cases hi : 0 ≤ v i
  · have hb := (conformal_bounds hg i).1 hi
    rw [min_eq_left hi, max_eq_right hi]
    constructor <;> linarith
  · have hi' : v i ≤ 0 := le_of_not_ge hi
    have hb := (conformal_bounds hg i).2 hi'
    rw [min_eq_right hi', max_eq_left hi']
    constructor <;> linarith

lemma conformal_trans {f g v : Fin n → ℝ}
    (hf : ConformalPart f g) (hg : ConformalPart g v) : ConformalPart f v := by
  intro i
  by_cases hi : 0 ≤ v i
  · have hgb := (conformal_bounds hg i).1 hi
    have hfb := (conformal_bounds hf i).1 hgb.1
    rw [min_eq_left hi, max_eq_right hi]
    exact ⟨hfb.1, hfb.2.trans hgb.2⟩
  · have hi' : v i ≤ 0 := le_of_not_ge hi
    have hgb := (conformal_bounds hg i).2 hi'
    have hfb := (conformal_bounds hf i).2 hgb.2
    rw [min_eq_right hi', max_eq_left hi']
    exact ⟨hgb.1.trans hfb.1, hfb.2⟩

def supportCount (v : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ 0)).card

/-- Remove a conformal elementary summand and make at least one nonzero
coordinate of the residual disappear. This is not a maximal feasible step
of the original polyhedron; it is the circuit-decomposition construction. -/
theorem conformal_elementary_reduction
    (K : Submodule ℝ (Fin n → ℝ)) (v : Fin n → ℝ)
    (hvK : v ∈ K) (hv0 : v ≠ 0) :
    ∃ g : Fin n → ℝ, Elementary K g ∧ ConformalPart g v ∧
      supportCount (v - g) < supportCount v := by
  classical
  let R := reflect v
  let K' : Submodule ℝ (Fin n → ℝ) := K.map R.toLinearMap
  have hRvK : R v ∈ K' := Submodule.mem_map.mpr ⟨v, hvK, rfl⟩
  have hRv0 : R v ≠ 0 := by
    intro h
    apply hv0
    apply R.injective
    simpa only [map_zero] using h
  obtain ⟨e, he, hepos, hesub⟩ :=
    exists_nonnegative_elementary K' (R v) hRvK hRv0 (reflect_self_nonnegative v)
  obtain ⟨w, hwK, hwR⟩ := Submodule.mem_map.mp he.1
  have hwR' : R w = e := hwR
  have hw0 : w ≠ 0 := by
    intro h
    apply he.2.1
    rw [← hwR', h, map_zero]
  have hwE : Elementary K w := by
    refine ⟨hwK, hw0, ?_⟩
    intro h hhK hh0 hhsub
    have hRhK : R h ∈ K' := Submodule.mem_map.mpr ⟨h, hhK, rfl⟩
    have hRh0 : R h ≠ 0 := by
      intro heq
      apply hh0
      apply R.injective
      simpa only [map_zero] using heq
    have hsub' : support (R h) ⊆ support e := by
      rw [← hwR']
      change support (reflect v h) ⊆ support (reflect v w)
      simpa only [reflect_support] using hhsub
    have hback := he.2.2 (R h) hRhK hRh0 hsub'
    rw [← hwR'] at hback
    change support (reflect v w) ⊆ support (reflect v h) at hback
    simpa only [reflect_support] using hback
  have htangent : ∀ i, R v i = 0 → 0 ≤ (-e) i := by
    intro i hvi
    have hei : e i = 0 := by
      by_contra hne
      exact hesub hne hvi
    simp only [Pi.neg_apply, hei, neg_zero, le_refl]
  have heneg : ∃ i, (-e) i < 0 := by
    have hex : ∃ i, e i ≠ 0 := by
      by_contra h
      apply he.2.1
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    change -e i < 0
    have hpos : 0 < e i := lt_of_le_of_ne (hepos i) (Ne.symm hi)
    linarith
  obtain ⟨alpha, ha, hremain, ⟨q, heq, hvq, hzeroq⟩, _⟩ :=
    maximal_nonnegative (R v) (-e) (reflect_self_nonnegative v) htangent heneg
  let g : Fin n → ℝ := alpha • w
  have hgE : Elementary K g := elementary_smul K w hwE alpha ha.ne'
  have hbounds : ∀ i, 0 ≤ alpha * e i ∧ alpha * e i ≤ R v i := by
    intro i
    have hrem := hremain i
    change 0 ≤ R v i + alpha * (-e i) at hrem
    exact ⟨mul_nonneg ha.le (hepos i), by linarith⟩
  have hconf : ConformalPart g v := by
    intro i
    have hb := hbounds i
    have hwri : (if v i < 0 then -w i else w i) = e i := congrFun hwR' i
    by_cases hi : v i < 0
    · simp only [if_pos hi] at hwri
      change 0 ≤ alpha * e i ∧ alpha * e i ≤ (if v i < 0 then -v i else v i) at hb
      rw [if_pos hi] at hb
      change min 0 (v i) ≤ alpha * w i ∧ alpha * w i ≤ max 0 (v i)
      rw [min_eq_right hi.le, max_eq_left hi.le]
      constructor <;> nlinarith
    · have hvi : 0 ≤ v i := le_of_not_gt hi
      simp only [if_neg hi] at hwri
      change 0 ≤ alpha * e i ∧ alpha * e i ≤ (if v i < 0 then -v i else v i) at hb
      rw [if_neg hi] at hb
      change min 0 (v i) ≤ alpha * w i ∧ alpha * w i ≤ max 0 (v i)
      rw [min_eq_left hvi, max_eq_right hvi]
      constructor <;> nlinarith
  have hsub : support (v - g) ⊆ support v :=
    conformal_support_subset (conformal_complement hconf)
  have hvq0 : v q ≠ 0 := by
    intro hvzero
    have hRvzero : R v q = 0 := by simp only [R, reflect_apply, hvzero, neg_zero, ite_self]
    linarith
  have hresq : (v - g) q = 0 := by
    have hwri : (if v q < 0 then -w q else w q) = e q := congrFun hwR' q
    change (if v q < 0 then -v q else v q) + alpha * (-e q) = 0 at hzeroq
    change v q - alpha * w q = 0
    by_cases hi : v q < 0
    · rw [if_pos hi] at hwri hzeroq
      nlinarith
    · rw [if_neg hi] at hwri hzeroq
      nlinarith
  have hstrict : (Finset.univ.filter (fun i => (v - g) i ≠ 0)) ⊂
      Finset.univ.filter (fun i => v i ≠ 0) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsub (Finset.mem_filter.mp hi).2⟩
    · intro heq
      have hqmem : q ∈ Finset.univ.filter (fun i => v i ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ q, hvq0⟩
      rw [← heq] at hqmem
      exact (Finset.mem_filter.mp hqmem).2 hresq
  exact ⟨g, hgE, hconf, Finset.card_lt_card hstrict⟩

/-- A conformal circuit decomposition with at most n summands. This looser
ambient-coordinate bound suffices for a cubic circuit-diameter envelope. -/
theorem exists_conformal_decomposition
    (K : Submodule ℝ (Fin n → ℝ)) (v : Fin n → ℝ) (hvK : v ∈ K) :
    ∃ parts : List (Fin n → ℝ), parts.sum = v ∧ parts.length ≤ n ∧
      ∀ g ∈ parts, Elementary K g ∧ ConformalPart g v := by
  classical
  have aux : ∀ k : ℕ, ∀ v : Fin n → ℝ, v ∈ K → supportCount v = k →
      ∃ parts : List (Fin n → ℝ), parts.sum = v ∧ parts.length ≤ k ∧
        ∀ g ∈ parts, Elementary K g ∧ ConformalPart g v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hvK hk
      by_cases hv0 : v = 0
      · subst v
        exact ⟨[], by simp, by simp, by simp⟩
      obtain ⟨g, hgE, hgconf, hlt⟩ := conformal_elementary_reduction K v hvK hv0
      have hremK : v - g ∈ K := K.sub_mem hvK hgE.1
      obtain ⟨parts, hsum, hlen, hparts⟩ :=
        ih (supportCount (v - g)) (by omega) (v - g) hremK rfl
      refine ⟨g :: parts, ?_, ?_, ?_⟩
      · rw [List.sum_cons, hsum]
        abel
      · simp only [List.length_cons]
        omega
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨hgE, hgconf⟩
        · have hp := hparts z hz
          exact ⟨hp.1, conformal_trans hp.2 (conformal_complement hgconf)⟩
  obtain ⟨parts, hsum, hlen, hparts⟩ := aux (supportCount v) v hvK rfl
  have hcard : supportCount v ≤ n := by
    have h := Finset.card_le_card (Finset.filter_subset (fun i => v i ≠ 0)
      (Finset.univ : Finset (Fin n)))
    simpa only [Finset.card_univ, Fintype.card_fin, supportCount] using h
  exact ⟨parts, hsum, hlen.trans hcard, hparts⟩

#print axioms conformal_elementary_reduction
#print axioms exists_conformal_decomposition

end HirschConformal
