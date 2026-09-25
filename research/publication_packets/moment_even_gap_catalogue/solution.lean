import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

/-! Exact accepted evaluation helpers from #285/#286 via #287. -/
namespace Hirsch.MomentSmallFaces

/-- The constant coefficient is separated before centering the moment rows. -/
lemma eval_split (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n) (t : ℝ) :
    p.eval t = p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) * t ^ (j.val + 1) := by
  calc
    p.eval t = ∑ j ∈ Finset.range (n + 1), p.coeff j * t ^ j :=
      Polynomial.eval_eq_sum_range' (by omega) t
    _ = ∑ j : Fin (n + 1), p.coeff j.val * t ^ j.val := Finset.sum_range _
    _ = p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) * t ^ (j.val + 1) := by
      simpa using (Fin.sum_univ_succ
        (fun j : Fin (n + 1) => p.coeff j.val * t ^ j.val))

/-- Averaging evaluations is the same as evaluating the coefficient functional
on the averaged moment vector. No extremal-point or support oracle is used. -/
lemma average_split {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (hm : (Fintype.card ι : ℝ) ≠ 0) :
    (∑ i, p.eval (a i)) / (Fintype.card ι : ℝ) =
      p.coeff 0 + ∑ j : Fin n, p.coeff (j.val + 1) *
        ((∑ i, a i ^ (j.val + 1)) / (Fintype.card ι : ℝ)) := by
  classical
  have hexpand : (∑ i, p.eval (a i)) =
      (Fintype.card ι : ℝ) * p.coeff 0 +
        ∑ j : Fin n, p.coeff (j.val + 1) * (∑ i, a i ^ (j.val + 1)) := by
    simp_rw [eval_split p n hp]
    rw [Finset.sum_add_distrib]
    congr 1
    · simp
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      exact (Finset.mul_sum _ _ _).symm
  rw [hexpand, add_div, Finset.sum_div]
  congr 1
  · field_simp [hm]
  · apply Finset.sum_congr rfl
    intro j _
    ring

lemma centered_eval {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (p : Polynomial ℝ) (n : ℕ) (hp : p.natDegree ≤ n)
    (hm : (Fintype.card ι : ℝ) ≠ 0) (i : ι) :
    (∑ j : Fin n,
      (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) *
        p.coeff (j.val + 1)) =
      p.eval (a i) - (∑ l, p.eval (a l)) / (Fintype.card ι : ℝ) := by
  classical
  have he := eval_split p n hp (a i)
  have hav := average_split a p n hp hm
  calc
    (∑ j : Fin n,
      (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) *
        p.coeff (j.val + 1)) =
      (∑ j : Fin n, p.coeff (j.val + 1) * a i ^ (j.val + 1)) -
      ∑ j : Fin n, p.coeff (j.val + 1) *
        ((∑ l, a l ^ (j.val + 1)) / (Fintype.card ι : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = p.eval (a i) - (∑ l, p.eval (a l)) / (Fintype.card ι : ℝ) := by
      linarith

end Hirsch.MomentSmallFaces

namespace Hirsch.MomentBarycentric

noncomputable def row {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) : ℝ :=
  ∑ j : Fin d,
    (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (m : ℝ)) * x j

noncomputable def slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) : Polynomial ℝ :=
  1 - ∑ j : Fin d,
    (Polynomial.X ^ (j.val + 1) -
      Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))) * Polynomial.C (x j)

lemma eval_slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) :
    (slack a x).eval (a i) = 1 - row a x i := by
  simp [slack, row, Polynomial.eval_finsetSum]

lemma degree_slack {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) :
    (slack a x).natDegree ≤ d := by
  unfold slack
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  calc
    ((Polynomial.X ^ (j.val + 1) -
        Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))) *
        Polynomial.C (x j)).natDegree ≤
        (Polynomial.X ^ (j.val + 1) -
          Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree +
          (Polynomial.C (x j)).natDegree := Polynomial.natDegree_mul_le
    _ = (Polynomial.X ^ (j.val + 1) -
          Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree := by simp
    _ ≤ max (Polynomial.X ^ (j.val + 1) : Polynomial ℝ).natDegree
          (Polynomial.C ((∑ l, a l ^ (j.val + 1)) / (m : ℝ))).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ = j.val + 1 := by simp
    _ ≤ d := by omega

lemma sum_row_zero {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hm : (m : ℝ) ≠ 0) : ∑ i, row a x i = 0 := by
  unfold row
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  have hc : (∑ _i : Fin m, (∑ l : Fin m, a l ^ (j.val + 1)) / (m : ℝ)) =
      ∑ l : Fin m, a l ^ (j.val + 1) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hm]
    <;> ring
  rw [hc, sub_self, zero_mul]

lemma slack_ne_zero {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hm : (m : ℝ) ≠ 0) : slack a x ≠ 0 := by
  intro hz
  have hsum : (∑ i : Fin m, (slack a x).eval (a i)) = (m : ℝ) := by
    simp_rw [eval_slack]
    rw [Finset.sum_sub_distrib, sum_row_zero a x hm]
    simp
  have hzero : (∑ i : Fin m, (slack a x).eval (a i)) = 0 := by simp [hz]
  exact hm (hsum.symm.trans hzero)


end Hirsch.MomentBarycentric

namespace Hirsch.MomentVertices

open Set MomentBarycentric

/-- Exact finite-margin helper reused from accepted #290. -/
lemma finite_margin {ι : Type*} (S : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i ∈ S, e * |t i| < a i := by
  classical
  revert ha
  induction S using Finset.induction_on with
  | empty =>
      intro ha
      exact ⟨1, by norm_num, by simp⟩
  | @insert i S hi ih =>
      intro ha
      obtain ⟨e, he, hS⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai : 0 < a i := ha i (Finset.mem_insert_self i S)
      have hd : 0 < |t i| + 1 := by positivity
      let f : ℝ := a i / (|t i| + 1)
      have hf : 0 < f := div_pos hai hd
      have hfeq : f * (|t i| + 1) = a i := by
        dsimp [f]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      refine ⟨min e f, lt_min he hf, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have hb := mul_le_mul_of_nonneg_right (min_le_right e f) (abs_nonneg (t i))
        nlinarith
      · exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (min_le_left e f) (abs_nonneg (t j))) (hS j hj)

lemma row_add {d m : ℕ} (a : Fin m → ℝ) (x y : Fin d → ℝ) (i : Fin m) :
    row a (x+y) i = row a x i + row a y i := by
  simp only [row, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma row_sub {d m : ℕ} (a : Fin m → ℝ) (x y : Fin d → ℝ) (i : Fin m) :
    row a (x-y) i = row a x i - row a y i := by
  simp only [row, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma row_smul {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (c : ℝ) (i : Fin m) :
    row a (c • x) i = c * row a x i := by
  unfold row
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

noncomputable def active {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => row a x i = 1)

lemma mem_active {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) (i : Fin m) :
    i ∈ active a x ↔ row a x i = 1 := by
  simp [active]

noncomputable def activeEval {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] ((active a x) → ℝ) where
  toFun z i := row a z i.val
  map_add' y z := by
    funext i
    exact row_add a y z i.val
  map_smul' c z := by
    funext i
    exact row_smul a z c i.val

/-- Root counting applies even to infeasible ambient points. -/
theorem tight_card_le {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ) :
    (active a x).card ≤ d := by
  classical
  by_contra hn
  have hlt : d < (active a x).card := lt_of_not_ge hn
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  apply slack_ne_zero a x hm0
  have hnat : (slack a x).natDegree < (active a x).card :=
    (degree_slack a x).trans_lt hlt
  have hdeg : (slack a x).degree < ((active a x).card : WithBot ℕ) :=
    lt_of_le_of_lt (slack a x).degree_le_natDegree (by exact_mod_cast hnat)
  apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (active a x) ha.injOn hdeg
  intro i hi
  rw [eval_slack, (mem_active a x i).mp hi]
  ring

/-- Interpolation and a centering correction construct arbitrary active-row
values. Full rank is a conclusion, not a supplied inverse or independence. -/
theorem activeEval_surjective {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ) :
    Function.Surjective (activeEval a x) := by
  classical
  intro values
  let I := ↥(active a x)
  let b : I → ℝ := fun i => a i.val
  have hb : Function.Injective b := by
    intro i j hij
    apply Subtype.ext
    exact ha hij
  let p : Polynomial ℝ := Lagrange.interpolate Finset.univ b values
  have hnat : p.natDegree ≤ Fintype.card I - 1 := by
    apply Polynomial.natDegree_le_iff_degree_le.mpr
    simpa only [Finset.card_univ] using Lagrange.degree_interpolate_le (s := Finset.univ) (v := b) values hb.injOn
  have hcard : Fintype.card I ≤ d := by
    simpa only [I, Fintype.card_coe] using tight_card_le a ha hm x
  have hp : p.natDegree ≤ d := by omega
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hfin0 : (Fintype.card (Fin m) : ℝ) ≠ 0 := by
    simpa only [Fintype.card_fin] using hm0
  let y : Fin d → ℝ := fun j => p.coeff (j.val+1)
  let c : ℝ := (∑ i : Fin m, p.eval (a i)) / (m : ℝ)
  have he : ∀ i : Fin m, row a y i = p.eval (a i)-c := by
    intro i
    simpa only [row, y, c, Fintype.card_fin] using
      MomentSmallFaces.centered_eval a p d hp hfin0 i
  refine ⟨y + c • x, ?_⟩
  funext i
  change row a (y + c • x) i.val = values i
  have hix : row a x i.val = 1 := (mem_active a x i.val).mp i.property
  have hev : p.eval (a i.val) = values i :=
    Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := b) values hb.injOn (Finset.mem_univ i)
  rw [row_add, row_smul, hix, he, hev]
  ring

/-- The finite-margin argument detects every nonzero active-kernel motion at
an actual extreme point of the original halfspace intersection. -/
lemma extreme_kernel {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hx : x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ)
    (z : Fin d → ℝ) (hz : ∀ i, row a x i = 1 → row a z i = 0) : z = 0 := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun i => row a x i ≠ 1)
  have hslack : ∀ i ∈ S, 0 < 1-row a x i := by
    intro i hi
    exact sub_pos.mpr (lt_of_le_of_ne (hx.1 i) (Finset.mem_filter.mp hi).2)
  obtain ⟨e,he,hsmall⟩ := finite_margin S (fun i => 1-row a x i)
    (fun i => row a z i) hslack
  have hcuts : ∀ i, row a (x+e•z) i ≤ 1 ∧ row a (x-e•z) i ≤ 1 := by
    intro i
    by_cases hi : row a x i = 1
    · simp only [row_add, row_sub, row_smul, hz i hi, mul_zero, add_zero, sub_zero]
      exact ⟨hx.1 i,hx.1 i⟩
    · have hs : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
      have hb := hsmall i hs
      have hlo := mul_le_mul_of_nonneg_left (neg_abs_le (row a z i)) he.le
      have hhi := mul_le_mul_of_nonneg_left (le_abs_self (row a z i)) he.le
      simp only [row_add, row_sub, row_smul]
      constructor <;> nlinarith
  have hmid : x ∈ openSegment ℝ (x+e•z) (x-e•z) := by
    refine ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have heq : x+e•z=x := hx.2 (fun i => (hcuts i).1) (fun i => (hcuts i).2) hmid
  funext j
  have h := congrFun heq j
  change x j+e*z j=x j at h
  have hprod : e*z j=0 := by linarith
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt he)

lemma extreme_activeEval_injective {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hx : x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ) :
    Function.Injective (activeEval a x) := by
  classical
  intro y z heq
  apply sub_eq_zero.mp
  apply extreme_kernel a x hx (y-z)
  intro i hi
  let j : active a x := ⟨i,(mem_active a x i).mpr hi⟩
  have he : row a y i = row a z i := congrFun heq j
  rw [row_sub, he, sub_self]

lemma extreme_of_activeEval_injective {d m : ℕ} (a : Fin m → ℝ) (x : Fin d → ℝ)
    (hx : ∀ i, row a x i ≤ 1) (hinj : Function.Injective (activeEval a x)) :
    x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ := by
  classical
  refine ⟨hx,?_⟩
  intro y hy z hz hseg
  obtain ⟨u,v,hu,hv,huv,heq⟩ := hseg
  apply hinj
  funext i
  change row a y i.val = row a x i.val
  have hix : row a x i.val = 1 := (mem_active a x i.val).mp i.property
  have hrow := congrArg (fun w : Fin d → ℝ => row a w i.val) heq
  change row a (u • y + v • z) i.val = row a x i.val at hrow
  rw [row_add, row_smul, row_smul, hix] at hrow
  have h1 := mul_nonneg hu.le (sub_nonneg.mpr (hy i.val))
  have h2 := mul_nonneg hv.le (sub_nonneg.mpr (hz i.val))
  have he : u*(1-row a y i.val)=0 := by nlinarith
  have hh : 1-row a y i.val=0 := (mul_eq_zero.mp he).resolve_left (ne_of_gt hu)
  rw [hix]
  linarith

/-- Exactly dimension many tight original rows characterize all actual vertices. -/
theorem extreme_iff_tight_card {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ) :
    x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ ↔
      (∀ i, row a x i ≤ 1) ∧ (active a x).card = d := by
  classical
  constructor
  · intro hx
    refine ⟨hx.1, le_antisymm (tight_card_le a ha hm x) ?_⟩
    have h := LinearMap.finrank_le_finrank_of_injective (extreme_activeEval_injective a x hx)
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      Fintype.card_coe] using h
  · rintro ⟨hx,hcard⟩
    apply extreme_of_activeEval_injective a x hx
    have hdim : Module.finrank ℝ (Fin d → ℝ) =
        Module.finrank ℝ ((active a x) → ℝ) := by
      simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
        Fintype.card_coe, hcard]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
      (activeEval_surjective a ha hm x)

end Hirsch.MomentVertices

namespace Hirsch.MomentRootCatalogue

open Set MomentBarycentric MomentVertices

noncomputable def rootPoly {m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) :
    Polynomial ℝ := ∏ i ∈ S, (Polynomial.X - Polynomial.C (a i))

lemma eval_rootPoly {m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) (t : ℝ) :
    (rootPoly a S).eval t = ∏ i ∈ S, (t-a i) := by
  classical
  simp [rootPoly, Polynomial.eval_prod]

lemma degree_rootPoly {m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) :
    (rootPoly a S).natDegree = S.card := by
  classical
  change (∏ i ∈ S, ((Polynomial.X : Polynomial ℝ) - Polynomial.C (a i))).natDegree = S.card
  rw [Polynomial.natDegree_prod_of_monic S
    (fun i : Fin m => ((Polynomial.X : Polynomial ℝ) - Polynomial.C (a i)))
    (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp

lemma eval_rootPoly_zero_iff {m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (S : Finset (Fin m)) (i : Fin m) :
    (rootPoly a S).eval (a i) = 0 ↔ i ∈ S := by
  classical
  rw [eval_rootPoly]
  constructor
  · intro h
    obtain ⟨j,hj,hzero⟩ := Finset.prod_eq_zero_iff.mp h
    have hij : i = j := ha (sub_eq_zero.mp hzero)
    exact hij.symm ▸ hj
  · intro hi
    exact Finset.prod_eq_zero_iff.mpr ⟨i,hi,sub_self _⟩

noncomputable def mean {m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  (∑ i : Fin m, (rootPoly a S).eval (a i)) / (m : ℝ)

noncomputable def candidate {d m : ℕ} (a : Fin m → ℝ)
    (S : Finset (Fin m)) : Fin d → ℝ :=
  fun j => -(rootPoly a S).coeff (j.val+1) / mean a S

/-- The same full-label mean is used in both the coefficient formula and all
original inequalities. No positivity of that mean is assumed. -/
lemma row_candidate {d m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m))
    (hS : S.card ≤ d) (hm : (m : ℝ) ≠ 0) (hmean : mean a S ≠ 0) (i : Fin m) :
    row a (candidate (d:=d) a S) i = 1 - (rootPoly a S).eval (a i) / mean a S := by
  classical
  have hdeg : (rootPoly a S).natDegree ≤ d := by rw [degree_rootPoly]; exact hS
  have hm' : (Fintype.card (Fin m) : ℝ) ≠ 0 := by simpa only [Fintype.card_fin] using hm
  have hc := MomentSmallFaces.centered_eval a (rootPoly a S) d hdeg hm' i
  have hc' : (∑ j : Fin d,
      (a i ^ (j.val+1) - (∑ l, a l ^ (j.val+1)) / (m : ℝ)) *
        (rootPoly a S).coeff (j.val+1)) = (rootPoly a S).eval (a i) - mean a S := by
    simpa only [Fintype.card_fin, mean] using hc
  calc
    row a (candidate (d:=d) a S) i =
        -(mean a S)⁻¹ * (∑ j : Fin d,
          (a i ^ (j.val+1) - (∑ l, a l ^ (j.val+1)) / (m : ℝ)) *
            (rootPoly a S).coeff (j.val+1)) := by
      unfold row candidate
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -(mean a S)⁻¹ * ((rootPoly a S).eval (a i) - mean a S) := by rw [hc']
    _ = 1 - (rootPoly a S).eval (a i) / mean a S := by
      field_simp [hmean]
      <;> ring

lemma active_candidate {d m : ℕ} (a : Fin m → ℝ) (ha : Function.Injective a)
    (S : Finset (Fin m)) (hS : S.card ≤ d) (hm : (m : ℝ) ≠ 0)
    (hmean : mean a S ≠ 0) : active a (candidate (d:=d) a S) = S := by
  classical
  ext i
  rw [mem_active, row_candidate a S hS hm hmean i]
  constructor
  · intro h
    have hquot : (rootPoly a S).eval (a i) / mean a S = 0 := by linarith
    have hmul := div_mul_cancel₀ ((rootPoly a S).eval (a i)) hmean
    rw [hquot, zero_mul] at hmul
    exact (eval_rootPoly_zero_iff a ha S i).mp hmul.symm
  · intro hi
    rw [(eval_rootPoly_zero_iff a ha S i).mpr hi, zero_div, sub_zero]

/-- A zero full-label mean would provide a nonzero active-kernel motion. The
accepted extremality theorem excludes it, including in dimension zero. -/
theorem extreme_mean_ne_zero {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ)
    (hx : x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ) :
    mean a (active a x) ≠ 0 := by
  classical
  let S := active a x
  have hS : S.card = d := ((extreme_iff_tight_card a ha hm x).mp hx).2
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hm' : (Fintype.card (Fin m) : ℝ) ≠ 0 := by simpa only [Fintype.card_fin] using hm0
  have hdeg : (rootPoly a S).natDegree ≤ d := by rw [degree_rootPoly,hS]
  let y : Fin d → ℝ := fun j => (rootPoly a S).coeff (j.val+1)
  have he : ∀ i : Fin m, row a y i = (rootPoly a S).eval (a i) - mean a S := by
    intro i
    simpa only [row,y,mean,Fintype.card_fin] using
      MomentSmallFaces.centered_eval a (rootPoly a S) d hdeg hm' i
  intro hzero
  change mean a S = 0 at hzero
  have hy : y = 0 := by
    apply extreme_kernel a x hx y
    intro i hi
    rw [he, hzero, sub_zero]
    exact (eval_rootPoly_zero_iff a ha S i).mpr ((mem_active a x i).mpr hi)
  obtain ⟨i,hi⟩ : ∃ i : Fin m, i ∉ S := by
    by_contra hn
    have hall : (Finset.univ : Finset (Fin m)) ⊆ S := by
      intro i _
      by_contra hi
      exact hn ⟨i,hi⟩
    have hc := Finset.card_le_card hall
    simp only [Finset.card_univ,Fintype.card_fin,hS] at hc
    omega
  have hr : row a y i = 0 := by rw [hy]; simp [row]
  rw [he, hzero, sub_zero] at hr
  exact hi ((eval_rootPoly_zero_iff a ha S i).mp hr)

/-- Every actual vertex equals the explicit coefficient candidate on its own
exact tight set. No inversion, supplied vertex list or root-factorization oracle. -/
theorem reconstruct_extreme {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) (x : Fin d → ℝ)
    (hx : x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ) :
    candidate (d:=d) a (active a x) = x := by
  classical
  have hS := ((extreme_iff_tight_card a ha hm x).mp hx).2
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hmean := extreme_mean_ne_zero a ha hm x hx
  apply extreme_activeEval_injective a x hx
  funext i
  change row a (candidate (d:=d) a (active a x)) i.val = row a x i.val
  rw [row_candidate a (active a x) hS.le hm0 hmean i.val,
    (eval_rootPoly_zero_iff a ha (active a x) i.val).mpr i.property,
    zero_div,sub_zero]
  exact ((mem_active a x i.val).mp i.property).symm

noncomputable def catalogue (d : ℕ) {m : ℕ} (a : Fin m → ℝ) :
    Finset (Finset (Fin m)) :=
  (Finset.powersetCard d Finset.univ).filter
    (fun S => mean a S ≠ 0 ∧ ∀ i : Fin m, 0 ≤ (rootPoly a S).eval (a i) / mean a S)

lemma mem_catalogue {d m : ℕ} (a : Fin m → ℝ) (S : Finset (Fin m)) :
    S ∈ catalogue d a ↔ S.card = d ∧ mean a S ≠ 0 ∧
      ∀ i : Fin m, 0 ≤ (rootPoly a S).eval (a i) / mean a S := by
  classical
  simp [catalogue, Finset.mem_powersetCard, and_assoc]

/-- The explicit finite filter returns exactly every original extreme point,
with no duplicate candidates. It is not asserted polynomial in dimension. -/
theorem complete_catalogue {d m : ℕ} (a : Fin m → ℝ)
    (ha : Function.Injective a) (hm : d < m) :
    Set.InjOn (candidate (d:=d) a) (catalogue d a) ∧
    (∀ x : Fin d → ℝ,
      x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ ↔
        x ∈ (catalogue d a).image (candidate (d:=d) a)) ∧
    (∀ S ∈ catalogue d a, ∀ i : Fin m,
      row a (candidate (d:=d) a S) i = 1 ↔ i ∈ S) ∧
    ((catalogue d a).image (candidate (d:=d) a)).card = (catalogue d a).card ∧
    (catalogue d a).card ≤ Nat.choose m d := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (show 0 < m by omega))
  have hact : ∀ S ∈ catalogue d a, active a (candidate (d:=d) a S) = S := by
    intro S hS
    obtain ⟨hc,hmn,hnon⟩ := (mem_catalogue a S).mp hS
    exact active_candidate a ha S hc.le hm0 hmn
  have hinj : Set.InjOn (candidate (d:=d) a) (catalogue d a) := by
    intro S hS T hT he
    calc
      S = active a (candidate (d:=d) a S) := (hact S hS).symm
      _ = active a (candidate (d:=d) a T) := congrArg (active a) he
      _ = T := hact T hT
  refine ⟨hinj,?_,?_,Finset.card_image_of_injOn hinj,?_⟩
  · intro x
    constructor
    · intro hx
      have hS := ((extreme_iff_tight_card a ha hm x).mp hx).2
      have hmean := extreme_mean_ne_zero a ha hm x hx
      have he := reconstruct_extreme a ha hm x hx
      have hmem : active a x ∈ catalogue d a := by
        apply (mem_catalogue a (active a x)).mpr
        refine ⟨hS,hmean,?_⟩
        intro i
        have hv := row_candidate a (active a x) hS.le hm0 hmean i
        rw [he] at hv
        linarith [hx.1 i]
      exact Finset.mem_image.mpr ⟨active a x,hmem,he⟩
    · intro hx
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hc,hmn,hnon⟩ := (mem_catalogue a S).mp hS
      apply (extreme_iff_tight_card a ha hm _).mpr
      constructor
      · intro i
        rw [row_candidate a S hc.le hm0 hmn i]
        linarith [hnon i]
      · rw [hact S hS]
        exact hc
  · intro S hS i
    rw [← mem_active, hact S hS]
  · have hsub : catalogue d a ⊆ Finset.powersetCard d (Finset.univ : Finset (Fin m)) := by
      intro S hS
      exact (Finset.mem_filter.mp hS).1
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using hc

end Hirsch.MomentRootCatalogue

namespace Hirsch.MomentEvenGaps

open MomentRootCatalogue MomentBarycentric

/-- The sign of a nonzero product is the parity of its negative factors. -/
private theorem prod_positive_iff_even_neg {ι : Type*}
    (S : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ S, f i ≠ 0) :
    0 < ∏ i ∈ S, f i ↔ (S.filter (fun i => f i < 0)).card % 2 = 0 := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | @insert i S hi ih =>
    intro hf
    have hfi : f i ≠ 0 := hf i (Finset.mem_insert_self i S)
    have hfs : ∀ j ∈ S, f j ≠ 0 :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ S, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfs
    have hnot : i ∉ S.filter (fun j => f j < 0) := by
      intro h
      exact hi (Finset.mem_filter.mp h).1
    by_cases hneg : f i < 0
    · rw [Finset.prod_insert hi, Finset.filter_insert, if_pos hneg,
        Finset.card_insert_of_notMem hnot]
      have hsign : 0 < f i * (∏ j ∈ S, f j) ↔ ¬ 0 < ∏ j ∈ S, f j := by
        constructor
        · intro h hp
          have hn := mul_neg_of_neg_of_pos hneg hp
          linarith
        · intro h
          have hn : (∏ j ∈ S, f j) < 0 :=
            lt_of_le_of_ne (le_of_not_gt h) hprod
          exact mul_pos_of_neg_of_neg hneg hn
      rw [hsign, ih hfs]
      omega
    · have hpos : 0 < f i := lt_of_le_of_ne (le_of_not_gt hneg) hfi.symm
      rw [Finset.prod_insert hi, Finset.filter_insert, if_neg hneg]
      have hsign : 0 < f i * (∏ j ∈ S, f j) ↔ 0 < ∏ j ∈ S, f j := by
        constructor
        · intro h
          by_contra hn
          have hh := mul_nonpos_of_nonneg_of_nonpos hpos.le (le_of_not_gt hn)
          linarith
        · exact mul_pos hpos
      rw [hsign]
      exact ih hfs

/-- Between two nonroots, precisely the intervening roots contribute negative
factors to the product of the two polynomial evaluations. -/
theorem pair_sign_iff_even_gap {m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (S : Finset (Fin m)) (i j : Fin m) (hi : i ∉ S) (hj : j ∉ S) (hij : i < j) :
    0 < (rootPoly a S).eval (a i) * (rootPoly a S).eval (a j) ↔
      (S.filter (fun s => i < s ∧ s < j)).card % 2 = 0 := by
  classical
  let f : Fin m → ℝ := fun s => (a i - a s) * (a j - a s)
  have hnon : ∀ s ∈ S, f s ≠ 0 := by
    intro s hs
    apply mul_ne_zero
    · apply sub_ne_zero.mpr
      intro he
      have h := ha.injective he
      subst s
      exact hi hs
    · apply sub_ne_zero.mpr
      intro he
      have h := ha.injective he
      subst s
      exact hj hs
  have hsign : ∀ s, f s < 0 ↔ i < s ∧ s < j := by
    intro s
    constructor
    · intro hn
      have hab := ha hij
      have hbetween : a i < a s ∧ a s < a j := by
        change (a i - a s) * (a j - a s) < 0 at hn
        rcases mul_neg_iff.mp hn with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
          constructor <;> linarith
      constructor
      · by_contra hh
        have hc := ha.monotone (le_of_not_gt hh)
        linarith [hbetween.1]
      · by_contra hh
        have hc := ha.monotone (le_of_not_gt hh)
        linarith [hbetween.2]
    · rintro ⟨h1,h2⟩
      exact mul_neg_of_neg_of_pos (sub_neg.mpr (ha h1)) (sub_pos.mpr (ha h2))
  have hfilter : S.filter (fun s => f s < 0) =
      S.filter (fun s => i < s ∧ s < j) := by
    apply Finset.filter_congr
    intro s _
    exact hsign s
  rw [eval_rootPoly, eval_rootPoly, ← Finset.prod_mul_distrib]
  exact (prod_positive_iff_even_neg S f hnon).trans (by rw [hfilter])

/-- Normalizing a finite nonzero family by its mean is nonnegative exactly
when all its nonzero entries have the same sign. Either mean sign is allowed. -/
private theorem normalized_iff_pair_products {m : ℕ} (b : Fin m → ℝ)
    (hm : 0 < (m : ℝ)) (hne : ∃ i, b i ≠ 0) :
    let μ : ℝ := (∑ i, b i) / (m : ℝ)
    (μ ≠ 0 ∧ ∀ i, 0 ≤ b i / μ) ↔
      ∀ i, b i ≠ 0 → ∀ j, b j ≠ 0 → 0 < b i * b j := by
  classical
  let μ : ℝ := (∑ i, b i) / (m : ℝ)
  change (μ ≠ 0 ∧ ∀ i, 0 ≤ b i / μ) ↔ _
  constructor
  · rintro ⟨hmu,hpos⟩ i hi j hj
    have hpi : 0 < b i / μ :=
      lt_of_le_of_ne (hpos i) (div_ne_zero hi hmu).symm
    have hpj : 0 < b j / μ :=
      lt_of_le_of_ne (hpos j) (div_ne_zero hj hmu).symm
    have he : b i * b j = ((b i / μ) * (b j / μ)) * μ ^ 2 := by
      field_simp [hmu]
      <;> ring
    rw [he]
    exact mul_pos (mul_pos hpi hpj) (sq_pos_of_ne_zero hmu)
  · intro hprod
    obtain ⟨i₀,hi₀⟩ := hne
    let c : ℝ := b i₀
    have hc : c ≠ 0 := hi₀
    have hnon : ∀ i, 0 ≤ c * b i := by
      intro i
      by_cases hi : b i = 0
      · simp [hi]
      · exact (hprod i₀ hi₀ i hi).le
    have hself : 0 < c * b i₀ := hprod i₀ hi₀ i₀ hi₀
    have hsum : 0 < ∑ i, c * b i :=
      hself.trans_le (Finset.single_le_sum (fun i _ => hnon i) (Finset.mem_univ i₀))
    have hcm : 0 < c * μ := by
      have he : c * μ = (∑ i, c * b i) / (m : ℝ) := by
        rw [← Finset.mul_sum]
        dsimp [μ]
        ring
      rw [he]
      exact div_pos hsum hm
    have hmu : μ ≠ 0 := by
      intro h
      rw [h, mul_zero] at hcm
      exact (lt_irrefl 0) hcm
    refine ⟨hmu,?_⟩
    intro i
    by_cases hi : b i = 0
    · simp [hi]
    · have he : b i / μ = (c * b i) / (c * μ) := by
        field_simp [hc,hmu]
        <;> ring
      rw [he]
      exact (div_pos (hprod i₀ hi₀ i hi) hcm).le

def EvenGaps {m : ℕ} (S : Finset (Fin m)) : Prop :=
  ∀ i ∉ S, ∀ j ∉ S, i < j → (S.filter (fun s => i < s ∧ s < j)).card % 2 = 0

/-- Gale's even-gap condition is EXACTLY the full-label root-polynomial filter,
including the nonzero mean requirement rather than assuming it. -/
theorem root_filter_iff_even_gaps {m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (S : Finset (Fin m)) (hproper : S.card < m) :
    (mean a S ≠ 0 ∧ ∀ i : Fin m, 0 ≤ (rootPoly a S).eval (a i) / mean a S) ↔
      EvenGaps S := by
  classical
  let b : Fin m → ℝ := fun i => (rootPoly a S).eval (a i)
  have hmNat : 0 < m := by omega
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmNat
  obtain ⟨i₀,hi₀⟩ : ∃ i₀ : Fin m, i₀ ∉ S := by
    by_contra hn
    have hall : (Finset.univ : Finset (Fin m)) ⊆ S := by
      intro i _
      by_contra hi
      exact hn ⟨i,hi⟩
    have hc := Finset.card_le_card hall
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    omega
  have hb : ∀ i, b i ≠ 0 ↔ i ∉ S := by
    intro i
    exact not_congr (eval_rootPoly_zero_iff a ha.injective S i)
  have hnorm := normalized_iff_pair_products b hm ⟨i₀,(hb i₀).mpr hi₀⟩
  change (mean a S ≠ 0 ∧ ∀ i, 0 ≤ (rootPoly a S).eval (a i) / mean a S) ↔
    (∀ i, b i ≠ 0 → ∀ j, b j ≠ 0 → 0 < b i * b j) at hnorm
  rw [hnorm]
  constructor
  · intro hp i hi j hj hij
    exact (pair_sign_iff_even_gap a ha S i j hi hj hij).mp
      (hp i ((hb i).mpr hi) j ((hb j).mpr hj))
  · intro hg i hi j hj
    have hiS := (hb i).mp hi
    have hjS := (hb j).mp hj
    rcases lt_trichotomy i j with hij | hij | hji
    · exact (pair_sign_iff_even_gap a ha S i j hiS hjS hij).mpr (hg i hiS j hjS hij)
    · subst j
      simpa only [pow_two] using sq_pos_of_ne_zero hi
    · have hp := (pair_sign_iff_even_gap a ha S j i hjS hiS hji).mpr (hg j hjS i hiS hji)
      simpa only [mul_comm] using hp

noncomputable def parityCatalogue (d m : ℕ) : Finset (Finset (Fin m)) := by
  classical
  exact (Finset.powersetCard d Finset.univ).filter EvenGaps

theorem catalogue_eq_parity {d m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (hm : d < m) : catalogue d a = parityCatalogue d m := by
  classical
  unfold catalogue parityCatalogue
  apply Finset.filter_congr
  intro S hS
  have hcard := (Finset.mem_powersetCard.mp hS).2
  exact root_filter_iff_even_gaps a ha S (by omega)

/-- The accepted numeric catalogue and all its geometric conclusions transfer
to a catalogue using only the ORIGINAL label order and a finite parity test. -/
theorem complete_even_catalogue {d m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (hm : d < m) :
    (∀ S ∈ parityCatalogue d m, mean a S ≠ 0 ∧
      ∀ i : Fin m, 0 ≤ (rootPoly a S).eval (a i) / mean a S) ∧
    Set.InjOn (candidate (d:=d) a) (parityCatalogue d m) ∧
    (∀ x : Fin d → ℝ,
      x ∈ ({y : Fin d → ℝ | ∀ i, row a y i ≤ 1}).extremePoints ℝ ↔
        x ∈ (parityCatalogue d m).image (candidate (d:=d) a)) ∧
    (∀ S ∈ parityCatalogue d m, ∀ i : Fin m,
      row a (candidate (d:=d) a S) i = 1 ↔ i ∈ S) ∧
    ((parityCatalogue d m).image (candidate (d:=d) a)).card = (parityCatalogue d m).card ∧
    (parityCatalogue d m).card ≤ Nat.choose m d := by
  classical
  have heq := catalogue_eq_parity a ha hm
  have hold := complete_catalogue a ha.injective hm
  rw [heq] at hold
  refine ⟨?_,hold⟩
  intro S hS
  rw [← heq] at hS
  exact ((mem_catalogue a S).mp hS).2

end Hirsch.MomentEvenGaps

/-- The classical Gale-evenness test gives a complete and duplicate-free
catalogue of ACTUAL vertices in the original mean-centered moment H system. -/
theorem solution (d m : ℕ) (hm : d < m) (a : Fin m → ℝ) (ha : StrictMono a) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let q : Finset (Fin m) → Polynomial ℝ :=
      fun S => ∏ i ∈ S, (Polynomial.X - Polynomial.C (a i))
    let μ : Finset (Fin m) → ℝ := fun S => (∑ i : Fin m, (q S).eval (a i)) / (m : ℝ)
    let v : Finset (Fin m) → (Fin d → ℝ) := fun S j => -(q S).coeff (j.val+1) / μ S
    let F : Finset (Finset (Fin m)) :=
      (Finset.powersetCard d Finset.univ).filter
        (fun S => ∀ i ∉ S, ∀ j ∉ S, i < j →
          (S.filter (fun s => i < s ∧ s < j)).card % 2 = 0)
    (∀ S ∈ F, μ S ≠ 0 ∧ ∀ i : Fin m, 0 ≤ (q S).eval (a i) / μ S) ∧
    Set.InjOn v F ∧
      (∀ x : Fin d → ℝ,
        x ∈ ({y | ∀ i, row y i ≤ 1}).extremePoints ℝ ↔ x ∈ F.image v) ∧
      (∀ S ∈ F, ∀ i : Fin m, row (v S) i = 1 ↔ i ∈ S) ∧
      (F.image v).card = F.card ∧ F.card ≤ Nat.choose m d := by
  exact Hirsch.MomentEvenGaps.complete_even_catalogue a ha hm

#print axioms Hirsch.MomentEvenGaps.pair_sign_iff_even_gap
#print axioms Hirsch.MomentEvenGaps.root_filter_iff_even_gaps
#print axioms Hirsch.MomentEvenGaps.catalogue_eq_parity
#print axioms Hirsch.MomentEvenGaps.complete_even_catalogue
#print axioms solution
