import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.HullCoordinate
open Set
variable {d : ℕ}

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

end Hirsch.HullCoordinate

namespace Hirsch.TargetRows
open Set
variable {d m : ℕ}

def body (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, A i x ≤ b i}

end Hirsch.TargetRows

namespace Hirsch.RadialRowEnvelope
open Set TargetRows
variable {d m : ℕ}

lemma extreme_not_in_other_segment (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v u w : Fin d → ℝ)
    (hv : v ∈ (body A b).extremePoints ℝ)
    (hu : u ∈ body A b) (hw : w ∈ body A b)
    (huv : u ≠ v) (hwv : w ≠ v) : v ∉ segment ℝ u w := by
  intro hs
  obtain ⟨a, c, ha, hc, hac, he⟩ := hs
  by_cases ha0 : a = 0
  · have hc1 : c = 1 := by linarith
    exact hwv (by simpa only [ha0, hc1, zero_smul, one_smul, zero_add] using he)
  by_cases hc0 : c = 0
  · have ha1 : a = 1 := by linarith
    exact huv (by simpa only [hc0, ha1, zero_smul, one_smul, add_zero] using he)
  have ho : v ∈ openSegment ℝ u w :=
    ⟨a, c, lt_of_le_of_ne ha (Ne.symm ha0), lt_of_le_of_ne hc (Ne.symm hc0), hac, he⟩
  exact huv (hv.2 hu hw ho)

end Hirsch.RadialRowEnvelope

namespace Hirsch.RowDeletionEdges

open Set TargetRows
variable {d m : ℕ}

/-- The whole affine line is retained, not just a pair of possibly lost vertices. -/
def affineLine (u w : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {z | ∃ t : ℝ, z = u + t • (w - u)}

def relaxed (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (keep : Fin m → Prop) : Set (Fin d → ℝ) :=
  {z | ∀ i, keep i → A i z ≤ b i}

lemma two_sided_feasible (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (x z : Fin d → ℝ) (hx : x ∈ body A b)
    (hz : ∀ i, A i x = b i → A i z = 0) :
    ∃ e : ℝ, 0 < e ∧ x + e • z ∈ body A b ∧ x - e • z ∈ body A b := by
  classical
  let S := Finset.univ.filter (fun i : Fin m => A i x ≠ b i)
  have hs : ∀ i ∈ S, 0 < b i - A i x := by
    intro i hi
    exact sub_pos.mpr (lt_of_le_of_ne (hx i) (Finset.mem_filter.mp hi).2)
  obtain ⟨e, he, hsmall⟩ := Hirsch.HullCoordinate.finite_margin S
    (fun i => b i - A i x) (fun i => A i z) hs
  have hall : ∀ i, A i (x + e • z) ≤ b i ∧ A i (x - e • z) ≤ b i := by
    intro i
    by_cases hi : A i x = b i
    · simp only [map_add, map_sub, map_smul, smul_eq_mul, hz i hi,
        mul_zero, add_zero, sub_zero]
      exact ⟨hx i, hx i⟩
    · have hsmall' := hsmall i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have hlo := mul_le_mul_of_nonneg_left (neg_abs_le (A i z)) he.le
      have hhi := mul_le_mul_of_nonneg_left (le_abs_self (A i z)) he.le
      simp only [map_add, map_sub, map_smul, smul_eq_mul]
      constructor <;> linarith
  exact ⟨e, he, (fun i => (hall i).1), (fun i => (hall i).2)⟩

/-- Derive the direction space of a genuine exposed segment from ALL its active
original equations. No active-rank or full-dimensionality premise. -/
lemma active_kernel_direction (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (u w z : Fin d → ℝ)
    (hE : IsExposed ℝ (body A b) (segment ℝ u w))
    (hz : ∀ i, A i ((1/2 : ℝ) • u + (1/2 : ℝ) • w) = b i → A i z = 0) :
    ∃ t : ℝ, z = t • (w - u) := by
  obtain ⟨f, hf⟩ := hE ⟨u, left_mem_segment ℝ u w⟩
  let x := (1/2 : ℝ) • u + (1/2 : ℝ) • w
  have hxseg : x ∈ segment ℝ u w :=
    ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hxF : x ∈ body A b ∧ ∀ y ∈ body A b, f y ≤ f x := by
    change x ∈ {y ∈ body A b | ∀ q ∈ body A b, f q ≤ f y}
    rw [← hf]
    exact hxseg
  obtain ⟨e, he, hp, hn⟩ := two_sided_feasible A b x z hxF.1 hz
  have hfp := hxF.2 (x + e • z) hp
  have hfn := hxF.2 (x - e • z) hn
  simp only [map_add, map_sub, map_smul, smul_eq_mul] at hfp hfn
  have hprod : e * f z = 0 := by linarith
  have hfz : f z = 0 := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt he)
  have hpseg : x + e • z ∈ segment ℝ u w := by
    rw [hf]
    refine ⟨hp, ?_⟩
    intro y hy
    simpa only [map_add, map_smul, smul_eq_mul, hfz, mul_zero, add_zero]
      using hxF.2 y hy
  obtain ⟨r, s, _hr, _hs, hrs, hpoint⟩ := hpseg
  have hr : r = 1 - s := by linarith
  have heq : e • z = (s - (1/2 : ℝ)) • (w - u) := by
    calc
      e • z = (x + e • z) - x := by abel
      _ = (r • u + s • w) - x := by rw [hpoint]
      _ = (s - (1/2 : ℝ)) • (w - u) := by rw [hr]; dsimp [x]; module
  refine ⟨(s - (1/2 : ℝ)) / e, ?_⟩
  calc
    z = (1/e) • (e • z) := by
      rw [smul_smul, div_mul_cancel₀ _ (ne_of_gt he), one_smul]
    _ = (1/e) • ((s - (1/2 : ℝ)) • (w - u)) := by rw [heq]
    _ = ((s - (1/2 : ℝ)) / e) • (w - u) := by
      rw [smul_smul]
      congr 1
      ring

/-- The original common-active equations define precisely the edge's affine
line, even when the original body is nonsimple or lower-dimensional. -/
theorem active_equations_iff_line (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (u w : Fin d → ℝ)
    (hu : u ∈ body A b) (hw : w ∈ body A b)
    (hE : IsExposed ℝ (body A b) (segment ℝ u w)) (y : Fin d → ℝ) :
    (∀ i, A i u = b i ∧ A i w = b i → A i y = b i) ↔ y ∈ affineLine u w := by
  constructor
  · intro hy
    let x := (1/2 : ℝ) • u + (1/2 : ℝ) • w
    have hz : ∀ i, A i x = b i → A i (y - x) = 0 := by
      intro i hi
      have hm : A i x = (A i u + A i w) / 2 := by
        dsimp [x]
        simp only [map_add, map_smul, smul_eq_mul]
        ring
      have hiu : A i u = b i := by linarith [hu i, hw i]
      have hiw : A i w = b i := by linarith [hu i, hw i]
      rw [map_sub, hy i ⟨hiu, hiw⟩, hi, sub_self]
    obtain ⟨t, ht⟩ := active_kernel_direction A b u w (y - x) hE hz
    refine ⟨(1/2 : ℝ) + t, ?_⟩
    calc
      y = x + (y - x) := by abel
      _ = x + t • (w - u) := by rw [ht]
      _ = u + ((1/2 : ℝ) + t) • (w - u) := by dsimp [x]; module
  · rintro ⟨t, rfl⟩ i ⟨hiu, hiw⟩
    simp only [map_add, map_smul, map_sub, smul_eq_mul, hiu, hiw,
      sub_self, mul_zero, add_zero]

/-- Summing common active ORIGINAL rows exposes their entire equality slice
in any relaxation that retains them. No supporting functional is supplied. -/
lemma common_slice_exposed (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (u w : Fin d → ℝ) (keep : Fin m → Prop)
    (hu : u ∈ body A b)
    (hkeep : ∀ i, A i u = b i ∧ A i w = b i → keep i) :
    IsExposed ℝ (relaxed A b keep)
      {z ∈ relaxed A b keep | ∀ i, A i u = b i ∧ A i w = b i → A i z = b i} := by
  classical
  let T := Finset.univ.filter (fun i : Fin m => A i u = b i ∧ A i w = b i)
  let f : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => ∑ i ∈ T, A i z
      map_add' := by
        intro x y
        simp only [map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [map_smul, smul_eq_mul, Finset.mul_sum]
        rfl }
  have hle : ∀ z ∈ relaxed A b keep, ∀ i ∈ T, A i z ≤ A i u := by
    intro z hz i hi
    have ht := (Finset.mem_filter.mp hi).2
    rw [ht.1]
    exact hz i (hkeep i ht)
  have hbound : ∀ z ∈ relaxed A b keep, f z ≤ f u := by
    intro z hz
    exact Finset.sum_le_sum (hle z hz)
  have huQ : u ∈ relaxed A b keep := fun i _ => hu i
  intro _
  refine ⟨f.toContinuousLinearMap, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, heq⟩
    have hfz : f z = f u := by
      change (∑ i ∈ T, A i z) = ∑ i ∈ T, A i u
      apply Finset.sum_congr rfl
      intro i hi
      have ht := (Finset.mem_filter.mp hi).2
      rw [heq i ht, ht.1]
    refine ⟨hz, ?_⟩
    intro y hy
    change f y ≤ f z
    rw [hfz]
    exact hbound y hy
  · rintro ⟨hz, hmax⟩
    have hlo : f u ≤ f z := hmax u huQ
    have hfz : f z = f u := le_antisymm (hbound z hz) hlo
    refine ⟨hz, ?_⟩
    intro i hi
    have himem : i ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have hsum : (∑ j ∈ T, (A j u - A j z)) = 0 := by
      rw [Finset.sum_sub_distrib]
      change f u - f z = 0
      rw [hfz, sub_self]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => sub_nonneg.mpr (hle z hz j hj))).mp hsum i himem
    exact (sub_eq_zero.mp hzero).symm.trans hi.1


/-- An original exposed edge is the WHOLE intersection of its supporting line
with the original body. This is not merely feasibility of its endpoints. -/
lemma original_line_inter (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (u w : Fin d → ℝ)
    (hE : IsExposed ℝ (body A b) (segment ℝ u w)) :
    body A b ∩ affineLine u w = segment ℝ u w := by
  obtain ⟨f, hf⟩ := hE ⟨u, left_mem_segment ℝ u w⟩
  have huF : u ∈ body A b ∧ ∀ y ∈ body A b, f y ≤ f u := by
    change u ∈ {x ∈ body A b | ∀ y ∈ body A b, f y ≤ f x}
    rw [← hf]
    exact left_mem_segment ℝ u w
  have hwF : w ∈ body A b ∧ ∀ y ∈ body A b, f y ≤ f w := by
    change w ∈ {x ∈ body A b | ∀ y ∈ body A b, f y ≤ f x}
    rw [← hf]
    exact right_mem_segment ℝ u w
  have hfw : f w = f u := le_antisymm (huF.2 w hwF.1) (hwF.2 u huF.1)
  ext z
  constructor
  · rintro ⟨hz, t, rfl⟩
    rw [hf]
    refine ⟨hz, ?_⟩
    intro y hy
    simpa only [map_add, map_smul, map_sub, smul_eq_mul, hfw,
      sub_self, mul_zero, add_zero] using huF.2 y hy
  · intro hz
    have hzP : z ∈ body A b := hE.subset hz
    refine ⟨hzP, ?_⟩
    obtain ⟨r, s, _hr, _hs, hrs, heq⟩ := hz
    have hr : r = 1 - s := by linarith
    refine ⟨s, ?_⟩
    rw [← heq, hr]
    module

/-- Retained active rows preserve the entire one-dimensional exposed carrier;
reinsertion recovers exactly the original edge, without preserving endpoints. -/
theorem retained_edge_extension (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (u w : Fin d → ℝ) (keep : Fin m → Prop)
    (hu : u ∈ body A b) (hw : w ∈ body A b)
    (hE : IsExposed ℝ (body A b) (segment ℝ u w))
    (hkeep : ∀ i, A i u = b i ∧ A i w = b i → keep i) :
    IsExposed ℝ (relaxed A b keep) (relaxed A b keep ∩ affineLine u w) ∧
      body A b ∩ (relaxed A b keep ∩ affineLine u w) = segment ℝ u w ∧
      segment ℝ u w ⊆ relaxed A b keep ∩ affineLine u w := by
  have hsets : {z ∈ relaxed A b keep |
      ∀ i, A i u = b i ∧ A i w = b i → A i z = b i} =
      relaxed A b keep ∩ affineLine u w := by
    ext z
    exact and_congr_right (fun _ => active_equations_iff_line A b u w hu hw hE z)
  have hexp := common_slice_exposed A b u w keep hu hkeep
  rw [hsets] at hexp
  have hsub : body A b ⊆ relaxed A b keep := fun _ hz i _ => hz i
  have hrec : body A b ∩ (relaxed A b keep ∩ affineLine u w) = segment ℝ u w := by
    rw [← original_line_inter A b u w hE]
    ext z
    constructor
    · rintro ⟨hz, _, hl⟩
      exact ⟨hz, hl⟩
    · rintro ⟨hz, hl⟩
      exact ⟨hz, hsub hz, hl⟩
  refine ⟨hexp, hrec, ?_⟩
  intro z hz
  rw [← hrec] at hz
  exact hz.2

lemma line_parameter_injective (u w : Fin d → ℝ) (huw : u ≠ w) :
    Function.Injective (fun t : ℝ => u + t • (w - u)) := by
  classical
  have hex : ∃ j, u j ≠ w j := by
    by_contra hn
    apply huw
    funext j
    by_contra hj
    exact hn ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  intro a b hab
  have hh := congrFun hab j
  change u j + a * (w j - u j) = u j + b * (w j - u j) at hh
  have hp : (a - b) * (w j - u j) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr (Ne.symm hj)))

end Hirsch.RowDeletionEdges

namespace Hirsch.ForcedRuns

open Set TargetRows RowDeletionEdges
variable {d m : ℕ}

lemma affineLine_symm (u w : Fin d → ℝ) : affineLine u w = affineLine w u := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨1-t, by module⟩
  · rintro ⟨t, rfl⟩
    exact ⟨1-t, by module⟩

/-- Two original edge lines meeting at a vertex cannot share a second point
when their other original vertices differ. No relaxed rank premise. -/
lemma edge_lines_meet_only (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (a x c : Fin d → ℝ)
    (ha : a ∈ (body A b).extremePoints ℝ)
    (hx : x ∈ body A b) (hc : c ∈ body A b)
    (hax : a ≠ x) (hac : a ≠ c)
    (hE : IsExposed ℝ (body A b) (segment ℝ x c))
    (z : Fin d → ℝ) (hz1 : z ∈ affineLine a x) (hz2 : z ∈ affineLine x c) : z = x := by
  rw [affineLine_symm a x] at hz1
  obtain ⟨s, hs⟩ := hz1
  obtain ⟨t, ht⟩ := hz2
  by_contra hzx
  have hs0 : s ≠ 0 := by
    intro he
    exact hzx (by simpa only [he, zero_smul, add_zero] using hs)
  have hdir : s • (a-x) = t • (c-x) := add_left_cancel (hs.symm.trans ht)
  have haDir : a-x = (t/s) • (c-x) := by
    calc
      a-x = (1/s) • (s • (a-x)) := by
        rw [smul_smul, div_mul_cancel₀ _ hs0, one_smul]
      _ = (1/s) • (t • (c-x)) := by rw [hdir]
      _ = (t/s) • (c-x) := by
        rw [smul_smul]
        congr 1
        ring
  have haLine : a ∈ affineLine x c := by
    refine ⟨t/s, ?_⟩
    rw [← haDir]
    abel
  have haSeg : a ∈ segment ℝ x c := by
    rw [← original_line_inter A b x c hE]
    exact ⟨ha.1, haLine⟩
  exact (Hirsch.RadialRowEnvelope.extreme_not_in_other_segment A b a x c
    ha hx hc (Ne.symm hax) (Ne.symm hac)) haSeg

/-- The junction of two distinct forced edges is itself exposed in the
relaxation; its old vertex does not disappear. -/
theorem junction_exposed (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (Q : Set (Fin d → ℝ)) (a x c : Fin d → ℝ)
    (ha : a ∈ (body A b).extremePoints ℝ)
    (hx : x ∈ body A b) (hc : c ∈ body A b) (hxQ : x ∈ Q)
    (hax : a ≠ x) (hac : a ≠ c)
    (hE : IsExposed ℝ (body A b) (segment ℝ x c))
    (hL : IsExposed ℝ Q (Q ∩ affineLine a x))
    (hR : IsExposed ℝ Q (Q ∩ affineLine x c)) : IsExposed ℝ Q {x} := by
  have heq : (Q ∩ affineLine a x) ∩ (Q ∩ affineLine x c) = {x} := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      exact Set.mem_singleton_iff.mpr
        (edge_lines_meet_only A b a x c ha hx hc hax hac hE z hz1.2 hz2.2)
    · intro hz
      have hz' : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨hxQ, ⟨1, by module⟩⟩, ⟨hxQ, ⟨0, by simp⟩⟩⟩
  have he := hL.inter hR
  rwa [heq] at he

/-- A line section cannot extend past either of its two extreme endpoints. -/
lemma extreme_section_subset (Q : Set (Fin d → ℝ)) (u w : Fin d → ℝ)
    (hu : u ∈ Q.extremePoints ℝ) (hw : w ∈ Q.extremePoints ℝ) (huw : u ≠ w) :
    Q ∩ affineLine u w ⊆ segment ℝ u w := by
  rintro z ⟨hz, t, rfl⟩
  have ht0 : 0 ≤ t := by
    by_contra hn
    have ht : t < 0 := lt_of_not_ge hn
    have hd : 0 < 1-t := by linarith
    have hsum : (-t)/(1-t) + 1/(1-t) = (1:ℝ) := by
      field_simp [ne_of_gt hd] <;> ring
    have hpoint : ((-t)/(1-t)) • w + (1/(1-t)) • (u + t • (w-u)) = u := by
      funext j
      change ((-t)/(1-t)) * w j + (1/(1-t)) * (u j+t*(w j-u j)) = u j
      field_simp [ne_of_gt hd] <;> ring
    have ho : u ∈ openSegment ℝ w (u+t • (w-u)) :=
      ⟨(-t)/(1-t), 1/(1-t), div_pos (neg_pos.mpr ht) hd,
        div_pos (by norm_num) hd, hsum, hpoint⟩
    exact huw (hu.2 hw.1 hz ho).symm
  have ht1 : t ≤ 1 := by
    by_contra hn
    have ht : 1 < t := lt_of_not_ge hn
    have htp : 0 < t := by linarith
    have hsum : (t-1)/t + 1/t = (1:ℝ) := by
      field_simp [ne_of_gt htp] <;> ring
    have hpoint : ((t-1)/t) • u + (1/t) • (u+t • (w-u)) = w := by
      funext j
      change ((t-1)/t) * u j + (1/t) * (u j+t*(w j-u j)) = w j
      field_simp [ne_of_gt htp] <;> ring
    have ho : w ∈ openSegment ℝ u (u+t • (w-u)) :=
      ⟨(t-1)/t, 1/t, div_pos (sub_pos.mpr ht) htp,
        div_pos (by norm_num) htp, hsum, hpoint⟩
    exact huw (hw.2 hu.1 hz ho)
  exact ⟨1-t, t, sub_nonneg.mpr ht1, ht0, by ring, by module⟩

/-- A forced run loses no internal vertices, and its middle edges remain
exactly the original exposed segments. Only its two boundary edges can extend. -/
theorem run_survival (n : ℕ) (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (b : Fin m → ℝ) (v : Fin d → ℝ) (hv : v ∈ body A b)
    (J : Finset (Fin m)) (p : Fin (n+3) → (Fin d → ℝ))
    (hp : ∀ i, p i ∈ (body A b).extremePoints ℝ) (hinj : Function.Injective p)
    (hE : ∀ i : Fin (n+2), IsExposed ℝ (body A b) (segment ℝ (p i.castSucc) (p i.succ)))
    (hforced : ∀ (t : Fin (n+2)) i, A i v < b i → A i (p t.castSucc) = b i →
      A i (p t.succ) = b i → i ∈ J) :
    let Q := relaxed A b (fun i => A i v = b i ∨ i ∈ J)
    let r := fun i : Fin (n+1) => p i.succ.castSucc
    Function.Injective r ∧
    (∀ i, r i ∈ Q.extremePoints ℝ ∧ IsExposed ℝ Q {r i}) ∧
    (∀ i : Fin n, IsExposed ℝ Q (segment ℝ (r i.castSucc) (r i.succ)) ∧
      Q ∩ affineLine (r i.castSucc) (r i.succ) = segment ℝ (r i.castSucc) (r i.succ)) ∧
    (∀ i : Fin (n+2), Q ∩ affineLine (p i.castSucc) (p i.succ) ≠
      segment ℝ (p i.castSucc) (p i.succ) → i.val = 0 ∨ i.val = n+1) := by
  classical
  intro Q r
  have hPQ : body A b ⊆ Q := fun _ hz i _ => hz i
  have hall : ∀ i : Fin (n+2),
      IsExposed ℝ Q (Q ∩ affineLine (p i.castSucc) (p i.succ)) ∧
      segment ℝ (p i.castSucc) (p i.succ) ⊆ Q ∩ affineLine (p i.castSucc) (p i.succ) := by
    intro t
    have hkeep : ∀ i, A i (p t.castSucc) = b i ∧ A i (p t.succ) = b i →
        A i v = b i ∨ i ∈ J := by
      intro i hi
      by_cases hvi : A i v = b i
      · exact Or.inl hvi
      · exact Or.inr (hforced t i (lt_of_le_of_ne (hv i) hvi) hi.1 hi.2)
    have hh := retained_edge_extension A b (p t.castSucc) (p t.succ)
      (fun i => A i v = b i ∨ i ∈ J) (hp _).1 (hp _).1 (hE t) hkeep
    exact ⟨hh.1, hh.2.2⟩
  have hpoint : ∀ k : Fin (n+3), 0 < k.val → k.val < n+2 →
      p k ∈ Q.extremePoints ℝ ∧ IsExposed ℝ Q {p k} := by
    intro k hk0 hkN
    let l : Fin (n+2) := ⟨k.val-1, by omega⟩
    let j : Fin (n+2) := ⟨k.val, hkN⟩
    have hl : l.succ = k := by apply Fin.ext; change k.val-1+1=k.val; omega
    have hj : j.castSucc = k := by apply Fin.ext; rfl
    have hax : p l.castSucc ≠ p k := by
      intro he
      have hh := congrArg Fin.val (hinj he)
      change k.val-1 = k.val at hh
      omega
    have hac : p l.castSucc ≠ p j.succ := by
      intro he
      have hh := congrArg Fin.val (hinj he)
      change k.val-1 = k.val+1 at hh
      omega
    have hleft : IsExposed ℝ Q (Q ∩ affineLine (p l.castSucc) (p k)) := by
      simpa only [hl] using (hall l).1
    have hright : IsExposed ℝ Q (Q ∩ affineLine (p k) (p j.succ)) := by
      simpa only [hj] using (hall j).1
    have he := junction_exposed A b Q (p l.castSucc) (p k) (p j.succ)
      (hp _) (hp _).1 (hp _).1 (hPQ (hp k).1) hax hac
      (by simpa only [hj] using hE j) hleft hright
    exact ⟨he.isExtreme.mem_extremePoints, he⟩
  have hmiddle : ∀ i : Fin (n+2), 0 < i.val → i.val < n+1 →
      Q ∩ affineLine (p i.castSucc) (p i.succ) = segment ℝ (p i.castSucc) (p i.succ) := by
    intro i hi0 hiN
    have hiu := (hpoint i.castSucc hi0 (by change i.val < n+2; omega)).1
    have hiw := (hpoint i.succ (by change 0 < i.val+1; omega)
      (by change i.val+1 < n+2; omega)).1
    have hne : p i.castSucc ≠ p i.succ := by
      intro he
      have hh := congrArg Fin.val (hinj he)
      change i.val = i.val+1 at hh
      omega
    exact Set.Subset.antisymm (extreme_section_subset Q _ _ hiu hiw hne) (hall i).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j he
    have hh := congrArg Fin.val (hinj he)
    apply Fin.ext
    change i.val+1 = j.val+1 at hh
    omega
  · intro i
    exact hpoint i.succ.castSucc (by change 0 < i.val+1; omega)
      (by have hh := i.isLt; change i.val+1 < n+2; omega)
  · intro i
    let j : Fin (n+2) := ⟨i.val+1, by have hh := i.isLt; omega⟩
    have hj0 : 0 < j.val := by change 0 < i.val+1; omega
    have hjN : j.val < n+1 := by have hh := i.isLt; change i.val+1 < n+1; omega
    have heq := hmiddle j hj0 hjN
    have hexp := (hall j).1
    rw [heq] at hexp
    exact ⟨hexp, heq⟩
  · intro i hi
    by_cases h0 : i.val = 0
    · exact Or.inl h0
    by_cases hN : i.val = n+1
    · exact Or.inr hN
    have hil : i.val < n+1 := by have hh := i.isLt; omega
    exact False.elim (hi (hmiddle i (by omega) hil))

end Hirsch.ForcedRuns

/-- Trim just the two boundary edges of a simple Hall-forced original run to
obtain an unchanged simple ordinary-edge path in the original-row relaxation. -/
theorem solution (d m n : ℕ)
    (A : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (v : Fin d → ℝ)
    (hv : v ∈ ({x | ∀ i, A i x ≤ b i} : Set (Fin d → ℝ)).extremePoints ℝ)
    (J : Finset (Fin m)) (p : Fin (n+3) → (Fin d → ℝ))
    (hp : ∀ i, p i ∈ ({x | ∀ j, A j x ≤ b j} : Set (Fin d → ℝ)).extremePoints ℝ)
    (hinj : Function.Injective p) (hnv : ∀ i, p i ≠ v)
    (hE : ∀ i : Fin (n+2), IsExposed ℝ {x : Fin d → ℝ | ∀ j, A j x ≤ b j}
      (segment ℝ (p i.castSucc) (p i.succ)))
    (hforced : ∀ (t : Fin (n+2)) i, A i v < b i → A i (p t.castSucc) = b i →
      A i (p t.succ) = b i → i ∈ J) :
    let Q : Set (Fin d → ℝ) := {x | ∀ i, A i v = b i ∨ i ∈ J → A i x ≤ b i}
    let r := fun i : Fin (n+1) => p i.succ.castSucc
    Function.Injective r ∧
    (∀ i, r i ∈ Q.extremePoints ℝ ∧ IsExposed ℝ Q {r i}) ∧
    (∀ i : Fin n, IsExposed ℝ Q (segment ℝ (r i.castSucc) (r i.succ)) ∧
      Q ∩ {x | ∃ s : ℝ, x = r i.castSucc + s • (r i.succ - r i.castSucc)} =
        segment ℝ (r i.castSucc) (r i.succ)) ∧
    (∀ i : Fin (n+2), Q ∩ {x | ∃ s : ℝ, x = p i.castSucc + s • (p i.succ - p i.castSucc)} ≠
      segment ℝ (p i.castSucc) (p i.succ) → i.val = 0 ∨ i.val = n+1) := by
  exact Hirsch.ForcedRuns.run_survival n A b v hv.1 J p hp hinj hE hforced

#print axioms Hirsch.ForcedRuns.edge_lines_meet_only
#print axioms Hirsch.ForcedRuns.junction_exposed
#print axioms Hirsch.ForcedRuns.extreme_section_subset
#print axioms Hirsch.ForcedRuns.run_survival
#print axioms solution
