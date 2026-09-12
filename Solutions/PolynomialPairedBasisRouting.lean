import Definitions.Def_Hirsch_model
import Solutions.PolynomialRegionRouting

/-!
# Ordinary-edge routing from complementary affine bases

The hypotheses are linear equations and feasibility, not a graph-isomorphism
or a diameter premise. PolynomialPositiveFeedbackBoxes discharges them using
one positive vector. New proof candidate: separate pinned Lean gate required.
-/
open Set Hirsch HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace HirschPairedBases

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Vec (ι : Type*) := ι → ℝ

def pairedPoly (L : Vec ι →ₗ[ℝ] Vec ι) (b : Vec ι) : Set (Vec ι) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i, L x i ≤ b i}

def rhs (b : Vec ι) (s : ι → Bool) : Vec ι := fun i => if s i then b i else 0

/-- Each binary choice selects the lower equality x_i=0 or the upper equality
(Lx)_i=b_i. Every selected system is invertible, its solution is feasible,
and opposite equalities never hold at the same feasible point. -/
structure PairedBasisModel (L : Vec ι →ₗ[ℝ] Vec ι) (b : Vec ι) where
  basis : (ι → Bool) → Vec ι ≃ₗ[ℝ] Vec ι
  basis_spec : ∀ s x i, basis s x i = if s i then L x i else x i
  feasible : ∀ s, (basis s).symm (rhs b s) ∈ pairedPoly L b
  no_double : ∀ x ∈ pairedPoly L b, ∀ i, x i = 0 → L x i < b i

namespace PairedBasisModel
variable {L : Vec ι →ₗ[ℝ] Vec ι} {b : Vec ι}
variable (m : PairedBasisModel L b)

def point (s : ι → Bool) : Vec ι := (m.basis s).symm (rhs b s)

lemma point_mem (s : ι → Bool) : m.point s ∈ pairedPoly L b := m.feasible s

lemma point_equations (s : ι → Bool) (i : ι) :
    (if s i then L (m.point s) i else m.point s i) = rhs b s i := by
  rw [← m.basis_spec]
  exact congrFun ((m.basis s).apply_symm_apply (rhs b s)) i

lemma point_zero (s : ι → Bool) (i : ι) (hi : s i = false) : m.point s i = 0 := by
  simpa [hi, rhs] using m.point_equations s i

lemma point_upper (s : ι → Bool) (i : ι) (hi : s i = true) : L (m.point s) i = b i := by
  simpa [hi, rhs] using m.point_equations s i

lemma point_pos (s : ι → Bool) (i : ι) (hi : s i = true) : 0 < m.point s i := by
  have hp := (m.point_mem s).1 i
  have he := m.point_upper s i hi
  by_contra hn
  have hz : m.point s i = 0 := by linarith
  have hlt := m.no_double _ (m.point_mem s) i hz
  linarith

lemma point_injective : Function.Injective m.point := by
  intro s t he
  funext i
  by_contra hn
  cases hs : s i <;> cases ht : t i
  · exact hn (hs.trans ht.symm)
  · have hz := m.point_zero s i hs
    have hp := m.point_pos t i ht
    rw [he] at hz
    linarith
  · have hp := m.point_pos s i hs
    have hz := m.point_zero t i ht
    rw [he] at hp
    linarith
  · exact hn (hs.trans ht.symm)

/-- An equality at an interior point of a segment, bounded above at both
endpoints, is an equality at the first endpoint. -/
private lemma active_scalar {a c p q B : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hp : p ≤ B) (hq : q ≤ B) (he : a*p+c*q=B) : p = B := by
  by_contra hn
  have hlt : p < B := lt_of_le_of_ne hp hn
  have h1 := mul_lt_mul_of_pos_left hlt ha
  have h2 := mul_le_mul_of_nonneg_left hq hc
  nlinarith

lemma pairedPoly_convex : Convex ℝ (pairedPoly L b) := by
  intro x hx y hy a c ha hc hac
  constructor
  · intro i
    change 0 ≤ a*x i+c*y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hc (hy.1 i))
  · intro i
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hx.2 i) ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 i) hc
    nlinarith

lemma point_extreme (s : ι → Bool) : m.point s ∈ extremePoints ℝ (pairedPoly L b) := by
  refine ⟨m.point_mem s, ?_⟩
  intro p hp q hq hseg
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  apply (m.basis s).injective
  funext i
  rw [m.basis_spec, m.basis_spec]
  cases hs : s i
  · have he0 := m.point_zero s i hs
    have he := congrFun hcomb i
    change a*p i+c*q i=m.point s i at he
    have hp0 : p i = 0 := by
      have ht := active_scalar ha hc.le hac (neg_nonpos.mpr (hp.1 i))
        (neg_nonpos.mpr (hq.1 i)) (show a*(-p i)+c*(-q i)=0 by nlinarith)
      linarith
    simpa [hs, hp0, he0]
  · have hu := m.point_upper s i hs
    have he := congrFun (congrArg L hcomb) i
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he
    have ht := active_scalar ha hc.le hac (hp.2 i) (hq.2 i) (he.trans hu)
    simpa [hs, ht, hu]

/-- Generic finite perturbation lemma, parallel to the repository's Euclidean
vertex-span proof. No topology or imported theorem placeholder is needed. -/
private lemma finite_linear_vertex_span {R E : Type*} [Fintype R]
    [AddCommGroup E] [Module ℝ E]
    (a : R → E →ₗ[ℝ] ℝ) (B : R → ℝ)
    (x : E) (hx : x ∈ extremePoints ℝ {z | ∀ r, a r z ≤ B r})
    (y : E) (horth : ∀ r, a r x = B r → a r y = 0) : y = 0 := by
  classical
  have hlocal : ∀ r : R, ∃ t : ℝ, 0 < t ∧ t * |a r y| ≤ B r - a r x := by
    intro r
    by_cases hr : a r x = B r
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [horth r hr, abs_zero, mul_zero, hr, sub_self]
    · have hs : 0 < B r - a r x := sub_pos.mpr (lt_of_le_of_ne (hx.1 r) hr)
      have hd : 0 < |a r y| + 1 := by positivity
      let t := (B r-a r x)/(|a r y|+1)
      have ht : 0 < t := div_pos hs hd
      have he : t*(|a r y|+1)=B r-a r x := div_mul_cancel₀ _ (ne_of_gt hd)
      exact ⟨t,ht,by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset R, ∃ t : ℝ, 0 < t ∧ ∀ r ∈ S, t ≤ e r := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert r S hr ih =>
      obtain ⟨t,ht,hte⟩ := ih
      refine ⟨min (e r) t,lt_min (hepos r) ht,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with heq | hj
      · subst j; exact min_le_left _ _
      · exact (min_le_right _ _).trans (hte j hj)
  obtain ⟨t,ht,hte⟩ := huniform Finset.univ
  have hbudget : ∀ r, t*|a r y| ≤ B r-a r x := fun r =>
    (mul_le_mul_of_nonneg_right (hte r (Finset.mem_univ r)) (abs_nonneg _)).trans (hebound r)
  have hp : ∀ r, a r (x+t•y) ≤ B r := by
    intro r
    simp only [map_add,map_smul,smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left (le_abs_self (a r y)) ht.le
    linarith [hbudget r]
  have hm : ∀ r, a r (x-t•y) ≤ B r := by
    intro r
    simp only [map_sub,map_smul,smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left (neg_le_abs (a r y)) ht.le
    linarith [hbudget r]
  have hmid : x ∈ openSegment ℝ (x+t•y) (x-t•y) := by
    refine ⟨(1/2:ℝ),(1/2:ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    module
  have heq := hx.2 hp hm hmid
  have hz : t•y=0 := by
    have h := congrArg (fun z => z-x) heq
    simpa using h
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt ht)

def lowerRow (i : ι) : Vec ι →ₗ[ℝ] ℝ where
  toFun x := -x i
  map_add' x y := by simp
  map_smul' a x := by simp

def upperRow (i : ι) : Vec ι →ₗ[ℝ] ℝ where
  toFun x := L x i
  map_add' x y := by simp
  map_smul' a x := by simp

/-- No extra vertices are silently omitted. A vertex with both inequalities
slack in one pair admits a nonzero two-sided feasible perturbation. -/
theorem extreme_eq_point (x : Vec ι) (hx : x ∈ extremePoints ℝ (pairedPoly L b)) :
    ∃ s, x = m.point s := by
  classical
  let s : ι → Bool := fun i => decide (L x i = b i)
  have hzero : ∀ i, s i = false → x i = 0 := by
    intro i hi
    have hnot : L x i ≠ b i := by simpa [s] using hi
    by_contra hxi
    let y := (m.basis s).symm (Pi.single i 1)
    have hby : m.basis s y = Pi.single i 1 := (m.basis s).apply_symm_apply _
    let a : Sum ι ι → Vec ι →ₗ[ℝ] ℝ := Sum.elim lowerRow (upperRow (L:=L))
    let B : Sum ι ι → ℝ := Sum.elim (fun _ => 0) b
    have hP : {z | ∀ r, a r z ≤ B r} = pairedPoly L b := by
      ext z
      simp [a,B,pairedPoly,lowerRow,upperRow,Sum.forall,neg_nonpos]
    have hx' : x ∈ extremePoints ℝ {z | ∀ r, a r z ≤ B r} := by rwa [hP]
    have hy0 : y = 0 := by
      apply finite_linear_vertex_span a B x hx' y
      intro r hr
      cases r with
      | inl j =>
        have hxj : x j = 0 := by change -x j=0 at hr; linarith
        have hji : j ≠ i := by intro he; subst j; exact hxi hxj
        have hs : s j = false := by
          have hlt := m.no_double x hx.1 j hxj
          simp [s,ne_of_lt hlt]
        have hj := congrFun hby j
        rw [m.basis_spec] at hj
        have hz : y j=0 := by simpa [hs,Pi.single_apply,hji] using hj
        change -y j=0
        simp [hz]
      | inr j =>
        have hxj : L x j=b j := hr
        have hji : j ≠ i := by intro he; subst j; exact hnot hxj
        have hs : s j=true := by simp [s,hxj]
        have hj := congrFun hby j
        rw [m.basis_spec] at hj
        change L y j=0
        simpa [hs,Pi.single_apply,hji] using hj
    have hbad := congrFun hby i
    rw [hy0,map_zero] at hbad
    norm_num at hbad
  refine ⟨s,?_⟩
  apply (m.basis s).injective
  rw [show m.basis s (m.point s)=rhs b s from (m.basis s).apply_symm_apply _]
  funext i
  rw [m.basis_spec]
  cases hi : s i
  · simpa [hi,rhs] using hzero i hi
  · have ht : L x i=b i := by simpa [s] using hi
    simp [hi,rhs,ht]

/-- The equations retained in a one-bit change define an extreme subset. -/
lemma shared_equations_extreme (s : ι → Bool) (i : ι) :
    IsExtreme ℝ (pairedPoly L b)
      {z | z ∈ pairedPoly L b ∧ ∀ j, j ≠ i → m.basis s z j=rhs b s j} := by
  refine ⟨fun z hz => hz.1,?_⟩
  intro p hp q hq z hz hseg
  refine ⟨hp,?_⟩
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  intro j hji
  have hez := hz.2 j hji
  rw [m.basis_spec] at hez
  rw [m.basis_spec]
  cases hs : s j
  · have hz0 : z j=0 := by simpa [hs,rhs] using hez
    have he := congrFun hcomb j
    change a*p j+c*q j=z j at he
    have ht := active_scalar ha hc.le hac (neg_nonpos.mpr (hp.1 j))
      (neg_nonpos.mpr (hq.1 j)) (show a*(-p j)+c*(-q j)=0 by nlinarith)
    have hp0 : p j=0 := by linarith
    simp [hs,rhs,hp0]
  · have hzt : L z j=b j := by simpa [hs,rhs] using hez
    have he := congrFun (congrArg L hcomb) j
    simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at he
    have ht := active_scalar ha hc.le hac (hp.2 j) (hq.2 j) (he.trans hzt)
    simp [hs,rhs,ht]

/-- A binary pivot is an ORDINARY EDGE. Other coordinates may move too; this
is not a coordinate-axis step or a circuit step. -/
theorem point_adj_update (s : ι → Bool) (i : ι) (hi : s i=false) :
    Adj (pairedPoly L b) (m.point s) (m.point (Function.update s i true)) := by
  classical
  let t := Function.update s i true
  let p := m.point s
  let q := m.point t
  have hp := m.point_mem s
  have hq := m.point_mem t
  have hp0 : p i=0 := m.point_zero s i hi
  have hqpos : 0<q i := m.point_pos t i (by simp [t])
  have hqtop : L q i=b i := m.point_upper t i (by simp [t])
  have hpstrict : L p i<b i := m.no_double p hp i hp0
  let F : Set (Vec ι) :=
    {z | z ∈ pairedPoly L b ∧ ∀ j, j ≠ i → m.basis s z j=rhs b s j}
  have hpF : p ∈ F := by
    refine ⟨hp,?_⟩
    intro j _
    exact congrFun ((m.basis s).apply_symm_apply _) j
  have hqF : q ∈ F := by
    refine ⟨hq,?_⟩
    intro j hji
    have ht := m.point_equations t j
    rw [m.basis_spec]
    simpa [t,Function.update_noteq hji,rhs] using ht
  have hFext : IsExtreme ℝ (pairedPoly L b) F := m.shared_equations_extreme s i
  have hFseg : F = segment ℝ p q := by
    apply Set.Subset.antisymm
    · intro z hz
      let theta : ℝ := z i/q i
      have htheta0 : 0≤theta := div_nonneg (hz.1.1 i) hqpos.le
      have hthetaq : theta*q i=z i := div_mul_cancel₀ _ (ne_of_gt hqpos)
      have hzcomb : (1-theta)•p+theta•q=z := by
        apply (m.basis s).injective
        funext j
        by_cases hji : j=i
        · subst j
          simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
          rw [m.basis_spec,m.basis_spec,m.basis_spec]
          simp [hi,hp0,hthetaq]
        · have h1 := hpF.2 j hji
          have h2 := hqF.2 j hji
          have h3 := hz.2 j hji
          simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
          rw [h1,h2,h3]
          ring
      have hl := congrFun (congrArg L hzcomb) i
      simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hl
      have htheta1 : theta≤1 := by
        have hbound := hz.1.2 i
        rw [hqtop] at hl
        nlinarith
      exact ⟨1-theta,theta,sub_nonneg.mpr htheta1,htheta0,by ring,hzcomb⟩
    · intro z hz
      obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hz
      refine ⟨?_,?_⟩
      · rw [←hcomb]
        exact pairedPoly_convex hp hq ha hc hac
      · intro j hji
        rw [←hcomb]
        simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
        rw [hpF.2 j hji,hqF.2 j hji]
        nlinarith
  refine ⟨?_,?_⟩
  · intro he
    have he' := congrFun he i
    change p i=q i at he'
    linarith
  · change IsExtreme ℝ (pairedPoly L b) (segment ℝ p q)
    rwa [hFseg] at hFext

lemma point_adj_of_single_change (s t : ι → Bool) (i : ι)
    (hi : s i ≠ t i) (hrest : ∀ j, j ≠ i → s j=t j) :
    Adj (pairedPoly L b) (m.point s) (m.point t) := by
  classical
  cases hs : s i <;> cases ht : t i
  · exact False.elim (hi (hs.trans ht.symm))
  · have he : Function.update s i true=t := by
      funext j
      by_cases hj : j=i
      · subst j; simp [ht]
      · simp [hj,hrest j hj]
    simpa [he] using m.point_adj_update s i hs
  · have he : Function.update t i true=s := by
      funext j
      by_cases hj : j=i
      · subst j; simp [hs]
      · simp [hj,(hrest j hj).symm]
    have h := m.point_adj_update t i ht
    rw [he] at h
    exact ⟨h.1.symm,by rw [segment_symm]; exact h.2⟩
  · exact False.elim (hi (hs.trans ht.symm))

end PairedBasisModel

/-- Process the coordinate labels in order, changing each at most once. -/
theorem paired_basis_diamLE {d : ℕ}
    {L : Vec (Fin d) →ₗ[ℝ] Vec (Fin d)} {b : Vec (Fin d)}
    (m : PairedBasisModel L b) : DiamLE (pairedPoly L b) d := by
  intro x hx y hy
  obtain ⟨s,rfl⟩ := m.extreme_eq_point x hx
  obtain ⟨t,rfl⟩ := m.extreme_eq_point y hy
  let sig : ℕ → Fin d → Bool := fun k j => if j.val<k then t j else s j
  have h0 : sig 0=s := by funext j; simp [sig]
  have hd : sig d=t := by funext j; simp [sig,j.isLt]
  refine ⟨fun k => m.point (sig k),by rw [h0],by rw [hd],?_⟩
  intro k hk
  let i : Fin d := ⟨k,hk⟩
  have hrest : ∀ j : Fin d, j≠i → sig k j=sig (k+1) j := by
    intro j hj
    have hval : j.val≠k := by intro he; apply hj; exact Fin.ext he
    by_cases hlt : j.val<k
    · have hlt' : j.val<k+1 := by omega
      simp [sig,hlt,hlt']
    · have hlt' : ¬j.val<k+1 := by omega
      simp [sig,hlt,hlt']
  by_cases he : sig k i=sig (k+1) i
  · left
    congr 1
    funext j
    by_cases hj : j=i
    · simpa [hj] using he
    · exact hrest j hj
  · right
    exact m.point_adj_of_single_change _ _ i he hrest

#print axioms PairedBasisModel.point_extreme
#print axioms PairedBasisModel.extreme_eq_point
#print axioms PairedBasisModel.point_adj_update
#print axioms paired_basis_diamLE
end HirschPairedBases
