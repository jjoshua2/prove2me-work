import Definitions.Def_Hirsch_model

/-!
# Ordinary edges from finite Minkowski support certificates

A support slice of a finite Minkowski sum is the sum of the support slices.
When these slices are collinear segments their sum is an actual exposed edge.
The finite-hull lemma reduces a summand's support-slice obligation to its listed
vertices. No circuit, graph-isomorphism or diameter oracle is assumed.

New candidate: this source has not been Lean-compiled in the originating session.
-/
open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschMinkowski
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]

def supportFace (P : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ) : Set E :=
  {x | x ∈ P ∧ f x = β}

def sumSet (S : ι → Set E) : Set E :=
  {z | ∃ x : ι → E, (∀ i, x i ∈ S i) ∧ (∑ i, x i) = z}

private lemma active_scalar {a c x y β : ℝ}
    (ha : 0<a) (hc : 0≤c) (hac : a+c=1)
    (hx : x≤β) (hy : y≤β) (he : a*x+c*y=β) : x=β := by
  by_contra hn
  have hlt : x<β := lt_of_le_of_ne hx hn
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left hy hc
  nlinarith

/-- A supporting maximum slice is an extreme subset, even before convexity. -/
theorem supportFace_isExtreme (P : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ)
    (hbound : ∀ x ∈ P, f x≤β) : IsExtreme ℝ P (supportFace P f β) := by
  refine ⟨fun x hx => hx.1, ?_⟩
  intro p hp q hq z hz hseg
  refine ⟨hp, ?_⟩
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  have he := congrArg f hcomb
  simp only [map_add,map_smul,smul_eq_mul] at he
  exact active_scalar ha hc.le hac (hbound p hp) (hbound q hq) (he.trans hz.2)

/-- This is ordinary parent-polytope adjacency, not a potential edge direction. -/
theorem adj_of_supportFace_eq_segment (P : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ)
    (x y : E) (hne : x≠y) (hbound : ∀ z ∈ P, f z≤β)
    (hface : supportFace P f β = segment ℝ x y) : Hirsch.Adj P x y := by
  refine ⟨hne, ?_⟩
  rw [←hface]
  exact supportFace_isExtreme P f β hbound

/-- A convex hull inherits both a supporting bound and its top-face inclusion.
The proof handles zero convex coefficients rather than assuming strict ones. -/
theorem convexHull_support_contained (S F : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ)
    (hF : Convex ℝ F)
    (hS : ∀ x ∈ S, f x≤β ∧ (f x=β → x∈F)) :
    ∀ x ∈ convexHull ℝ S, f x≤β ∧ (f x=β → x∈F) := by
  let good : Set E := {x | f x≤β ∧ (f x=β → x∈F)}
  have hgood : Convex ℝ good := by
    intro x hx y hy a c ha hc hac
    have he : f (a • x+c • y)=a*f x+c*f y := by simp
    have h₁ := mul_le_mul_of_nonneg_left hx.1 ha
    have h₂ := mul_le_mul_of_nonneg_left hy.1 hc
    refine ⟨?_, ?_⟩
    · rw [he]; nlinarith
    · intro ht
      by_cases ha0 : a=0
      · have hc1 : c=1 := by linarith
        simpa [ha0,hc1] using hy.2 (by simpa [ha0,hc1] using ht)
      by_cases hc0 : c=0
      · have ha1 : a=1 := by linarith
        simpa [hc0,ha1] using hx.2 (by simpa [hc0,ha1] using ht)
      have hapos : 0<a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hcpos : 0<c := lt_of_le_of_ne hc (Ne.symm hc0)
      have htop : a*f x+c*f y=β := he.symm.trans ht
      have hxeq := active_scalar hapos hc hac hx.1 hy.1 htop
      have hyeq := active_scalar hcpos ha (by linarith) hy.1 hx.1 (by nlinarith)
      exact hF (hx.2 hxeq) (hy.2 hyeq) ha hc hac
  exact convexHull_min (fun x hx => hS x hx) hgood

/-- Checking all listed vertices suffices for the exact exposed segment of a
finite hull. S may contain redundant/nonvertex points; none is silently dropped. -/
theorem convexHull_supportFace_eq_segment (S : Set E)
    (f : E →ₗ[ℝ] ℝ) (β : ℝ) (a b : E)
    (ha : a∈S) (hb : b∈S) (hfa : f a=β) (hfb : f b=β)
    (hbound : ∀ x∈S, f x≤β)
    (hmax : ∀ x∈S, f x=β → x∈segment ℝ a b) :
    supportFace (convexHull ℝ S) f β = segment ℝ a b := by
  have h := convexHull_support_contained S (segment ℝ a b) f β
    (convex_segment a b) (fun x hx => ⟨hbound x hx,hmax x hx⟩)
  apply Set.Subset.antisymm
  · intro x hx
    exact (h x hx.1).2 hx.2
  · intro x hx
    obtain ⟨r,s,hr,hs,hrs,hcomb⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [←hcomb]
      exact (convex_convexHull ℝ S) (subset_convexHull ℝ S ha)
        (subset_convexHull ℝ S hb) hr hs hrs
    · rw [←hcomb]
      simp only [map_add,map_smul,smul_eq_mul,hfa,hfb]
      nlinarith

theorem sumSet_support_bound (S : ι → Set E) (f : E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (hbound : ∀ i, ∀ x∈S i, f x≤β i) :
    ∀ z∈sumSet S, f z≤∑ i, β i := by
  rintro z ⟨x,hx,rfl⟩
  rw [map_sum]
  exact Finset.sum_le_sum (fun i _ => hbound i (x i) (hx i))

/-- Equality of the total support value forces equality in EVERY summand. -/
theorem sumSet_supportFace (S : ι → Set E) (f : E →ₗ[ℝ] ℝ) (β : ι → ℝ)
    (hbound : ∀ i, ∀ x∈S i, f x≤β i) :
    supportFace (sumSet S) f (∑ i, β i) = sumSet (fun i => supportFace (S i) f (β i)) := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨⟨x,hx,hxz⟩,hz⟩
    refine ⟨x,?_,hxz⟩
    intro i
    refine ⟨hx i,?_⟩
    by_contra hn
    have hs : (∑ j, f (x j)) < ∑ j, β j :=
      Finset.sum_lt_sum (fun j _ => hbound j (x j) (hx j))
        ⟨i,Finset.mem_univ i,lt_of_le_of_ne (hbound i (x i) (hx i)) hn⟩
    have he : (∑ j, f (x j))=∑ j, β j := by rw [←map_sum,hxz,hz]
    linarith
  · rintro z ⟨x,hx,rfl⟩
    refine ⟨⟨x,fun i => (hx i).1,rfl⟩,?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => (hx i).2)

def intervalLine (a g : E) (η : ℝ) : Set E :=
  {x | ∃ t : ℝ, 0≤t ∧ t≤η ∧ x=a+t • g}

/-- Minkowski addition of parallel intervals adds their lengths exactly. -/
theorem sumSet_intervalLine (a : ι → E) (g : E) (η : ι → ℝ)
    (hη : ∀ i, 0≤η i) :
    sumSet (fun i => intervalLine (a i) g (η i)) =
      intervalLine (∑ i,a i) g (∑ i,η i) := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨x,hx,rfl⟩
    choose t ht0 htη hxt using hx
    refine ⟨∑ i,t i,Finset.sum_nonneg (fun i _ => ht0 i),
      Finset.sum_le_sum (fun i _ => htη i),?_⟩
    simp only [hxt,Finset.sum_add_distrib,Finset.sum_smul]
  · rintro z ⟨t,ht0,htη,rfl⟩
    by_cases hzero : (∑ i,η i)=0
    · have ht : t=0 := by linarith
      refine ⟨a,fun i => ⟨0,le_rfl,hη i,by simp⟩,?_⟩
      simp [ht]
    · have hpos : 0<∑ i,η i := lt_of_le_of_ne
        (Finset.sum_nonneg (fun i _ => hη i)) (Ne.symm hzero)
      let r : ℝ := t/(∑ i,η i)
      have hr0 : 0≤r := div_nonneg ht0 hpos.le
      have hr1 : r≤1 := (div_le_one hpos).mpr htη
      have hrt : r*(∑ i,η i)=t := div_mul_cancel₀ t hzero
      refine ⟨fun i => a i+(r*η i) • g,?_,?_⟩
      · intro i
        exact ⟨r*η i,mul_nonneg hr0 (hη i),
          by simpa using mul_le_mul_of_nonneg_right hr1 (hη i),rfl⟩
      · simp only [Finset.sum_add_distrib,Finset.sum_smul,←Finset.mul_sum,hrt]

lemma intervalLine_eq_segment (a g : E) (η : ℝ) (hη : 0≤η) :
    intervalLine a g η = segment ℝ a (a+η • g) := by
  apply Set.Subset.antisymm
  · rintro z ⟨t,ht0,htη,rfl⟩
    by_cases hzero : η=0
    · have ht : t=0 := by linarith
      simp [ht,hzero]
    · have hpos : 0<η := lt_of_le_of_ne hη (Ne.symm hzero)
      have hr0 : 0≤t/η := div_nonneg ht0 hη
      have hr1 : t/η≤1 := (div_le_one hpos).mpr htη
      have hrt : (t/η)*η=t := div_mul_cancel₀ t hzero
      refine ⟨1-t/η,t/η,by linarith,hr0,by ring,?_⟩
      simp only [smul_add,smul_smul,hrt]
      module
  · rintro z ⟨r,s,hr,hs,hrs,hcomb⟩
    refine ⟨s*η,mul_nonneg hs hη,?_,?_⟩
    · have hs1 : s≤1 := by linarith
      simpa using mul_le_mul_of_nonneg_right hs1 hη
    · rw [←hcomb]
      calc
        r • a+s • (a+η • g) = (r+s) • a+(s*η) • g := by module
        _ = a+(s*η) • g := by rw [hrs,one_smul]

/-- Finite geometric data at ONE dual-wall crossing produce an actual edge.
A simultaneous switch of parallel summand faces is allowed; higher-rank
simultaneous switches are not covered by this certificate. -/
theorem minkowski_adj_of_parallel_support
    (S : ι → Set E) (f : E →ₗ[ℝ] ℝ) (β η : ι → ℝ)
    (a : ι → E) (g : E)
    (hbound : ∀ i, ∀ x∈S i, f x≤β i) (hη : ∀ i,0≤η i)
    (hface : ∀ i, supportFace (S i) f (β i)=intervalLine (a i) g (η i))
    (hne : (∑ i,a i) ≠ (∑ i,a i)+(∑ i,η i) • g) :
    Hirsch.Adj (sumSet S) (∑ i,a i) ((∑ i,a i)+(∑ i,η i) • g) := by
  apply adj_of_supportFace_eq_segment (sumSet S) f (∑ i,β i) _ _ hne
    (sumSet_support_bound S f β hbound)
  rw [sumSet_supportFace S f β hbound]
  have hf : (fun i => supportFace (S i) f (β i))=(fun i => intervalLine (a i) g (η i)) :=
    funext hface
  rw [hf,sumSet_intervalLine a g η hη]
  exact intervalLine_eq_segment _ _ _ (Finset.sum_nonneg (fun i _ => hη i))

#print axioms supportFace_isExtreme
#print axioms convexHull_support_contained
#print axioms convexHull_supportFace_eq_segment
#print axioms sumSet_supportFace
#print axioms sumSet_intervalLine
#print axioms minkowski_adj_of_parallel_support
end HirschMinkowski
