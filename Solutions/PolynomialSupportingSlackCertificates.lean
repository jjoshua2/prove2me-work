import Definitions.Def_Hirsch_model

/-!
# Exact finite certificates for vertices and ordinary edges

The cyclic continuation generates rational slack polynomials and checks their
active ranks. These general geometric lemmas explain the corresponding kernel
obligations without assuming a graph isomorphism or a diameter theorem.
New source candidate: no Lean compilation or platform verdict is claimed.
-/
open Set Hirsch
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschSlackCertificates
variable {d n : ℕ}

private lemma tight_at_first_endpoint {α β p q B : ℝ}
    (ha : 0 < α) (hb : 0 ≤ β) (hs : α+β=1)
    (hp : p ≤ B) (hq : q ≤ B) (hz : α*p+β*q=B) : p=B := by
  by_contra hn
  have hlt : p < B := lt_of_le_of_ne hp hn
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left hq hb
  have hsum : α*B+β*B=B := by rw [← add_mul,hs,one_mul]
  linarith

/-- Feasibility and an injective active-row map certify extremality. -/
theorem vertex_of_tight_kernel_zero
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n))
    (hx : x ∈ Hpoly a b) (htight : ∀ i ∈ S, ⟪a i,x⟫=b i)
    (hkernel : ∀ z : EuclideanSpace ℝ (Fin d),
      (∀ i ∈ S, ⟪a i,z⟫=0) → z=0) :
    x ∈ extremePoints ℝ (Hpoly a b) := by
  refine ⟨hx,?_⟩
  intro p hp q hq hseg
  obtain ⟨α,β,hα,hβ,hs,hcomb⟩ := hseg
  have hz : p-x=0 := by
    apply hkernel
    intro i hi
    have he := congrArg (fun z : EuclideanSpace ℝ (Fin d) => ⟪a i,z⟫) hcomb
    simp only [inner_add_right,inner_smul_right] at he
    rw [htight i hi] at he
    have hpt := tight_at_first_endpoint hα hβ.le hs (hp i) (hq i) he
    rw [inner_sub_right,hpt,htight i hi,sub_self]
  exact sub_eq_zero.mp hz

/-- A one-dimensional common active kernel plus the two endpoint bounds
identifies the whole equality face with the endpoint segment. -/
theorem segment_of_common_tight_kernel
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y z : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n))
    (hx : x ∈ Hpoly a b) (hy : y ∈ Hpoly a b) (hz : z ∈ Hpoly a b)
    (htx : ∀ i ∈ S, ⟪a i,x⟫=b i) (htz : ∀ i ∈ S, ⟪a i,z⟫=b i)
    (hline : ∀ v : EuclideanSpace ℝ (Fin d),
      (∀ i ∈ S, ⟪a i,v⟫=0) → ∃ t : ℝ, v=t • (y-x))
    (left right : Fin n)
    (hlx : ⟪a left,x⟫=b left) (hly : ⟪a left,y⟫<b left)
    (hry : ⟪a right,y⟫=b right) (hrx : ⟪a right,x⟫<b right) :
    z ∈ segment ℝ x y := by
  obtain ⟨t, ht⟩ := hline (z-x) (by
    intro i hi
    rw [inner_sub_right,htz i hi,htx i hi,sub_self])
  have hrepr : (1-t) • x + t • y = z := by
    calc
      _ = x + t • (y-x) := by module
      _ = z := by rw [← ht]; abel
  have hleft := congrArg (fun v : EuclideanSpace ℝ (Fin d) => ⟪a left,v⟫) hrepr
  have hright := congrArg (fun v : EuclideanSpace ℝ (Fin d) => ⟪a right,v⟫) hrepr
  simp only [inner_add_right,inner_smul_right,hlx] at hleft
  simp only [inner_add_right,inner_smul_right,hry] at hright
  have ht0 : 0 ≤ t := by have hb := hz left; nlinarith
  have ht1 : t ≤ 1 := by have hb := hz right; nlinarith
  exact ⟨1-t,t,sub_nonneg.mpr ht1,ht0,by ring,hrepr⟩

/-- Rank d-1 shared active rows are checked numerically by the generator.
Their kernel-line certificate proves an ORDINARY edge, not a circuit step. -/
theorem edge_of_common_tight_kernel
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n))
    (hx : x ∈ Hpoly a b) (hy : y ∈ Hpoly a b)
    (htx : ∀ i ∈ S, ⟪a i,x⟫=b i) (hty : ∀ i ∈ S, ⟪a i,y⟫=b i)
    (hline : ∀ v : EuclideanSpace ℝ (Fin d),
      (∀ i ∈ S, ⟪a i,v⟫=0) → ∃ t : ℝ, v=t • (y-x))
    (left right : Fin n)
    (hlx : ⟪a left,x⟫=b left) (hly : ⟪a left,y⟫<b left)
    (hry : ⟪a right,y⟫=b right) (hrx : ⟪a right,x⟫<b right) :
    Adj (Hpoly a b) x y := by
  refine ⟨?_,?_,?_⟩
  · intro he
    rw [←he,hlx] at hly
    exact (lt_irrefl _ hly)
  · intro z hz i
    obtain ⟨α,β,hα,hβ,hs,hcomb⟩ := hz
    rw [←hcomb,inner_add_right,inner_smul_right,inner_smul_right]
    have h₁ := mul_le_mul_of_nonneg_left (hx i) hα
    have h₂ := mul_le_mul_of_nonneg_left (hy i) hβ
    have hscale : α*b i+β*b i=b i := by rw [← add_mul, hs, one_mul]
    linarith
  · intro p hp q hq z hz hseg
    have hztight : ∀ i ∈ S, ⟪a i,z⟫=b i := by
      intro i hi
      obtain ⟨α,β,hα,hβ,hs,hcomb⟩ := hz
      rw [←hcomb,inner_add_right,inner_smul_right,inner_smul_right,htx i hi,hty i hi]
      rw [←add_mul,hs,one_mul]
    have hptight : ∀ i ∈ S, ⟪a i,p⟫=b i := by
      intro i hi
      obtain ⟨α,β,hα,hβ,hs,hcomb⟩ := hseg
      have he := congrArg (fun v : EuclideanSpace ℝ (Fin d) => ⟪a i,v⟫) hcomb
      simp only [inner_add_right,inner_smul_right] at he
      rw [hztight i hi] at he
      exact tight_at_first_endpoint hα hβ.le hs (hp i) (hq i) he
    exact segment_of_common_tight_kernel a b x y p S hx hy hp htx hptight
      hline left right hlx hly hry hrx

/-- Each consecutive-root factor is nonnegative at every integer label. -/
theorem consecutive_root_factor_nonneg (t i : ℤ) :
    0 ≤ ((t : ℝ)-(i : ℝ))*((t : ℝ)-((i : ℝ)+1)) := by
  by_cases h : t ≤ i
  · have ht : (t : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have h' : i+1 ≤ t := by omega
    have ht : (i : ℝ)+1 ≤ (t : ℝ) := by exact_mod_cast h'
    exact mul_nonneg (by linarith) (by linarith)

#print axioms vertex_of_tight_kernel_zero
#print axioms segment_of_common_tight_kernel
#print axioms edge_of_common_tight_kernel
#print axioms consecutive_root_factor_nonneg
end HirschSlackCertificates
