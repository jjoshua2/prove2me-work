import Definitions.Def_Hirsch_model

/-!
# Exact ordinary edges in coordinate-difference systems

Connectivity of the tight-row graph certifies vertices. Two connected blocks
in a common tight-row graph give a one-dimensional fiber; endpoint blockers
then identify its entire feasible face with the endpoint segment. A cut vector
alone is NOT an edge certificate. No nondegeneracy assumption is used.

New proof candidates: separate pinned Lean compilation/axiom audit required.
-/
open Set Hirsch
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschNetwork
variable {V A : Type*} [DecidableEq V] [DecidableEq A]

def potentials (root : V) (tail head : A → V) (bound : A → ℝ) : Set (V → ℝ) :=
  {x | x root=0 ∧ ∀ e, x (head e)-x (tail e)≤bound e}

def rowGraph (tail head : A → V) (S : Finset A) : SimpleGraph V where
  Adj i j := i≠j ∧ ∃ e∈S, (tail e=i ∧ head e=j) ∨ (tail e=j ∧ head e=i)
  symm := by
    rintro i j ⟨hne,e,he,hij|hji⟩
    · exact ⟨hne.symm,e,he,Or.inr hij⟩
    · exact ⟨hne.symm,e,he,Or.inl hji⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem value_eq_of_row_walk (tail head : A → V) (S : Finset A)
    (z : V → ℝ) (hz : ∀ e∈S, z (head e)-z (tail e)=0)
    {i j : V} (p : (rowGraph tail head S).Walk i j) : z i=z j := by
  induction p with
  | nil => rfl
  | @cons i k j hik p ih =>
    obtain ⟨_,e,he,⟨ht,hh⟩|⟨ht,hh⟩⟩ := hik
    · have h := hz e he
      rw [ht,hh] at h
      linarith
    · have h := hz e he
      rw [ht,hh] at h
      linarith

private lemma active_scalar {a c p q B : ℝ}
    (ha : 0<a) (hc : 0≤c) (hac : a+c=1)
    (hp : p≤B) (hq : q≤B) (he : a*p+c*q=B) : p=B := by
  by_contra hn
  have hlt := lt_of_le_of_ne hp hn
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left hq hc
  nlinarith

/-- The path witnesses are ordinary finite graph connectivity, not graph
routes between polytope vertices and not any diameter premise. -/
theorem vertex_of_connected_tight_rows
    (root : V) (tail head : A → V) (bound : A → ℝ)
    (x : V → ℝ) (S : Finset A)
    (hx : x∈potentials root tail head bound)
    (htight : ∀ e∈S, x (head e)-x (tail e)=bound e)
    (hconn : ∀ i, Nonempty ((rowGraph tail head S).Walk root i)) :
    x∈extremePoints ℝ (potentials root tail head bound) := by
  refine ⟨hx,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  have hpt : ∀ e∈S, p (head e)-p (tail e)=bound e := by
    intro e he
    have hv := congrArg (fun z : V → ℝ => z (head e)-z (tail e)) hcomb
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hv
    exact active_scalar ha hc.le hac (hp.2 e) (hq.2 e)
      (by have ht := htight e he; nlinarith)
  have hk : ∀ e∈S, (p-x) (head e)-(p-x) (tail e)=0 := by
    intro e he
    have h₁ := hpt e he
    have h₂ := htight e he
    simp only [Pi.sub_apply]
    linarith
  funext i
  obtain ⟨w⟩ := hconn i
  have h := value_eq_of_row_walk tail head S (p-x) hk w
  change p root-x root=p i-x i at h
  rw [hp.1,hx.1] at h
  linarith

def cutDirection (root : V) (U : Set V) [DecidablePred (·∈U)] : V → ℝ :=
  fun i => (if i∈U then 1 else 0)-(if root∈U then 1 else 0)

/-- Constant on each of two connected blocks, pinned at root, is exactly a
multiple of their cut direction. Extra tight rows can only strengthen this. -/
theorem kernel_of_two_connected_blocks
    (root : V) (tail head : A → V) (S : Finset A)
    (U : Set V) [DecidablePred (·∈U)] (r s : V)
    (hr : r∉U) (hs : s∈U)
    (hconn : ∀ i, Nonempty ((rowGraph tail head S).Walk (if i∈U then s else r) i))
    (z : V → ℝ) (hz0 : z root=0)
    (hz : ∀ e∈S, z (head e)-z (tail e)=0) :
    z=(z s-z r) • cutDirection root U := by
  have hval : ∀ i, z i=if i∈U then z s else z r := by
    intro i
    obtain ⟨w⟩ := hconn i
    have h := value_eq_of_row_walk tail head S z hz w
    by_cases hi : i∈U <;> simpa [hi] using h.symm
  have hroot := hval root
  funext i
  have hi := hval i
  by_cases h₀ : root∈U <;> by_cases hᵢ : i∈U <;>
    simp [cutDirection,h₀,hᵢ,Pi.smul_apply,smul_eq_mul] at hroot hi ⊢ <;> linarith

/-- Feasible endpoints with a one-dimensional common active fiber and an
opposite strict blocker at each endpoint form an ORDINARY exposed edge. -/
theorem edge_of_common_network_kernel
    (root : V) (tail head : A → V) (bound : A → ℝ)
    (x y : V → ℝ) (S : Finset A)
    (hx : x∈potentials root tail head bound) (hy : y∈potentials root tail head bound)
    (htx : ∀ e∈S, x (head e)-x (tail e)=bound e)
    (hty : ∀ e∈S, y (head e)-y (tail e)=bound e)
    (hline : ∀ z : V → ℝ, z root=0 →
      (∀ e∈S, z (head e)-z (tail e)=0) → ∃ t : ℝ,z=t • (y-x))
    (leave enter : A)
    (hlx : x (head leave)-x (tail leave)=bound leave)
    (hly : y (head leave)-y (tail leave)<bound leave)
    (hry : y (head enter)-y (tail enter)=bound enter)
    (hrx : x (head enter)-x (tail enter)<bound enter) :
    Adj (potentials root tail head bound) x y := by
  have hsegment : ∀ z∈potentials root tail head bound,
      (∀ e∈S,z (head e)-z (tail e)=bound e) → z∈segment ℝ x y := by
    intro z hz ht
    have hz0 : (z-x) root=0 := by simp [hz.1,hx.1]
    have hker : ∀ e∈S,(z-x) (head e)-(z-x) (tail e)=0 := by
      intro e he
      have h₁ := ht e he
      have h₂ := htx e he
      simp only [Pi.sub_apply]
      linarith
    obtain ⟨t,ht⟩ := hline (z-x) hz0 hker
    have hcomb : (1-t) • x+t • y=z := by
      calc
        _ = x+t • (y-x) := by module
        _ = z := by rw [←ht]; abel
    have hleft := congrArg (fun v : V → ℝ => v (head leave)-v (tail leave)) hcomb
    have hright := congrArg (fun v : V → ℝ => v (head enter)-v (tail enter)) hcomb
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hleft hright
    have ht0 : 0≤t := by have h := hz.2 leave; nlinarith
    have ht1 : t≤1 := by have h := hz.2 enter; nlinarith
    exact ⟨1-t,t,by linarith,ht0,by ring,hcomb⟩
  refine ⟨?_,?_,?_⟩
  · intro he
    rw [←he,hlx] at hly
    exact (lt_irrefl _ hly)
  · intro z hz
    obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hz
    refine ⟨?_,?_⟩
    · rw [←hcomb]
      simp [hx.1,hy.1]
    · intro e
      have h := congrArg (fun v : V → ℝ => v (head e)-v (tail e)) hcomb
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h
      have h₁ := mul_le_mul_of_nonneg_left (hx.2 e) ha
      have h₂ := mul_le_mul_of_nonneg_left (hy.2 e) hc
      nlinarith
  · intro p hp q hq z hz hseg
    apply hsegment p hp
    intro e he
    have hzt : z (head e)-z (tail e)=bound e := by
      obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hz
      have h := congrArg (fun v : V → ℝ => v (head e)-v (tail e)) hcomb
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h
      have h₁ := htx e he
      have h₂ := hty e he
      nlinarith
    obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
    have h := congrArg (fun v : V → ℝ => v (head e)-v (tail e)) hcomb
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h
    exact active_scalar ha hc.le hac (hp.2 e) (hq.2 e) (by nlinarith)

/-- The two component path certificates discharge the analytic kernel-line
premise of the ordinary-edge lemma. The positive cut step is not an oracle. -/
theorem edge_of_spanning_cut
    (root : V) (tail head : A → V) (bound : A → ℝ)
    (x y : V → ℝ) (S : Finset A)
    (hx : x∈potentials root tail head bound) (hy : y∈potentials root tail head bound)
    (htx : ∀ e∈S,x (head e)-x (tail e)=bound e)
    (hty : ∀ e∈S,y (head e)-y (tail e)=bound e)
    (U : Set V) [DecidablePred (·∈U)] (r s : V) (hr : r∉U) (hs : s∈U)
    (hconn : ∀ i, Nonempty ((rowGraph tail head S).Walk (if i∈U then s else r) i))
    (θ : ℝ) (hθ : 0<θ) (hstep : y-x=θ • cutDirection root U)
    (leave enter : A)
    (hlx : x (head leave)-x (tail leave)=bound leave)
    (hly : y (head leave)-y (tail leave)<bound leave)
    (hry : y (head enter)-y (tail enter)=bound enter)
    (hrx : x (head enter)-x (tail enter)<bound enter) :
    Adj (potentials root tail head bound) x y := by
  apply edge_of_common_network_kernel root tail head bound x y S hx hy htx hty
    (leave := leave) (enter := enter) (hlx := hlx) (hly := hly) (hry := hry) (hrx := hrx)
  intro z hz0 hz
  refine ⟨(z s-z r)/θ,?_⟩
  have hk := kernel_of_two_connected_blocks root tail head S U r s hr hs hconn z hz0 hz
  rw [hstep,smul_smul,div_mul_cancel₀ _ (ne_of_gt hθ)]
  exact hk

/-- A directed path of tight inequalities cannot coexist with a strictly
slack shortcut which is tight at another feasible point. This is the scalar
core guaranteeing a backward tree edge in a target-insertion phase. -/
theorem tight_path_forces_target_tight
    (n : ℕ) (u v : ℕ → ℝ) (cost : Fin n → ℝ) (C : ℝ)
    (hu : ∀ i : Fin n,u (i.val+1)-u i.val=cost i)
    (hv : ∀ i : Fin n,v (i.val+1)-v i.val≤cost i)
    (hvtarget : v n-v 0=C) (hutarget : u n-u 0≤C) : u n-u 0=C := by
  have telescope : ∀ (m : ℕ) (x : ℕ → ℝ),
      (∑ i : Fin m, x (i.val+1)-x i.val)=x m-x 0 := by
    intro m x
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [ih]
      ring
  have he : u n-u 0=∑ i,cost i := by
    rw [←telescope n u]
    exact Finset.sum_congr rfl (fun i _ => hu i)
  have hv' := Finset.sum_le_sum (fun i _ => hv i)
  rw [telescope n v,hvtarget] at hv'
  linarith

#print axioms value_eq_of_row_walk
#print axioms vertex_of_connected_tight_rows
#print axioms kernel_of_two_connected_blocks
#print axioms edge_of_common_network_kernel
#print axioms edge_of_spanning_cut
#print axioms tight_path_forces_target_tight
end HirschNetwork
