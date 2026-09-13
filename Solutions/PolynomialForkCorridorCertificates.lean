import Mathlib

/-!
# Finite cores of the fork/corridor test for overlapping gain cycles

A vertex-simple path cannot leave a corridor through an attachment and return
through the same attachment. Multiplicative vertex potentials then determine
its exact gain. Applied at an orientation reversal, compatible endpoint gains
force the entire cycle to have gain one.

These are NEW UNCOMPILED candidates. The block-cut/ear-decomposition completeness
proof, all-basis graph classification, hereditary cone-width application and
external classical diameter theorem are not asserted kernel-checked here.
-/
open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschForkCorridor

/-- Finite product of the transport factors of an indexed path. -/
def pathGain (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => pathGain g n * g n

/-- Edgewise potential identities determine every path product. No shortest
path or acyclicity hypothesis is needed for this algebraic statement. -/
theorem pathGain_times_initial (g p : ℕ → ℝ) (n : ℕ)
    (h : ∀ i<n, p (i+1)=g i*p i) :
    pathGain g n*p 0=p n := by
  induction n with
  | zero => simp [pathGain]
  | succ n ih =>
    have ht := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    calc
      pathGain g (n+1)*p 0 = g n*(pathGain g n*p 0) := by
        simp only [pathGain]
        ring
      _ = g n*p n := by rw [ht]
      _ = p (n+1) := hn.symm

/-- All paths inside a balanced corridor have the same endpoint gain. -/
theorem pathGain_eq_endpoint_ratio (g p : ℕ → ℝ) (n : ℕ)
    (h0 : p 0 ≠ 0) (h : ∀ i<n, p (i+1)=g i*p i) :
    pathGain g n=p n/p 0 := by
  apply (eq_div_iff h0).mpr
  exact pathGain_times_initial g p n h

/-- The fork's two incident rows close any certified corridor path to a
unit-gain cycle. Both inward and outward forks use this same identity after
orienting the two gains away from their shared vertex. -/
theorem fork_cycle_gain_one (left right source target transport : ℝ)
    (hsource : source ≠ 0) (hright : right ≠ 0)
    (hpath : transport*source=target)
    (hcompat : left*target=right*source) :
    left*transport/right=1 := by
  apply (div_eq_one_iff_eq hright).mpr
  have he : (left*transport)*source=right*source := by
    calc
      (left*transport)*source = left*(transport*source) := by ring
      _ = left*target := by rw [hpath]
      _ = right*source := hcompat
  exact mul_right_cancel₀ hsource he

/-- A certified unit-gain cycle returns every transported scalar unchanged. -/
theorem closed_path_returns_value (g p q : ℕ → ℝ) (n : ℕ)
    (hp : p 0 ≠ 0)
    (hgp : ∀ i<n, p (i+1)=g i*p i)
    (hgpClosed : p n=p 0)
    (hgq : ∀ i<n, q (i+1)=g i*q i) : q n=q 0 := by
  have hprod : pathGain g n=1 := by
    rw [pathGain_eq_endpoint_ratio g p n hp hgp,hgpClosed]
    exact div_self hp
  have he := pathGain_times_initial g q n hgq
  simpa only [hprod,one_mul] using he.symm

/-- A chain that crosses from one bit value to another has an adjacent
orientation reversal. Such a reversal is the fork used by the graph test. -/
theorem exists_orientation_reversal (b : ℕ → Bool) (n : ℕ)
    (hne : b n ≠ b 0) : ∃ i<n, b (i+1) ≠ b i := by
  by_contra h
  have hadj : ∀ i<n, b (i+1)=b i := by
    intro i hi
    by_contra hn
    exact h ⟨i,hi,hn⟩
  have hconstant : ∀ k, k≤n → b k=b 0 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      exact (hadj k (by omega)).trans (ih (by omega))
  exact hne (hconstant n le_rfl)

/-- A component label propagates through a consecutive outside interval. -/
theorem constant_on_interval {C : Type*} (label : ℕ → C) (a n : ℕ)
    (h : ∀ j<n, label (a+j+1)=label (a+j)) :
    label (a+n)=label a := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := ih (fun j hj => h j (by omega))
    have hn := h n (by omega)
    simpa only [Nat.add_assoc] using hn.trans ht

/-- A purported excursion outside a corridor exits and reenters through the
same gate, contradicting vertex simplicity. The graph verifier supplies the
same-component step identities and the two gate equalities from its outside
component certificate. It never assumes the desired path stays inside. -/
theorem no_simple_outside_excursion {V C : Type*}
    (p : ℕ → V) (component : V → C) (gate : C → V) (a b : ℕ)
    (hab : a+1<b)
    (hinj : Set.InjOn p (Set.Icc a b))
    (hleft : p a=gate (component (p (a+1))))
    (hright : p b=gate (component (p (b-1))))
    (hstep : ∀ j, a+1≤j → j+1<b →
      component (p (j+1))=component (p j)) : False := by
  have hc := constant_on_interval (fun j => component (p j)) (a+1) (b-(a+2))
    (by
      intro j hj
      exact hstep (a+1+j) (by omega) (by omega))
  have hindex : a+1+(b-(a+2))=b-1 := by omega
  rw [hindex] at hc
  have he : p a=p b := by
    calc
      p a = gate (component (p (a+1))) := hleft
      _ = gate (component (p (b-1))) := congrArg gate hc.symm
      _ = p b := hright.symm
  have hi := hinj (show a∈Set.Icc a b from ⟨le_rfl,by omega⟩)
    (show b∈Set.Icc a b from ⟨by omega,le_rfl⟩) he
  omega

#print axioms pathGain_times_initial
#print axioms pathGain_eq_endpoint_ratio
#print axioms fork_cycle_gain_one
#print axioms closed_path_returns_value
#print axioms exists_orientation_reversal
#print axioms constant_on_interval
#print axioms no_simple_outside_excursion
end HirschForkCorridor
