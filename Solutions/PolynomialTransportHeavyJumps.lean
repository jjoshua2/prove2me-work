import Mathlib

/-!
# A transport obstruction to bounded-slack, bounded-spill portal repairs

Light transitions move every active row by at most one in a row-label metric.
A heavy transition still retains at least one row. A chain with at most one
heavy transition cannot join supports separated by more than its length.
The cyclic-polar application and the classification of light carriers are
proved separately in the research note. No global diameter premise occurs.

New candidate: no Lean compilation or platform verdict is claimed.
-/
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace HirschRowTransport
variable {α : Type*} [DecidableEq α]

/-- Every row in the first signature is close to some row in the second. -/
def Within (dist : α → α → ℕ) (S T : Finset α) (radius : ℕ) : Prop :=
  ∀ x ∈ S, ∃ y ∈ T, dist x y ≤ radius

lemma within_refl (dist : α → α → ℕ) (hzero : ∀ x, dist x x = 0)
    (S : Finset α) : Within dist S S 0 := by
  intro x hx
  exact ⟨x, hx, by rw [hzero]⟩

lemma within_comp (dist : α → α → ℕ)
    (htriangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (S T U : Finset α) (a b : ℕ)
    (hST : Within dist S T a) (hTU : Within dist T U b) :
    Within dist S U (a+b) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hST x hx
  obtain ⟨z, hz, hyz⟩ := hTU y hy
  exact ⟨z, hz, (htriangle x y z).trans (Nat.add_le_add hxy hyz)⟩

lemma forward_chain (dist : α → α → ℕ)
    (hzero : ∀ x, dist x x = 0)
    (htriangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (sig : ℕ → Finset α) (L : ℕ) :
    (∀ j < L, Within dist (sig j) (sig (j+1)) 1) →
      Within dist (sig 0) (sig L) L := by
  induction L with
  | zero => intro _; exact within_refl dist hzero _
  | succ L ih =>
    intro hs
    exact within_comp dist htriangle _ _ _ L 1
      (ih (fun j hj => hs j (by omega))) (hs L (by omega))

lemma backward_chain (dist : α → α → ℕ)
    (hzero : ∀ x, dist x x = 0)
    (htriangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (sig : ℕ → Finset α) (L : ℕ) :
    (∀ j < L, Within dist (sig (j+1)) (sig j) 1) →
      Within dist (sig L) (sig 0) L := by
  induction L with
  | zero => intro _; exact within_refl dist hzero _
  | succ L ih =>
    intro hs
    have ht := within_comp dist htriangle _ _ _ 1 L
      (hs L (by omega)) (ih (fun j hj => hs j (by omega)))
    simpa only [Nat.add_comm 1 L] using ht

/-- A retained row bridges the two light subchains surrounding one heavy jump. -/
theorem retained_row_bridge (dist : α → α → ℕ)
    (hsymm : ∀ x y, dist x y = dist y x)
    (htriangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (source left right target : Finset α) (a b gap : ℕ)
    (hleft : Within dist left source a) (hright : Within dist right target b)
    (hmeet : (left ∩ right).Nonempty)
    (hgap : ∀ x ∈ source, ∀ y ∈ target, gap ≤ dist x y) :
    gap ≤ a+b := by
  obtain ⟨z, hz⟩ := hmeet
  obtain ⟨x, hx, hzx⟩ := hleft z (Finset.mem_inter.mp hz).1
  obtain ⟨y, hy, hzy⟩ := hright z (Finset.mem_inter.mp hz).2
  rw [hsymm z x] at hzx
  exact (hgap x hx y hy).trans
    ((htriangle x z y).trans (Nat.add_le_add hzx hzy))

/-- No assumption concerns uncharged descendants or actual graph distance.
This is a finite signature-chain obstruction at one repair node. -/
theorem separation_le_length_of_at_most_one_heavy
    (dist : α → α → ℕ) (hzero : ∀ x, dist x x = 0)
    (hsymm : ∀ x y, dist x y = dist y x)
    (htriangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (sig : ℕ → Finset α) (L gap : ℕ) (heavy : Finset ℕ)
    (hsource : (sig 0).Nonempty)
    (hindices : heavy ⊆ Finset.range L) (hcard : heavy.card ≤ 1)
    (hlight : ∀ j < L, j ∉ heavy →
      Within dist (sig j) (sig (j+1)) 1 ∧ Within dist (sig (j+1)) (sig j) 1)
    (hmeet : ∀ j ∈ heavy, (sig j ∩ sig (j+1)).Nonempty)
    (hgap : ∀ x ∈ sig 0, ∀ y ∈ sig L, gap ≤ dist x y) : gap ≤ L := by
  classical
  by_cases hn : heavy.Nonempty
  · obtain ⟨i, hi⟩ := hn
    have hiL : i < L := Finset.mem_range.mp (hindices hi)
    have huniq : ∀ j ∈ heavy, j = i := by
      intro j hj
      exact (Finset.card_le_one.mp hcard) j hj i hi
    have hprefix : Within dist (sig i) (sig 0) i := by
      apply backward_chain dist hzero htriangle
      intro j hj
      exact (hlight j (by omega) (by intro h; have := huniq j h; omega)).2
    have hsuffix : Within dist (sig (i+1)) (sig L) (L-(i+1)) := by
      have h := forward_chain dist hzero htriangle (fun j => sig (i+1+j)) (L-(i+1)) (by
        intro j hj
        have hn : i+1+j ∉ heavy := by
          intro hmem
          have := huniq (i+1+j) hmem
          omega
        simpa only [Nat.add_assoc] using (hlight (i+1+j) (by omega) hn).1)
      have hend : i+1+(L-(i+1)) = L := by omega
      simpa only [Nat.add_zero, hend] using h
    have h := retained_row_bridge dist hsymm htriangle
      (sig 0) (sig i) (sig (i+1)) (sig L) i (L-(i+1)) gap
      hprefix hsuffix (hmeet i hi) hgap
    omega
  · have he : heavy = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have h := forward_chain dist hzero htriangle sig L (by
      intro j hj
      exact (hlight j hj (by simp [he])).1)
    obtain ⟨x, hx⟩ := hsource
    obtain ⟨y, hy, hxy⟩ := h x hx
    exact (hgap x hx y hy).trans hxy

/-- If the endpoint supports are farther apart than the number of transitions,
at least two heavy occurrences must be paid. They need not have distinct labels. -/
theorem two_heavy_mass_lower_bound
    (dist : α → α → ℕ) (hzero : ∀ x, dist x x = 0)
    (hsymm : ∀ x y, dist x y = dist y x)
    (htriangle : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (sig : ℕ → Finset α) (L gap threshold : ℕ) (heavy : Finset ℕ)
    (mass : ℕ → ℕ) (hsource : (sig 0).Nonempty)
    (hindices : heavy ⊆ Finset.range L)
    (hlight : ∀ j < L, j ∉ heavy →
      Within dist (sig j) (sig (j+1)) 1 ∧ Within dist (sig (j+1)) (sig j) 1)
    (hmeet : ∀ j ∈ heavy, (sig j ∩ sig (j+1)).Nonempty)
    (hgap : ∀ x ∈ sig 0, ∀ y ∈ sig L, gap ≤ dist x y)
    (hfar : L < gap) (hcost : ∀ j ∈ heavy, threshold ≤ mass j) :
    2*threshold ≤ ∑ j ∈ Finset.range L, mass j := by
  have hcount : 2 ≤ heavy.card := by
    by_contra hn
    have h := separation_le_length_of_at_most_one_heavy dist hzero hsymm htriangle
      sig L gap heavy hsource hindices (by omega) hlight hmeet hgap
    omega
  have hsum : heavy.card*threshold ≤ ∑ j ∈ heavy, mass j := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (fun j hj => hcost j hj)
  have hsub : (∑ j ∈ heavy, mass j) ≤ ∑ j ∈ Finset.range L, mass j :=
    Finset.sum_le_sum_of_subset_of_nonneg hindices (by intro j _ _; exact Nat.zero_le _)
  exact ((Nat.mul_le_mul_right threshold hcount).trans hsum).trans hsub

#print axioms forward_chain
#print axioms backward_chain
#print axioms retained_row_bridge
#print axioms separation_le_length_of_at_most_one_heavy
#print axioms two_heavy_mass_lower_bound
end HirschRowTransport
