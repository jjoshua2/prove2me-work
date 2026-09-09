import Solutions.PolynomialProjectiveDamageSurviving

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschFaceSplice

noncomputable section

namespace HirschDamagePublic

lemma ordered_of_pairwise {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w)) (pos : ℕ)
    (hpos : ∀ b ∈ blocks, pos ≤ b.s)
    (hp : blocks.Pairwise (fun a b => a.t ≤ b.s)) :
    BlocksOrderedFrom pos blocks := by
  induction blocks generalizing pos with
  | nil => trivial
  | cons b bs ih =>
      have hpair := List.pairwise_cons.mp hp
      exact ⟨hpos b (by simp), ih b.t hpair.1 hpair.2⟩

lemma sums_ofFn {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)} (m : ℕ) :
    ∀ f : Fin m → PathFaceBlock (L := L) P w,
      blockBudgetSum (List.ofFn f) = ∑ i, (f i).B ∧
      blockRemovedLength (List.ofFn f) = ∑ i, ((f i).t - (f i).s) := by
  induction m with
  | zero =>
      intro f
      simp [blockBudgetSum, blockRemovedLength]
  | succ m ih =>
      intro f
      have h := ih (fun i => f i.succ)
      constructor
      · simpa only [List.ofFn_succ, blockBudgetSum, Fin.sum_univ_succ] using
          congrArg (fun z => (f 0).B + z) h.1
      · simpa only [List.ofFn_succ, blockRemovedLength, Fin.sum_univ_succ] using
          congrArg (fun z => ((f 0).t - (f 0).s) + z) h.2

end HirschDamagePublic

/-- Public-vocabulary exact repair theorem. Only steps outside the ordered
half-open intervals must survive. Interior points and steps are unrestricted. -/
theorem solution
    {d m L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (s t B : Fin m → ℕ)
    (F : Fin m → Set (EuclideanSpace ℝ (Fin d)))
    (hst : ∀ i, s i ≤ t i) (htL : ∀ i, t i ≤ L)
    (horder : ∀ i j, i < j → t i ≤ s j)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hD : ∀ i, DiamLE (F i) (B i))
    (hends : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hin : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hsurvive : ∀ j, j < L → (∀ i, j < s i ∨ t i ≤ j) →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (L - (∑ i, t i - s i) + ∑ i, B i) = w L ∧
      ∀ j < L - (∑ i, t i - s i) + ∑ i, B i,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  classical
  let f : Fin m → PathFaceBlock (L := L) P w := fun i =>
    { s := s i, t := t i, B := B i, F := F i
      hst := hst i, htL := htL i, hF := hF i, hFD := hD i
      hsP := (hends i).1, htP := (hends i).2
      hsF := (hin i).1, htF := (hin i).2 }
  have hord : BlocksOrderedFrom 0 (List.ofFn f) := by
    apply HirschDamagePublic.ordered_of_pairwise
    · intro b _
      exact Nat.zero_le b.s
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      exact horder i j hij
  have hs : ∀ j, j < L → StepOutsideBlocks (List.ofFn f) j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
    intro j hj hout
    apply hsurvive j hj
    intro i
    exact hout (f i) ((List.mem_ofFn' f (f i)).mpr ⟨i, rfl⟩)
  have h := splice_ordered_face_blocks_of_surviving_steps_exact
    P (w 0) (w L) w rfl rfl (List.ofFn f) hord hs
  have hsum := HirschDamagePublic.sums_ofFn m f
  rw [hsum.1, hsum.2] at h
  simpa only [f] using h

#print axioms HirschDamagePublic.ordered_of_pairwise
#print axioms HirschDamagePublic.sums_ofFn
#print axioms solution
