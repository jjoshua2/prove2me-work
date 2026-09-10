import Solutions.PolynomialProjectiveDamageBlocks

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 7000000

noncomputable section

namespace HirschFaceSplice

/-- An original step index lies outside every half-open damage interval. -/
def StepOutsideBlocks {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w)) (j : ℕ) : Prop :=
  ∀ b, b ∈ blocks → j < b.s ∨ b.t ≤ j

lemma block_start_ge_of_ordered {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    {pos : ℕ} {blocks : List (PathFaceBlock (L := L) P w)}
    (hord : BlocksOrderedFrom pos blocks)
    {b : PathFaceBlock (L := L) P w} (hb : b ∈ blocks) :
    pos ≤ b.s := by
  induction blocks generalizing pos with
  | nil => simp at hb
  | cons c cs ih =>
      change pos ≤ c.s ∧ BlocksOrderedFrom c.t cs at hord
      rcases hord with ⟨hposC, hrest⟩
      simp only [List.mem_cons] at hb
      rcases hb with hbc | hb
      · subst b
        exact hposC
      · have hct : c.t ≤ b.s := ih hrest hb
        exact hposC.trans (c.hst.trans hct)

lemma blockBudgetSum_le_length_mul {d L C : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w))
    (hB : ∀ b ∈ blocks, b.B ≤ C) :
    blockBudgetSum blocks ≤ blocks.length * C := by
  induction blocks with
  | nil => simp [blockBudgetSum]
  | cons b bs ih =>
      have hb : b.B ≤ C := hB b (by simp)
      have htail : ∀ c ∈ bs, c.B ≤ C := by
        intro c hc
        exact hB c (by simp [hc])
      have hadd := Nat.add_le_add hb (ih htail)
      simpa [blockBudgetSum, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hadd

/-- Original step count removed by the selected blocks. -/
def blockRemovedLength {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)} :
    List (PathFaceBlock (L := L) P w) → ℕ
  | [] => 0
  | b :: bs => (b.t - b.s) + blockRemovedLength bs

/-- Exact concatenation budget: surviving gaps plus one face charge per block. -/
def blockRepairLength {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)} (pos : ℕ) :
    List (PathFaceBlock (L := L) P w) → ℕ
  | [] => L - pos
  | b :: bs => (b.s - pos) + b.B + blockRepairLength b.t bs

/-- Ordered intervals cannot remove more original steps than the suffix contains. -/
lemma blockRemovedLength_le {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w))
    (pos : ℕ) (hposL : pos ≤ L) (hord : BlocksOrderedFrom pos blocks) :
    blockRemovedLength blocks ≤ L - pos := by
  induction blocks generalizing pos with
  | nil => simp [blockRemovedLength]
  | cons b bs ih =>
      change pos ≤ b.s ∧ BlocksOrderedFrom b.t bs at hord
      have hi := ih b.t b.htL hord.2
      have hst := b.hst
      have htL := b.htL
      have hposS := hord.1
      have hgap := Nat.sub_add_cancel hposS
      have hblock := Nat.sub_add_cancel hst
      have htail := Nat.sub_add_cancel htL
      have hwhole := Nat.sub_add_cancel hposL
      simp only [blockRemovedLength]
      omega

/-- Conservation of the original length, before natural-number subtraction. -/
lemma blockRepairLength_add_removed {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w))
    (pos : ℕ) (hposL : pos ≤ L) (hord : BlocksOrderedFrom pos blocks) :
    blockRepairLength pos blocks + blockRemovedLength blocks =
      L - pos + blockBudgetSum blocks := by
  induction blocks generalizing pos with
  | nil => simp [blockRepairLength, blockRemovedLength, blockBudgetSum]
  | cons b bs ih =>
      change pos ≤ b.s ∧ BlocksOrderedFrom b.t bs at hord
      have hi := ih b.t b.htL hord.2
      have hgap := Nat.sub_add_cancel hord.1
      have hblock := Nat.sub_add_cancel b.hst
      have htail := Nat.sub_add_cancel b.htL
      have hwhole := Nat.sub_add_cancel hposL
      simp only [blockRepairLength, blockRemovedLength, blockBudgetSum]
      omega

lemma blockRepairLength_eq {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w))
    (pos : ℕ) (hposL : pos ≤ L) (hord : BlocksOrderedFrom pos blocks) :
    blockRepairLength pos blocks =
      (L - pos - blockRemovedLength blocks) + blockBudgetSum blocks := by
  have hle := blockRemovedLength_le blocks pos hposL hord
  have heq := blockRepairLength_add_removed blocks pos hposL hord
  omega

/-- Repair genuinely damaged sequences: no original step inside a block is
assumed valid. The exact budget contains only surviving gaps and face charges. -/
theorem splice_surviving_steps_exact_suffix
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hwL : w L = v)
    (pos : ℕ) (hposL : pos ≤ L)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom pos blocks)
    (hsurvive : ∀ j, pos ≤ j → j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w pos ∧ q (blockRepairLength pos blocks) = v ∧
      ∀ j < blockRepairLength pos blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  induction blocks generalizing pos with
  | nil =>
      let qs : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      refine ⟨qs, rfl, ?_, ?_⟩
      · have hidx : pos + (L - pos) = L := Nat.add_sub_of_le hposL
        simpa [qs, blockRepairLength, hidx] using hwL
      · intro j hj
        have hj' : j < L - pos := by simpa [blockRepairLength] using hj
        have hjL : pos + j < L := by omega
        have hout : StepOutsideBlocks ([] : List (PathFaceBlock (L := L) P w))
            (pos + j) := by
          intro b hb
          simp at hb
        have h := hsurvive (pos + j) (Nat.le_add_right pos j) hjL hout
        simpa [qs, Nat.add_assoc] using h
  | cons b bs ih =>
      change pos ≤ b.s ∧ BlocksOrderedFrom b.t bs at hord
      rcases hord with ⟨hposS, hrest⟩
      let qgap : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      have hgap0 : qgap 0 = w pos := by simp [qgap]
      have hgapB : qgap (b.s - pos) = w b.s := by
        simp [qgap, Nat.add_sub_of_le hposS]
      have hgapstep : ∀ j < b.s - pos,
          qgap j = qgap (j + 1) ∨ Adj P (qgap j) (qgap (j + 1)) := by
        intro j hj
        have hltS : pos + j < b.s := by
          calc
            pos + j < pos + (b.s - pos) := Nat.add_lt_add_left hj pos
            _ = b.s := Nat.add_sub_of_le hposS
        have hjL : pos + j < L := hltS.trans_le (b.hst.trans b.htL)
        have hout : StepOutsideBlocks (b :: bs) (pos + j) := by
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with hcb | hc
          · subst c
            exact Or.inl hltS
          · have hstart : b.t ≤ c.s := block_start_ge_of_ordered hrest hc
            exact Or.inl (hltS.trans_le (b.hst.trans hstart))
        simpa [qgap, Nat.add_assoc] using
          hsurvive (pos + j) (Nat.le_add_right pos j) hjL hout
      obtain ⟨qface, hface0, hfaceB, hfacestep⟩ :=
        b.hFD (w b.s) (extreme_in_extreme_face b.hF b.hsP b.hsF)
          (w b.t) (extreme_in_extreme_face b.hF b.htP b.htF)
      have hfacestepP : ∀ j < b.B,
          qface j = qface (j + 1) ∨ Adj P (qface j) (qface (j + 1)) := by
        intro j hj
        rcases hfacestep j hj with heq | hadj
        · exact Or.inl heq
        · exact Or.inr (face_adj_to_parent b.hF hadj)
      have hsurviveRest : ∀ j, b.t ≤ j → j < L → StepOutsideBlocks bs j →
          w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
        intro j htj hjL hout
        apply hsurvive j (hposS.trans (b.hst.trans htj)) hjL
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with hcb | hc
        · subst c
          exact Or.inr htj
        · exact hout c hc
      obtain ⟨qrest, hrest0, hrestB, hreststep⟩ :=
        ih b.t b.htL hrest hsurviveRest
      obtain ⟨qgf, hgf0, hgfB, hgfstep⟩ :=
        HirschProduct.append_walk (Adj P) qgap qface
          hgap0 hgapB hface0 hfaceB hgapstep hfacestepP
      obtain ⟨qall, hall0, hallB, hallstep⟩ :=
        HirschProduct.append_walk (Adj P) qgf qrest
          hgf0 hgfB hrest0 hrestB hgfstep hreststep
      exact ⟨qall, hall0, hallB, hallstep⟩

/-- Exact global budget: original length minus removed steps plus repair costs.
This does not assume the original sequence was a walk in the repaired polytope. -/
theorem splice_ordered_face_blocks_of_surviving_steps_exact
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L - blockRemovedLength blocks + blockBudgetSum blocks) = v ∧
      ∀ j < L - blockRemovedLength blocks + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_surviving_steps_exact_suffix P v w hwL 0 (Nat.zero_le L) blocks hord
      (fun j _ hj hout => hsurvive j hj hout)
  have hbudget := blockRepairLength_eq blocks 0 (Nat.zero_le L) hord
  simp only [Nat.sub_zero] at hbudget
  rw [hbudget] at hqB hqstep
  exact ⟨q, hq0.trans hw0, hqB, hqstep⟩

/-- Backward-compatible loose suffix bound, derived from the exact repair. -/
theorem splice_ordered_face_blocks_of_surviving_steps_suffix
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hwL : w L = v)
    (pos : ℕ) (hposL : pos ≤ L)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom pos blocks)
    (hsurvive : ∀ j, pos ≤ j → j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w pos ∧ q (L - pos + blockBudgetSum blocks) = v ∧
      ∀ j < L - pos + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_surviving_steps_exact_suffix P v w hwL pos hposL blocks hord hsurvive
  have hid := blockRepairLength_add_removed blocks pos hposL hord
  have hle : blockRepairLength pos blocks ≤ L - pos + blockBudgetSum blocks := by omega
  exact HirschProduct.pad_walk (Adj P) hle q hq0 hqB hqstep

/-- Loose global form retained for callers that do not track removed lengths. -/
theorem splice_ordered_face_blocks_of_surviving_steps
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L + blockBudgetSum blocks) = v ∧
      ∀ j < L + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_of_surviving_steps_exact P u v w hw0 hwL blocks hord hsurvive
  have hle : L - blockRemovedLength blocks + blockBudgetSum blocks ≤
      L + blockBudgetSum blocks := Nat.add_le_add_right (Nat.sub_le _ _) _
  exact HirschProduct.pad_walk (Adj P) hle q hq0 hqB hqstep

/-- At most M damaged intervals of cost at most C, with no interior survival assumption. -/
theorem splice_surviving_steps_uniform
    {d L M C : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hlen : blocks.length ≤ M) (hB : ∀ b ∈ blocks, b.B ≤ C) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L + M * C) = v ∧
      ∀ j < L + M * C,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_of_surviving_steps P u v w hw0 hwL blocks hord hsurvive
  have hsum := blockBudgetSum_le_length_mul blocks hB
  have hmul : blocks.length * C ≤ M * C := Nat.mul_le_mul_right C hlen
  exact HirschProduct.pad_walk (Adj P) (Nat.add_le_add_left (hsum.trans hmul) L)
    q hq0 hqB hqstep

/-- Compatibility wrapper. For new applications use the surviving-steps theorem. -/
theorem splice_ordered_face_blocks_uniform
    {d L M C : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hlen : blocks.length ≤ M) (hB : ∀ b ∈ blocks, b.B ≤ C) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L + M * C) = v ∧
      ∀ j < L + M * C,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  exact splice_surviving_steps_uniform P u v w hw0 hwL blocks hord
    (fun j hj _ => hwstep j hj) hlen hB

/-- Aggregate savings suffice: individual repairs may grow provided their total
cost does not exceed the number of original steps removed. -/
theorem splice_surviving_steps_no_growth
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hcost : blockBudgetSum blocks ≤ blockRemovedLength blocks) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q L = v ∧
      ∀ j < L, q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_of_surviving_steps_exact P u v w hw0 hwL blocks hord hsurvive
  have hremoved := blockRemovedLength_le blocks 0 (Nat.zero_le L) hord
  simp only [Nat.sub_zero] at hremoved
  have hle : L - blockRemovedLength blocks + blockBudgetSum blocks ≤ L := by omega
  exact HirschProduct.pad_walk (Adj P) hle q hq0 hqB hqstep

#print axioms block_start_ge_of_ordered
#print axioms blockBudgetSum_le_length_mul
#print axioms blockRemovedLength_le
#print axioms blockRepairLength_add_removed
#print axioms blockRepairLength_eq
#print axioms splice_surviving_steps_exact_suffix
#print axioms splice_ordered_face_blocks_of_surviving_steps_exact
#print axioms splice_ordered_face_blocks_of_surviving_steps_suffix
#print axioms splice_ordered_face_blocks_of_surviving_steps
#print axioms splice_surviving_steps_uniform
#print axioms splice_ordered_face_blocks_uniform
#print axioms splice_surviving_steps_no_growth

end HirschFaceSplice
