import Solutions.PolynomialProjectiveDamageBlocks

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 7000000

noncomputable section

namespace HirschFaceSplice

/-- An original step index lies outside every recorded damage interval. -/
def StepOutsideBlocks {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (blocks : List (PathFaceBlock (L := L) P w)) (j : ℕ) : Prop :=
  ∀ b, b ∈ blocks → j < b.s ∨ b.t ≤ j

/-- Every block in an ordered tail starts at or after the tail's current
position. -/
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

/-- Sum-of-diameters charge under a uniform per-block diameter bound. -/
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
      have hi := ih htail
      have hadd := Nat.add_le_add hb hi
      simpa [blockBudgetSum, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hadd

/-- Uniform-budget corollary of ordered block amortization. If there are at
most `M` disjoint ordered damage blocks and every supporting face has diameter
at most `C`, all replacements fit in `L + M*C` steps. -/
theorem splice_ordered_face_blocks_uniform
    {d L M C : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L,
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hlen : blocks.length ≤ M)
    (hB : ∀ b ∈ blocks, b.B ≤ C) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L + M * C) = v ∧
      ∀ j < L + M * C,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks P u v w hw0 hwL hwstep blocks hord
  have hsum := blockBudgetSum_le_length_mul blocks hB
  have hmul : blocks.length * C ≤ M * C := Nat.mul_le_mul_right C hlen
  have hbudget : L + blockBudgetSum blocks ≤ L + M * C :=
    Nat.add_le_add_left (hsum.trans hmul) L
  exact HirschProduct.pad_walk (Adj P) hbudget q hq0 hqB hqstep

/-- Actual projective-removal-compatible suffix repair. Original path steps
need only remain valid outside the recorded damage blocks; the interiors of
those intervals may contain destroyed/invalid steps. Each damaged interval is
replaced wholesale by a path inside its supporting extreme face.

Thus ordered disjoint damage blocks still cost at most one intrinsic face
diameter each, even when none of the original interior steps survive. -/
theorem splice_ordered_face_blocks_of_surviving_steps_suffix
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hwL : w L = v)
    (pos : ℕ) (hposL : pos ≤ L)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom pos blocks)
    (hsurvive : ∀ j, pos ≤ j → j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w pos ∧
      q (L - pos + blockBudgetSum blocks) = v ∧
      ∀ j < L - pos + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  induction blocks generalizing pos with
  | nil =>
      let qs : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      refine ⟨qs, rfl, ?_, ?_⟩
      · have hidx : pos + (L - pos) = L := by omega
        simpa [qs, blockBudgetSum, hidx] using hwL
      · intro j hj
        have hj' : j < L - pos := by simpa [blockBudgetSum] using hj
        have hposj : pos ≤ pos + j := Nat.le_add_right pos j
        have hjL : pos + j < L := by omega
        have hout : StepOutsideBlocks ([] : List (PathFaceBlock (L := L) P w))
            (pos + j) := by
          intro b hb
          simp at hb
        have h := hsurvive (pos + j) hposj hjL hout
        simpa [qs, blockBudgetSum, Nat.add_assoc] using h
  | cons b bs ih =>
      change pos ≤ b.s ∧ BlocksOrderedFrom b.t bs at hord
      rcases hord with ⟨hposS, hrest⟩

      let qgap : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      have hgap0 : qgap 0 = w pos := by simp [qgap]
      have hgapB : qgap (b.s - pos) = w b.s := by
        have hidx : pos + (b.s - pos) = b.s := by omega
        simp [qgap, hidx]
      have hgapstep : ∀ j < b.s - pos,
          qgap j = qgap (j + 1) ∨ Adj P (qgap j) (qgap (j + 1)) := by
        intro j hj
        have hltS : pos + j < b.s := by
          calc
            pos + j < pos + (b.s - pos) := Nat.add_lt_add_left hj pos
            _ = b.s := by omega
        have hsL : b.s ≤ L := b.hst.trans b.htL
        have hjL : pos + j < L := hltS.trans_le hsL
        have hout : StepOutsideBlocks (b :: bs) (pos + j) := by
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with hcb | hc
          · subst c
            exact Or.inl hltS
          · have hstart : b.t ≤ c.s := block_start_ge_of_ordered hrest hc
            exact Or.inl (hltS.trans_le (b.hst.trans hstart))
        exact hsurvive (pos + j) (Nat.le_add_right pos j) hjL hout

      have hsFext : w b.s ∈ extremePoints ℝ b.F :=
        extreme_in_extreme_face b.hF b.hsP b.hsF
      have htFext : w b.t ∈ extremePoints ℝ b.F :=
        extreme_in_extreme_face b.hF b.htP b.htF
      obtain ⟨qface, hface0, hfaceB, hfacestep⟩ :=
        b.hFD (w b.s) hsFext (w b.t) htFext
      have hfacestepP : ∀ j < b.B,
          qface j = qface (j + 1) ∨ Adj P (qface j) (qface (j + 1)) := by
        intro j hj
        rcases hfacestep j hj with heq | hadj
        · exact Or.inl heq
        · exact Or.inr (face_adj_to_parent b.hF hadj)

      have hsurviveRest : ∀ j, b.t ≤ j → j < L → StepOutsideBlocks bs j →
          w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
        intro j htj hjL hout
        have hposj : pos ≤ j := hposS.trans (b.hst.trans htj)
        apply hsurvive j hposj hjL
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

      let K := (b.s - pos) + b.B + (L - b.t + blockBudgetSum bs)
      let M := L - pos + (b.B + blockBudgetSum bs)
      have htail : L - b.t ≤ L - b.s := Nat.sub_le_sub_left b.hst L
      have hposSsum : pos + (b.s - pos) = b.s := by omega
      have hsLsum : b.s + (L - b.s) = L := by omega
      have hposLsum : pos + (L - pos) = L := by omega
      have hsum : (b.s - pos) + (L - b.s) = L - pos := by omega
      have hcore : (b.s - pos) + (L - b.t) ≤ L - pos := by
        calc
          (b.s - pos) + (L - b.t) ≤ (b.s - pos) + (L - b.s) :=
            Nat.add_le_add_left htail _
          _ = L - pos := hsum
      have hKM : K ≤ M := by
        dsimp [K, M]
        omega
      obtain ⟨qpad, hpad0, hpadM, hpadstep⟩ :=
        HirschProduct.pad_walk (Adj P) hKM qall hall0 (by
          simpa [K, Nat.add_assoc] using hallB) (by
          simpa [K, Nat.add_assoc] using hallstep)
      refine ⟨qpad, hpad0, ?_, ?_⟩
      · simpa [M, blockBudgetSum, Nat.add_assoc] using hpadM
      · simpa [M, blockBudgetSum, Nat.add_assoc] using hpadstep

/-- Global surviving-steps form. The original sequence may be invalid inside
all marked blocks; if every unmarked step survives and the block endpoints
lie in bounded-diameter extreme faces, the whole sequence is repairable with
budget `L + sum B_i`. -/
theorem splice_ordered_face_blocks_of_surviving_steps
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks)
    (hsurvive : ∀ j, j < L → StepOutsideBlocks blocks j →
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧ q (L + blockBudgetSum blocks) = v ∧
      ∀ j < L + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_of_surviving_steps_suffix P u v w hwL
      0 (Nat.zero_le L) blocks hord (by
        intro j _ hjL hout
        exact hsurvive j hjL hout)
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [hw0] using hq0
  · simpa using hqB
  · simpa using hqstep

#print axioms block_start_ge_of_ordered
#print axioms blockBudgetSum_le_length_mul
#print axioms splice_ordered_face_blocks_uniform
#print axioms splice_ordered_face_blocks_of_surviving_steps_suffix
#print axioms splice_ordered_face_blocks_of_surviving_steps

end HirschFaceSplice
