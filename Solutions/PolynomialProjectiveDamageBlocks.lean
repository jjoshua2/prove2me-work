import Solutions.PolynomialFaceReentrySplice

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschFaceSplice

/-- One damage block on an existing parent walk.  The block records an
interval `[s,t]` whose two endpoints lie in an extreme face `F` of intrinsic
diameter at most `B`. -/
structure PathFaceBlock {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) where
  s : ℕ
  t : ℕ
  B : ℕ
  F : Set (EuclideanSpace ℝ (Fin d))
  hst : s ≤ t
  htL : t ≤ L
  hF : IsExtreme ℝ P F
  hFD : DiamLE F B
  hsP : w s ∈ extremePoints ℝ P
  htP : w t ∈ extremePoints ℝ P
  hsF : w s ∈ F
  htF : w t ∈ F

/-- Sum of the intrinsic face-diameter charges in a list of blocks. -/
def blockBudgetSum {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)} :
    List (PathFaceBlock (L := L) P w) → ℕ
  | [] => 0
  | b :: bs => b.B + blockBudgetSum bs

/-- Ordered blocks do not overlap in the original path: after the current
position, the next block starts no earlier than that position, and recursive
processing resumes at the previous block's last endpoint. -/
def BlocksOrderedFrom {d L : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin d))}
    {w : ℕ → EuclideanSpace ℝ (Fin d)}
    (pos : ℕ) : List (PathFaceBlock (L := L) P w) → Prop
  | [] => True
  | b :: bs => pos ≤ b.s ∧ BlocksOrderedFrom b.t bs

/-- Amortized suffix repair for a sequence of disjoint face-supported damage
blocks.  Starting at original path position `pos`, all blocks can be replaced
while paying at most one copy of each block's face diameter.  The original
path length outside the selected blocks is never charged twice.

The deliberately loose budget `L-pos + sum B_i` is the useful invariant for
projective-removal applications: it is independent of the number of local
flip events inside any one block. -/
theorem splice_ordered_face_blocks_suffix
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hwL : w L = v)
    (hwstep : ∀ j < L,
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (pos : ℕ) (hposL : pos ≤ L)
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom pos blocks) :
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
        have hjL : pos + j < L := by omega
        have h := hwstep (pos + j) hjL
        simpa [qs, blockBudgetSum, Nat.add_assoc] using h
  | cons b bs ih =>
      rcases hord with ⟨hposS, hrest⟩

      let qgap : ℕ → EuclideanSpace ℝ (Fin d) := fun j => w (pos + j)
      have hgap0 : qgap 0 = w pos := by simp [qgap]
      have hgapB : qgap (b.s - pos) = w b.s := by
        have hidx : pos + (b.s - pos) = b.s := by omega
        simp [qgap, hidx]
      have hgapstep : ∀ j < b.s - pos,
          qgap j = qgap (j + 1) ∨ Adj P (qgap j) (qgap (j + 1)) := by
        intro j hj
        have hidx : pos + j < L := by omega
        have h := hwstep (pos + j) hidx
        simpa [qgap, Nat.add_assoc] using h

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

      obtain ⟨qrest, hrest0, hrestB, hreststep⟩ :=
        ih b.t b.htL hrest

      obtain ⟨qgf, hgf0, hgfB, hgfstep⟩ :=
        HirschProduct.append_walk (Adj P) qgap qface
          hgap0 hgapB hface0 hfaceB hgapstep hfacestepP
      obtain ⟨qall, hall0, hallB, hallstep⟩ :=
        HirschProduct.append_walk (Adj P) qgf qrest
          hgf0 hgfB hrest0 hrestB hgfstep hreststep

      let K := (b.s - pos) + b.B + (L - b.t + blockBudgetSum bs)
      let M := L - pos + (b.B + blockBudgetSum bs)
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

/-- Global form: a finite ordered family of disjoint damage blocks on a
length-`L` path can all be repaired for total budget at most
`L + sum_i B_i`.  Thus local damage events are amortized by supporting faces,
not by their raw event count. -/
theorem splice_ordered_face_blocks
    {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L,
      w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (blocks : List (PathFaceBlock (L := L) P w))
    (hord : BlocksOrderedFrom 0 blocks) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = u ∧
      q (L + blockBudgetSum blocks) = v ∧
      ∀ j < L + blockBudgetSum blocks,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by
  obtain ⟨q, hq0, hqB, hqstep⟩ :=
    splice_ordered_face_blocks_suffix P u v w hwL hwstep
      0 (Nat.zero_le L) blocks hord
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [hw0] using hq0
  · simpa using hqB
  · simpa using hqstep

#print axioms splice_ordered_face_blocks_suffix
#print axioms splice_ordered_face_blocks

end HirschFaceSplice
