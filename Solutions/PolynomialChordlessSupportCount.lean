import Mathlib
import Solutions.PolynomialShortestRegionRouting

/-!
# Quantitative support count on a chordless used-region path

A shortest region path has no nonconsecutive chords.  This module extracts the
counting consequence needed by the target-cone resource argument: any one used
region has at most two neighbors among the entire path support.  Therefore, for
any selected subset of `r` support labels containing the current label, at
least `r-3` selected labels are distinct from and nonadjacent to the current
label.

The result is graph-theoretic and does not mention polyhedra.  Downstream the
selected subset will be the used final cut labels; nonadjacency will then be
converted to disjoint cut faces and strict ambient rows.
-/

open Set

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace HirschRegionRoute

/-- Support vertices adjacent to a fixed support vertex along the ambient graph.
For a chordless path these can only be the predecessor and successor. -/
def supportNeighborFinset
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (i : V) : Finset V :=
  p.support.toFinset.filter (G.Adj i)

/-- Pointwise form of chordlessness on path support: every graph-neighbor of a
support vertex is its immediate predecessor or successor in the support list.
The predecessor expression saturates at zero; that harmless endpoint value is
only used as a two-element container. -/
theorem chordless_support_neighbor_eq_prev_or_next
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hchord : WalkChordless p)
    {i j : V} (hi : i ∈ p.support) (hj : j ∈ p.support)
    (hij : G.Adj i j) :
    j = p.getVert (p.support.idxOf i - 1) ∨
      j = p.getVert (p.support.idxOf i + 1) := by
  let r := p.support.idxOf i
  let s := p.support.idxOf j
  have hir : p.getVert r = i := by
    simpa [r] using p.getVert_support_idxOf hi
  have hjs : p.getVert s = j := by
    simpa [s] using p.getVert_support_idxOf hj
  have hrlt : r < p.support.length := by
    simpa [r] using List.idxOf_lt_length_of_mem hi
  have hslt : s < p.support.length := by
    simpa [s] using List.idxOf_lt_length_of_mem hj
  have hlen : p.support.length = p.length + 1 := p.length_support
  have hrle : r ≤ p.length := by omega
  have hsle : s ≤ p.length := by omega
  have hrs : r ≠ s := by
    intro hrs
    apply hij.ne
    rw [← hir, ← hjs, hrs]
  by_cases hrslt : r < s
  · have hstep : s = r + 1 := by
      by_contra hne
      have hgap : r + 1 < s := by omega
      have hno := hchord r s hgap hsle
      apply hno
      simpa [hir, hjs] using hij
    right
    rw [← hjs]
    congr 1
    omega
  · have hsr : s < r := by omega
    have hstep : r = s + 1 := by
      by_contra hne
      have hgap : s + 1 < r := by omega
      have hno := hchord s r hgap hrle
      apply hno
      simpa [hir, hjs] using hij.symm
    left
    rw [← hjs]
    congr 1
    omega

/-- A chordless support vertex has at most two graph-neighbors inside the full
walk support. -/
theorem supportNeighborFinset_card_le_two
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hchord : WalkChordless p)
    (i : V) (hi : i ∈ p.support) :
    (supportNeighborFinset p i).card ≤ 2 := by
  let r := p.support.idxOf i
  have hsub : supportNeighborFinset p i ⊆
      ({p.getVert (r - 1), p.getVert (r + 1)} : Finset V) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hjsupp : j ∈ p.support := by
      simpa using hj'.1
    have hadj : G.Adj i j := hj'.2
    rcases chordless_support_neighbor_eq_prev_or_next
      p hchord hi hjsupp hadj with hprev | hnext
    · left
      simpa [r] using hprev
    · right
      simpa [r] using hnext
  have hcard := Finset.card_le_card hsub
  have hpair : ({p.getVert (r - 1), p.getVert (r + 1)} : Finset V).card ≤ 2 := by
    simp
  exact hcard.trans hpair

/-- Selected support labels which are either the current label itself or adjacent
to it.  A chordless path has at most three such selected labels. -/
def blockedSelectedFinset
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) (i : V) : Finset V :=
  cuts ∩ insert i (supportNeighborFinset p i)

/-- Selected labels left after removing the current label and every support
neighbor of it.  These are the labels downstream geometry can turn into strict
rows on the current carrier. -/
def nonneighborSelectedFinset
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V) (i : V) : Finset V :=
  cuts \ blockedSelectedFinset p cuts i

/-- Every surviving selected label is in the supplied selection, is distinct
from the current label, and is graph-nonadjacent to it. -/
theorem mem_nonneighborSelectedFinset
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (cuts : Finset V)
    (hcuts : cuts ⊆ p.support.toFinset)
    (i x : V) (hx : x ∈ nonneighborSelectedFinset p cuts i) :
    x ∈ cuts ∧ x ≠ i ∧ ¬ G.Adj i x := by
  have hxsd := Finset.mem_sdiff.mp hx
  have hxcut : x ∈ cuts := hxsd.1
  have hxnot : x ∉ blockedSelectedFinset p cuts i := hxsd.2
  have hxi : x ≠ i := by
    intro h
    subst x
    apply hxnot
    exact Finset.mem_inter.mpr ⟨hxcut, Finset.mem_insert_self _ _⟩
  have hnadj : ¬ G.Adj i x := by
    intro hadj
    have hxsuppFin : x ∈ p.support.toFinset := hcuts hxcut
    have hxsupp : x ∈ p.support := by simpa using hxsuppFin
    have hxneighbor : x ∈ supportNeighborFinset p i := by
      apply Finset.mem_filter.mpr
      exact ⟨by simpa using hxsupp, hadj⟩
    apply hxnot
    apply Finset.mem_inter.mpr
    exact ⟨hxcut, Finset.mem_insert.mpr (Or.inr hxneighbor)⟩
  exact ⟨hxcut, hxi, hnadj⟩

/-- Quantitative form: from any `r` selected labels on a chordless path, at
least `r-3` are nonneighbors of a fixed selected label. -/
theorem nonneighborSelectedFinset_card_ge_sub_three
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hchord : WalkChordless p)
    (cuts : Finset V) (hcuts : cuts ⊆ p.support.toFinset)
    (i : V) (hi : i ∈ cuts) :
    cuts.card - 3 ≤ (nonneighborSelectedFinset p cuts i).card := by
  have hiSupportFin : i ∈ p.support.toFinset := hcuts hi
  have hiSupport : i ∈ p.support := by simpa using hiSupportFin
  have hneigh : (supportNeighborFinset p i).card ≤ 2 :=
    supportNeighborFinset_card_le_two p hchord i hiSupport
  have hinsert : (insert i (supportNeighborFinset p i)).card ≤ 3 := by
    have h := Finset.card_insert_le i (supportNeighborFinset p i)
    omega
  have hblocked : (blockedSelectedFinset p cuts i).card ≤ 3 := by
    have hsub : blockedSelectedFinset p cuts i ⊆
        insert i (supportNeighborFinset p i) := Finset.inter_subset_right
    exact (Finset.card_le_card hsub).trans hinsert
  have hblockSub : blockedSelectedFinset p cuts i ⊆ cuts :=
    Finset.inter_subset_left
  have hsplit :
      (nonneighborSelectedFinset p cuts i).card +
          (blockedSelectedFinset p cuts i).card = cuts.card := by
    simpa [nonneighborSelectedFinset] using
      Finset.card_sdiff_add_card_eq_card hblockSub
  omega

#print axioms chordless_support_neighbor_eq_prev_or_next
#print axioms supportNeighborFinset_card_le_two
#print axioms mem_nonneighborSelectedFinset
#print axioms nonneighborSelectedFinset_card_ge_sub_three

end HirschRegionRoute
