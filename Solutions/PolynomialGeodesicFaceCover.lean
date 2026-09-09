import Mathlib
import Solutions.PolynomialFaceReentrySplice
import Solutions.PolynomialAdjEndpoints

open scoped RealInnerProductSpace BigOperators
open Set Hirsch

set_option maxHeartbeats 5000000
set_option pp.width 100000

noncomputable section

attribute [local instance] Classical.propDecidable

namespace HirschFaceSplice

abbrev Walk {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d)))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w L = v ∧
    ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))

/-- Minimum length among the finite padded graph walks with fixed endpoints.
This is not a non-revisiting-face hypothesis. -/
def IsShortestLength {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d)))
    (u v : EuclideanSpace ℝ (Fin d)) (L : ℕ) : Prop :=
  ∀ K : ℕ, Walk P K u v → L ≤ K

lemma walk_vertices_extreme {d L : ℕ}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (h0 : w 0 ∈ extremePoints ℝ P)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∀ j ≤ L, w j ∈ extremePoints ℝ P := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
    intro hj
    have hjL : j < L := by omega
    rcases hs j hjL with heq | hadj
    · rw [← heq]
      exact ih (by omega)
    · exact HirschPolynomialAccess.adj_right_extreme P hadj

/-- First and last visits to a face on a shortest parent path are at most
its intrinsic graph diameter apart. No face-convexity of shortest paths is
assumed: this follows by replacing the entire intervening subpath. -/
theorem shortest_face_visit_span_le
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F) (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P) (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    t - s ≤ B := by
  have hw' := splice_reentry_through_extreme_face
    d L B s t P F hF hFD u v w hw0 hwL hs hst htL hsP htP hsF htF
  have hle := hmin (s + B + (L - t)) hw'
  omega

/-- Count visits, rather than excursions. The bound includes both endpoints
of the path. It is valid even when the path leaves and re-enters the face. -/
theorem shortest_face_visit_card_le
    (d L B : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F) (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P) :
    ((Finset.range (L + 1)).filter (fun j => w j ∈ F)).card ≤ B + 1 := by
  classical
  let S := (Finset.range (L + 1)).filter (fun j => w j ∈ F)
  change S.card ≤ B + 1
  by_cases hne : S.Nonempty
  · let s := S.min' hne
    have hsS : s ∈ S := Finset.min'_mem S hne
    have hsL : s ≤ L := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hsS).1
      omega
    have hsF : w s ∈ F := (Finset.mem_filter.mp hsS).2
    have hsub : S ⊆ Finset.Icc s (s + B) := by
      intro t ht
      have hst : s ≤ t := Finset.min'_le S t ht
      have htL : t ≤ L := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        omega
      have htF : w t ∈ F := (Finset.mem_filter.mp ht).2
      have hspan := shortest_face_visit_span_le d L B s t P F hF hFD u v
        w hw0 hwL hs hmin hst htL (hverts s hsL) (hverts t htL) hsF htF
      exact Finset.mem_Icc.mpr ⟨hst, by omega⟩
    have hcard : (Finset.Icc s (s + B)).card = B + 1 := by simp [Nat.add_assoc]
    exact (Finset.card_le_card hsub).trans_eq hcard
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hS]

/-- Double-count incidences between vertices of a shortest path and a finite
family of extreme faces. Each path vertex must be covered at least `q`
times; each face is charged at most its intrinsic diameter plus one.

This is a proved geometric certificate, not an assertion that a cheap cover
exists for every polytope. -/
theorem shortest_face_cover_budget
    {ι : Type*} [Fintype ι]
    (d L q : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) (B i))
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hs : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hmin : IsShortestLength P u v L)
    (hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P)
    (hcover : ∀ j ≤ L, q ≤ (Finset.univ.filter (fun i => w j ∈ F i)).card) :
    q * (L + 1) ≤ ∑ i, (B i + 1) := by
  classical
  have hcount :
      (∑ j ∈ Finset.range (L + 1),
        (Finset.univ.filter (fun i => w j ∈ F i)).card) =
      ∑ i, ((Finset.range (L + 1)).filter (fun j => w j ∈ F i)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  calc
    q * (L + 1) = ∑ _j ∈ Finset.range (L + 1), q := by simp [Nat.mul_comm]
    _ ≤ ∑ j ∈ Finset.range (L + 1),
        (Finset.univ.filter (fun i => w j ∈ F i)).card := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcover j (by have := Finset.mem_range.mp hj; omega)
    _ = ∑ i, ((Finset.range (L + 1)).filter (fun j => w j ∈ F i)).card := hcount
    _ ≤ ∑ i, (B i + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact shortest_face_visit_card_le d L (B i) P (F i) (hF i) (hFD i)
        u v w hw0 hwL hs hmin hverts

/-- Connectivity alone supplies a shortest path. A multiplicity-q face cover
then gives the explicit parent graph diameter budget
`(sum_i (B_i+1))/q - 1`.

In particular no numerical diameter bound for the parent is assumed. -/
theorem diamLE_of_face_cover
    {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ (Finset.univ.filter (fun i => x ∈ F i)).card)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L, Walk P L u v) :
    DiamLE P ((∑ i, (B i + 1)) / q - 1) := by
  classical
  intro u hu v hv
  have hex : ∃ L, Walk P L u v := hconnect u hu v hv
  let L := Nat.find hex
  obtain ⟨w, hw0, hwL, hs⟩ := Nat.find_spec hex
  have hmin : IsShortestLength P u v L := by
    intro K hK
    exact Nat.find_min' hex hK
  have hverts : ∀ j ≤ L, w j ∈ extremePoints ℝ P :=
    walk_vertices_extreme P w (by simpa only [hw0] using hu) hs
  have hbudget := shortest_face_cover_budget d L q P F B hF hFD u v
    w hw0 hwL hs hmin hverts (fun j hj => hcover (w j) (hverts j hj))
  have hquot : L + 1 ≤ (∑ i, (B i + 1)) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    simpa only [Nat.mul_comm] using hbudget
  have hL : L ≤ (∑ i, (B i + 1)) / q - 1 := by omega
  exact HirschProduct.pad_walk (Adj P) hL w hw0 hwL hs

#print axioms shortest_face_visit_span_le
#print axioms shortest_face_visit_card_le
#print axioms shortest_face_cover_budget
#print axioms diamLE_of_face_cover

end HirschFaceSplice
