import Mathlib

/-!
An uncompiled Lean draft accompanying the exact external Q28 computation.

Everything proved here concerns a finite quotient graph, not yet the mission's
Euclidean H-polytope. The missing bridge is: every extreme point is represented
by the listed rational vertices/sign orbits, and every Hirsch.Adj step maps to
QuotientAdj (or stays in the same orbit). Do NOT present this file alone as a
proof of Hirsch.q28_polar_no_length_five_walk.

No sorry, axioms, unsafe code, native_decide, or platform target imports occur.
Compile in the mission's Lean 4.30.0 / Mathlib c5ea003 environment before use.
-/

namespace HirschAudit

/-- A potential increasing by at most one per directed edge is a lower-bound
certificate for the length of every padded walk. -/
theorem potential_le_on_walk {V : Type*}
    (R : V → V → Prop) (potential : V → ℕ)
    (hstep : ∀ x y, R x y → potential y ≤ potential x + 1)
    (w : ℕ → V) (N : ℕ)
    (hw : ∀ j < N, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    potential (w N) ≤ potential (w 0) + N := by
  have aux : ∀ j, j ≤ N → potential (w j) ≤ potential (w 0) + j := by
    intro j
    induction j with
    | zero =>
        intro _
        simp
    | succ j ih =>
        intro hj
        have hjN : j < N := by omega
        have hp := ih (by omega : j ≤ N)
        have hs : potential (w (j + 1)) ≤ potential (w j) + 1 := by
          rcases hw j hjN with heq | hadj
          · rw [← heq]
            omega
          · exact hstep _ _ hadj
        omega
  exact aux N (Nat.le_refl N)

/-- Two feasible values, exactly one tight, give a strictly feasible midpoint. -/
theorem midpoint_strict_of_xor (x y B : ℝ)
    (hx : x ≤ B) (hy : y ≤ B) (hxor : (x = B ↔ y ≠ B)) :
    (x + y) / 2 < B := by
  by_cases ht : x = B
  · have hn : y ≠ B := hxor.mp ht
    have hlt : y < B := by
      by_contra h
      have hge : B ≤ y := le_of_not_gt h
      exact hn (le_antisymm hy hge)
    linarith
  · have hlt : x < B := by
      by_contra h
      have hge : B ≤ x := le_of_not_gt h
      exact ht (le_antisymm hx hge)
    linarith

-- Sign-orbit numbering is exactly that in q28_certificate.json.
def orbitLevel : Fin 20 → ℕ :=
  ![6, 0, 6, 3, 5, 3, 5, 4, 1, 1, 1, 4, 3, 2, 2, 3, 4, 4, 2, 2]

-- An unordered edge list; loops record edges between sign variants in one orbit.
def quotientEdges : List (ℕ × ℕ) :=
  [(0,2),(0,4),(0,6),(1,8),(1,9),(1,10),(2,2),(2,4),
   (3,3),(3,7),(3,13),(3,18),(4,4),(4,7),(4,16),
   (5,5),(5,11),(5,13),(5,16),(6,6),(6,11),(6,17),
   (7,7),(7,12),(7,16),(8,8),(8,13),(8,19),
   (9,9),(9,10),(9,14),(9,18),(10,10),
   (11,11),(11,15),(11,17),(12,12),(12,14),(12,17),
   (13,13),(13,19),(14,14),(14,15),(14,18),
   (15,15),(15,19),(16,16),(16,17),(17,17),
   (18,18),(18,19),(19,19)]

def QuotientAdj (i j : Fin 20) : Prop :=
  (i.val, j.val) ∈ quotientEdges ∨ (j.val, i.val) ∈ quotientEdges

instance (i j : Fin 20) : Decidable (QuotientAdj i j) :=
  inferInstanceAs (Decidable
    ((i.val, j.val) ∈ quotientEdges ∨ (j.val, i.val) ∈ quotientEdges))

/-- Small, kernel-decidable finite check, independent of real geometry. -/
theorem orbitLevel_step :
    ∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1 := by
  decide

/-- Orbit 1 is the positive apex, orbit 0 the negative apex. -/
theorem quotient_no_length_five_walk :
    ¬ ∃ w : ℕ → Fin 20,
      w 0 = 1 ∧ w 5 = 0 ∧
      ∀ j < 5, w j = w (j + 1) ∨ QuotientAdj (w j) (w (j + 1)) := by
  rintro ⟨w, hstart, hend, hwalk⟩
  have h := potential_le_on_walk QuotientAdj orbitLevel orbitLevel_step w 5 hwalk
  rw [hstart, hend] at h
  norm_num [orbitLevel] at h

/-- The second outstanding Q28 target, at the finite-graph level. -/
theorem quotient_no_length_three_between_links :
    ∀ x y : Fin 20,
      ¬ (QuotientAdj 1 x ∧ QuotientAdj y 0 ∧
        ∃ w : ℕ → Fin 20, w 0 = x ∧ w 3 = y ∧
          ∀ j < 3, w j = w (j + 1) ∨ QuotientAdj (w j) (w (j + 1))) := by
  intro x y h
  rcases h with ⟨hux, hyv, w, hw0, hw3, hw⟩
  have hx := orbitLevel_step 1 x hux
  have hy := orbitLevel_step y 0 hyv
  have hp := potential_le_on_walk QuotientAdj orbitLevel orbitLevel_step w 3 hw
  rw [hw0, hw3] at hp
  have hpos : orbitLevel 1 = 0 := by decide
  have hneg : orbitLevel 0 = 6 := by decide
  rw [hpos] at hx
  rw [hneg] at hy
  omega

/-- The only geometric input needed by the finite certificate.

When instantiating with the polytope's vertices, establish the mapToOrbit and
edge-transfer condition from an exhaustive vertex certificate and active-set
rank bounds. Taking R = Hirsch.Adj on all Euclidean points is possible if the
map is given arbitrary values on nonvertices and Adj's endpoints are proved
extreme. Alternatively work with the subtype of extreme points.
-/
theorem no_length_five_of_orbit_map {V : Type*}
    (R : V → V → Prop) (u v : V) (mapToOrbit : V → Fin 20)
    (hu : mapToOrbit u = 1) (hv : mapToOrbit v = 0)
    (hmap : ∀ x y, R x y →
      mapToOrbit x = mapToOrbit y ∨ QuotientAdj (mapToOrbit x) (mapToOrbit y)) :
    ∀ w : ℕ → V,
      ¬ (w 0 = u ∧ w 5 = v ∧
        ∀ j < 5, w j = w (j + 1) ∨ R (w j) (w (j + 1))) := by
  intro w h
  rcases h with ⟨hstart, hend, hw⟩
  apply quotient_no_length_five_walk
  refine ⟨fun j => mapToOrbit (w j), ?_, ?_, ?_⟩
  · simpa [hstart] using hu
  · simpa [hend] using hv
  · intro j hj
    rcases hw j hj with heq | hadj
    · exact Or.inl (congrArg mapToOrbit heq)
    · exact hmap _ _ hadj

end HirschAudit
