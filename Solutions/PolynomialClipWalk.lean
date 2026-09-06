import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialHalfspaceEdge
import Solutions.PolynomialHalfspaceVertex
import Solutions.PolynomialAdjEndpoints
import Solutions.PolynomialProductWalk

open scoped RealInnerProductSpace
open Set Hirsch HirschCut

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschClip

abbrev Walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) (B : ℕ) (u v : E) : Prop :=
  ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
    ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))

lemma adj_reverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Adj P v u := by
  refine ⟨Ne.symm h.1, ?_⟩
  simpa only [segment_symm] using h.2

lemma reverse_steps {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {B : ℕ} (w : ℕ → E)
    (hs : ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∀ j < B, w (B - j) = w (B - (j + 1)) ∨
      Adj P (w (B - j)) (w (B - (j + 1))) := by
  intro j hj
  have hi : B - (j + 1) < B := by omega
  have heq : B - (j + 1) + 1 = B - j := by omega
  rcases hs (B - (j + 1)) hi with h | h
  · exact Or.inl (by simpa only [heq] using h.symm)
  · exact Or.inr (by simpa only [heq] using adj_reverse h)

lemma walk_reverse {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {B : ℕ} {u v : E} (h : Walk P B u v) : Walk P B v u := by
  obtain ⟨w, h0, hB, hs⟩ := h
  refine ⟨fun j => w (B - j), ?_, ?_, reverse_steps P w hs⟩
  · simpa only [Nat.sub_zero] using hB
  · simpa only [Nat.sub_self] using h0

lemma walk_append {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {A B : ℕ} {u v z : E}
    (h1 : Walk P A u v) (h2 : Walk P B v z) : Walk P (A + B) u z := by
  obtain ⟨p, hp0, hpA, hp⟩ := h1
  obtain ⟨q, hq0, hqB, hq⟩ := h2
  exact HirschProduct.append_walk (Adj P) p q hp0 hpA hq0 hqB hp hq

lemma walk_pad {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {A B : ℕ} {u v : E}
    (hAB : A ≤ B) (h : Walk P A u v) : Walk P B u v := by
  obtain ⟨w, h0, hA, hs⟩ := h
  exact HirschProduct.pad_walk (Adj P) hAB w h0 hA hs

variable {d : ℕ}

/-- The equality slice is an extreme subset of the retained halfspace. -/
lemma cut_face_isExtreme
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) :
    IsExtreme ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) (Q ∩ {x | ⟪c, x⟫ = b}) := by
  refine ⟨fun x hx => ⟨hx.1, hx.2.le⟩, ?_⟩
  intro x hx y hy z hz hop
  refine ⟨hx.1, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hcombo⟩ := hop
  have heq : α * ⟪c, x⟫ + β * ⟪c, y⟫ = b := by
    have h : ⟪c, z⟫ = b := hz.2
    rw [← hcombo, inner_combo] at h
    exact h
  have hxle : ⟪c, x⟫ ≤ b := hx.2
  have hyle : ⟪c, y⟫ ≤ b := hy.2
  have hweight : α * b + β * b = b := by
    rw [← add_mul, hαβ, one_mul]
  have hprod : α * (b - ⟪c, x⟫) = 0 := by
    nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hxle),
      mul_nonneg hβ.le (sub_nonneg.mpr hyle)]
  have hslack := (mul_eq_zero.mp hprod).resolve_left hα.ne'
  exact (sub_eq_zero.mp hslack).symm

/-- A cut-face walk lifts to genuine retained-polytope edges. -/
lemma cut_face_walk
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (C : ℕ)
    (hF : DiamLE (Q ∩ {x | ⟪c, x⟫ = b}) C)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (hv : v ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (huc : ⟪c, u⟫ = b) (hvc : ⟪c, v⟫ = b) :
    Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) C u v := by
  have huF : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ = b}) := by
    refine ⟨⟨hu.1.1, huc⟩, ?_⟩
    intro p hp q hq hop
    exact hu.2 ⟨hp.1, hp.2.le⟩ ⟨hq.1, hq.2.le⟩ hop
  have hvF : v ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ = b}) := by
    refine ⟨⟨hv.1.1, hvc⟩, ?_⟩
    intro p hp q hq hop
    exact hv.2 ⟨hp.1, hp.2.le⟩ ⟨hq.1, hq.2.le⟩ hop
  obtain ⟨w, h0, hC, hs⟩ := hF u huF v hvF
  refine ⟨w, h0, hC, ?_⟩
  intro j hj
  rcases hs j hj with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, (cut_face_isExtreme Q c b).trans h.2⟩

/-- Clip a prefix at its first contact, keeping its actual length k rather
than padding to the entire outer-walk budget. This permits two end portions
of the SAME outer walk to share one budget. -/
lemma clip_prefix
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (k : ℕ) (hk : 0 < k) (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hbefore : ∀ l < k, ⟪c, w l⟫ < b)
    (hend : b ≤ ⟪c, w k⟫)
    (hstep : ∀ l < k, w l = w (l + 1) ∨ Adj Q (w l) (w (l + 1))) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧
      ⟪c, z⟫ = b ∧ Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) k (w 0) z := by
  let j := k - 1
  have hjk : j + 1 = k := by dsimp [j]; omega
  have hj : j < k := by omega
  have hleft := hbefore j hj
  have hright : b ≤ ⟪c, w (j + 1)⟫ := by simpa only [hjk] using hend
  have hedge : Adj Q (w j) (w (j + 1)) := by
    rcases hstep j hj with hsame | hadj
    · rw [hsame] at hleft
      exact False.elim ((not_lt_of_ge hright) hleft)
    · exact hadj
  obtain ⟨z, hcz, hzedge⟩ := clip_crossing_edge Q c b hedge hleft hright
  have hzext := HirschPolynomialAccess.adj_right_extreme _ hzedge
  let wp : ℕ → EuclideanSpace ℝ (Fin d) := fun l => if l < k then w l else z
  refine ⟨z, hzext, hcz, wp, ?_, ?_, ?_⟩
  · change (if 0 < k then w 0 else z) = w 0
    exact if_pos hk
  · change (if k < k then w k else z) = z
    exact if_neg (Nat.lt_irrefl k)
  · intro l hl
    by_cases hnext : l + 1 < k
    · rcases hstep l hl with hsame | hadj
      · exact Or.inl (by simpa only [wp, if_pos hl, if_pos hnext] using hsame)
      · have he := retained_edge Q c b hadj (hbefore l hl).le
          (hbefore (l + 1) hnext).le
        exact Or.inr (by simpa only [wp, if_pos hl, if_pos hnext] using he)
    · have hlj : l = j := by omega
      subst l
      exact Or.inr (by simpa only [wp, if_pos hj, if_neg hnext] using hzedge)

/-- An outer vertex strictly retained by the cut reaches the cut face within
B steps. This helper is derived from the variable-length prefix lemma. -/
lemma outer_cut_walk
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ) (B : ℕ)
    (hD : DiamLE Q B)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ Q) (hv : v ∈ extremePoints ℝ Q)
    (huc : ⟪c, u⟫ < b) (hvc : b ≤ ⟪c, v⟫) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧
      ⟪c, z⟫ = b ∧ Walk (Q ∩ {x | ⟪c, x⟫ ≤ b}) B u z := by
  classical
  obtain ⟨w, hw0, hwB, hws⟩ := hD u hu v hv
  have hex : ∃ k : ℕ, k ≤ B ∧ b ≤ ⟪c, w k⟫ :=
    ⟨B, le_rfl, by simpa only [hwB] using hvc⟩
  let k := Nat.find hex
  have hk : k ≤ B ∧ b ≤ ⟪c, w k⟫ := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hbad : b ≤ ⟪c, u⟫ := by simpa only [hk0, hw0] using hk.2
    exact (not_le_of_gt huc) hbad
  have hbefore : ∀ l < k, ⟪c, w l⟫ < b := by
    intro l hl
    by_contra h
    have hmin : k ≤ l := Nat.find_min' hex ⟨by omega, le_of_not_gt h⟩
    omega
  obtain ⟨z, hz, hcz, hwalk⟩ := clip_prefix Q c b k hkpos w hbefore hk.2
    (fun l hl => hws l (by omega))
  refine ⟨z, hz, hcz, ?_⟩
  apply walk_pad hk.1
  simpa only [hw0] using hwalk

#print axioms clip_prefix
#print axioms cut_face_walk

end HirschClip
