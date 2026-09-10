import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_larman_bound
import Theorems.Thm_Hirsch_vertex_tight_rows_span
import Solutions.PolynomialSeparatedRows

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Both endpoints of an `Adj` edge are vertices.  This is implicit in the
mathematical meaning of `Adj`; the model definition only stores extremeness of
the whole segment, so we expose the endpoint consequence here. -/
lemma adj_right_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {u z : EuclideanSpace ℝ (Fin d)}
    (hadj : Adj P u z) : z ∈ extremePoints ℝ P := by
  rcases hadj with ⟨huz, hseg⟩
  have hzP : z ∈ P := hseg.subset (right_mem_segment ℝ u z)
  refine ⟨hzP, ?_⟩
  intro x hxP y hyP hzopen
  have hxseg : x ∈ segment ℝ u z :=
    hseg.left_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  have hyseg : y ∈ segment ℝ u z :=
    hseg.right_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hxseg
  obtain ⟨c, e, hc, he, hce, hy⟩ := hyseg
  obtain ⟨s, t, hs, ht, hst, hxy⟩ := hzopen
  have hcoeff : s * a + t * c + (s * b + t * e) = 1 := by
    calc
      s * a + t * c + (s * b + t * e) = s * (a + b) + t * (c + e) := by ring
      _ = s * 1 + t * 1 := by rw [hab, hce]
      _ = 1 := by linarith
  have hlin0 : s • x + t • y - z = 0 := sub_eq_zero.mpr hxy
  rw [← hx, ← hy] at hlin0
  have hrewrite :
      s • (a • u + b • z) + t • (c • u + e • z) - z =
        (s * a + t * c) • u + (s * b + t * e - 1) • z := by
    module
  have hlin1 :
      (s * a + t * c) • u + (s * b + t * e - 1) • z = 0 := by
    rw [← hrewrite]
    exact hlin0
  have hB : s * b + t * e - 1 = -(s * a + t * c) := by
    linarith [hcoeff]
  rw [hB] at hlin1
  have hlin : (s * a + t * c) • (u - z) = 0 := by
    simpa [smul_sub, sub_eq_add_neg] using hlin1
  have hcoef : s * a + t * c = 0 :=
    (smul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr huz)
  have ha0 : a = 0 := by
    nlinarith [mul_nonneg ht.le hc]
  have hb1 : b = 1 := by linarith [hab]
  rw [ha0, zero_smul, zero_add, hb1, one_smul] at hx
  exact hx.symm

/-- A padded walk between distinct endpoints contains a first genuine edge,
and that edge leaves its starting vertex. -/
lemma first_adjacent_from_start
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {u v : EuclideanSpace ℝ (Fin d)} {B : ℕ}
    (huv : u ≠ v)
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwB : w B = v)
    (hwstep : ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ z, Adj P u z := by
  classical
  have hex : ∃ j, j < B ∧ w j ≠ w (j + 1) := by
    by_contra h
    push Not at h
    have hall : ∀ j ≤ B, w j = w 0 := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
        have hjB : j < B := by omega
        have heq : w j = w (j + 1) := h j hjB
        rw [← heq]
        exact ih (by omega)
    apply huv
    calc
      u = w 0 := hw0.symm
      _ = w B := (hall B (le_refl B)).symm
      _ = v := hwB
  let j := Nat.find hex
  have hj : j < B ∧ w j ≠ w (j + 1) := Nat.find_spec hex
  have hprefix : ∀ k < j, w k = w (k + 1) := by
    intro k hkj
    by_contra hk
    have hkB : k < B := lt_trans hkj hj.1
    have hkprop : k < B ∧ w k ≠ w (k + 1) := ⟨hkB, hk⟩
    exact (not_lt_of_ge (Nat.find_min' hex hkprop)) hkj
  have hwj : w j = u := by
    have hconst : ∀ k ≤ j, w k = w 0 := by
      intro k hkj
      induction k with
      | zero => rfl
      | succ k ih =>
        have hklt : k < j := by omega
        rw [← hprefix k hklt]
        exact ih (by omega)
    exact (hconst j (le_refl j)).trans hw0
  have hadj : Adj P (w j) (w (j + 1)) := by
    rcases hwstep j hj.1 with heq | hadj
    · exact False.elim (hj.2 heq)
    · exact hadj
  exact ⟨w (j + 1), by simpa [hwj] using hadj⟩

/-- At the balanced boundary `n = 2d`, separated extreme vertices partition
all rows into `d` source facets and `d` target facets.  Consequently every
genuine edge leaving the source must enter at least one target facet.

This proves existential target-face access in one edge in the exact Dantzig
regime. -/
theorem balanced_separated_some_target_facet_one_step
    (d : ℕ)
    (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d))
    (b : Fin (2 * d) → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hsep : ∀ j, a j ≠ 0 →
      ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) :
    ∃ (i : Fin (2 * d)) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      Adj (Hpoly a b) u z := by
  classical
  let SU : Finset (Fin (2 * d)) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, u⟫ = b i)
  let SV : Finset (Fin (2 * d)) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, v⟫ = b i)
  have hU : d ≤ SU.card := by
    simpa [SU] using nonzero_tight_rows_card_ge_dim a b u hu
  have hV : d ≤ SV.card := by
    simpa [SV] using nonzero_tight_rows_card_ge_dim a b v hv
  have hdisj : Disjoint SU SV := by
    refine Finset.disjoint_left.2 ?_
    intro j hju hjv
    have huj := (Finset.mem_filter.1 hju).2
    have hvj := (Finset.mem_filter.1 hjv).2
    rcases hsep j huj.1 with hnotu | hnotv
    · exact hnotu huj.2
    · exact hnotv hvj.2
  have hsum : SU.card + SV.card = 2 * d := by
    have hunion : (SU ∪ SV).card = SU.card + SV.card :=
      Finset.card_union_of_disjoint hdisj
    have hle : (SU ∪ SV).card ≤ 2 * d := by
      have hsub : SU ∪ SV ⊆ (Finset.univ : Finset (Fin (2 * d))) := by simp
      simpa using Finset.card_le_card hsub
    omega
  have hUcard : SU.card = d := by omega
  have hVcard : SV.card = d := by omega
  have hcover : SU ∪ SV = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hUcard, hVcard]
    omega
  have hne : (Hpoly a b).Nonempty := ⟨u, hu.1⟩
  obtain ⟨w, hw0, hwB, hwstep⟩ :=
    Hirsch.larman_bound d (2 * d) a b hne hbd u hu v hv
  obtain ⟨z, huz⟩ :=
    first_adjacent_from_start (Hpoly a b) huv w hw0 hwB hwstep
  have hzext : z ∈ extremePoints ℝ (Hpoly a b) :=
    adj_right_extreme (Hpoly a b) huz
  have htarget : ∃ i, i ∈ SV ∧ ⟪a i, z⟫ = b i := by
    by_contra h
    push Not at h
    have hzNoV : ∀ i, i ∈ SV → ⟪a i, z⟫ ≠ b i := h
    let SZ : Finset (Fin (2 * d)) :=
      Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, z⟫ = b i)
    have hZ : d ≤ SZ.card := by
      simpa [SZ] using nonzero_tight_rows_card_ge_dim a b z hzext
    have hZsub : SZ ⊆ SU := by
      intro i hiZ
      have hi := (Finset.mem_filter.1 hiZ).2
      have hiuniv : i ∈ SU ∪ SV := by rw [hcover]; simp
      rcases Finset.mem_union.1 hiuniv with hiU | hiV
      · exact hiU
      · exact False.elim (hzNoV i hiV hi.2)
    have hZle : SZ.card ≤ SU.card := Finset.card_le_card hZsub
    have hZU : SZ = SU :=
      Finset.eq_of_subset_of_card_le hZsub (by omega)
    have horth : ∀ j, ⟪a j, u⟫ = b j → ⟪a j, z - u⟫ = 0 := by
      intro j hju
      by_cases haj : a j = 0
      · simp [haj]
      · have hjU : j ∈ SU := by simp [SU, haj, hju]
        have hjZ : j ∈ SZ := by simpa [hZU] using hjU
        have hjtightZ : ⟪a j, z⟫ = b j := (Finset.mem_filter.1 hjZ).2.2
        simp [inner_sub_right, hjtightZ, hju]
    have hzu0 := Hirsch.vertex_tight_rows_span d (2 * d) a b u hu (z - u) horth
    have hzu : z = u := sub_eq_zero.mp hzu0
    exact huz.1 hzu.symm
  obtain ⟨i, hiV, hiz⟩ := htarget
  have hi := (Finset.mem_filter.1 hiV).2
  exact ⟨i, z, hi.1, hi.2, hzext, hiz, huz⟩

end HirschPolynomialAccess
