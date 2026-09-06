import Mathlib
import Theorems.Thm_Hirsch_larman_bound
import Solutions.PolynomialAdjEndpoints
import Solutions.PolynomialCommonFaceLarman

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Along any padded walk, a predicate false at the start and true at the end
has a first genuine edge crossing from false to true. -/
lemma first_hit_edge
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (T : EuclideanSpace ℝ (Fin d) → Prop) [DecidablePred T]
    {B : ℕ}
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (h0 : ¬ T (w 0)) (hB : T (w B))
    (hstep : ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ j < B, ¬ T (w j) ∧ T (w (j + 1)) ∧ Adj P (w j) (w (j + 1)) := by
  classical
  have hex : ∃ k : ℕ, k ≤ B ∧ T (w k) := ⟨B, le_rfl, hB⟩
  let k := Nat.find hex
  have hk : k ≤ B ∧ T (w k) := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    apply h0
    simpa [h] using hk.2
  obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjB : j < B := by omega
  have hjnot : ¬ T (w j) := by
    intro hjT
    have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, hjT⟩
    omega
  have hjnext : T (w (j + 1)) := by
    simpa [hjk] using hk.2
  have hadj : Adj P (w j) (w (j + 1)) := by
    rcases hstep j hjB with heq | hadj
    · exfalso
      apply hjnot
      rw [heq]
      exact hjnext
    · exact hadj
  exact ⟨j, hjB, hjnot, hjnext, hadj⟩

/-- A separated pair reaches some nonzero target supporting row in a number
of steps exponential only in the row excess `n - 2*d`. This improves the
ambient-dimension Larman estimate in small-excess regimes, not uniformly.
It is not a polynomial Hirsch proof or access to an arbitrarily prescribed row. -/
theorem target_facet_access_excess_bound
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧
        w (n * 2 ^ ((n - 2 * d) - 3) + 1) = z ∧
        ∀ j < n * 2 ^ ((n - 2 * d) - 3) + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  classical
  let P := Hpoly a b
  let T : EuclideanSpace ℝ (Fin d) → Prop := fun y =>
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧ ⟪a i, y⟫ = b i
  have hT0 : ¬ T u := by
    rintro ⟨i, hai, hiv, hiu⟩
    rcases hsep i hai with hnu | hnv
    · exact hnu hiu
    · exact hnv hiv
  have hexTarget : ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by
    by_contra hn
    have hrowzero : ∀ i, ⟪a i, v⟫ = b i → a i = 0 := by
      intro i hit
      by_contra hne
      exact hn ⟨i, hne, hit⟩
    have horth : ∀ i, ⟪a i, v⟫ = b i → ⟪a i, u - v⟫ = 0 := by
      intro i hit
      rw [hrowzero i hit, inner_zero_left]
    have hdiff := vertex_tight_rows_span_checked d n a b v hv (u - v) horth
    exact huv (sub_eq_zero.mp hdiff)
  obtain ⟨it, hait, hitv⟩ := hexTarget
  have hTv : T v := ⟨it, hait, hitv, hitv⟩
  have hPne : P.Nonempty := ⟨u, hu.1⟩
  obtain ⟨wg, hwg0, hwgB, hwgstep⟩ :=
    Hirsch.larman_bound d n a b hPne hbd u hu v hv
  have hTstart : ¬ T (wg 0) := by simpa [hwg0] using hT0
  have hTend : T (wg (n * 2 ^ (d - 3))) := by simpa [hwgB] using hTv
  obtain ⟨j, hjB, hxavoid, hztarget, hxz⟩ :=
    first_hit_edge P T wg hTstart hTend hwgstep
  let x := wg j
  let z := wg (j + 1)
  have hxz' : Adj P x z := by simpa [x, z] using hxz
  have hxext : x ∈ extremePoints ℝ P := adj_left_extreme P hxz'
  have hzext : z ∈ extremePoints ℝ P := adj_right_extreme P hxz'
  have hxavoid' : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i := by
    intro i hai hiv hix
    apply hxavoid
    exact ⟨i, hai, hiv, by simpa [x] using hix⟩
  obtain ⟨w0, hw00, hw0x, hw0step⟩ :=
    target_avoider_common_face_walk a b u v x hbd hu hv hxext hsep hxavoid'
  obtain ⟨i, hai, hiv, hiz⟩ := hztarget
  let L := n * 2 ^ ((n - 2 * d) - 3)
  let w : ℕ → EuclideanSpace ℝ (Fin d) := fun k =>
    if k ≤ L then w0 k else z
  refine ⟨i, z, hai, hiv, hzext, ?_, w, ?_, ?_, ?_⟩
  · simpa [z] using hiz
  · have h0L : 0 ≤ L := Nat.zero_le _
    simp [w, h0L, hw00]
  · change (if L + 1 ≤ L then w0 (L + 1) else z) = z
    exact if_neg (by omega)
  · intro k hk
    by_cases hkL : k < L
    · have hkle : k ≤ L := by omega
      have hk1le : k + 1 ≤ L := by omega
      simpa [w, hkle, hk1le] using hw0step k hkL
    · have hkEq : k = L := by omega
      subst k
      have hLle : L ≤ L := le_rfl
      have hLnle : ¬ L + 1 ≤ L := by omega
      have hleft : w L = x := by
        change (if L ≤ L then w0 L else z) = x
        rw [if_pos hLle]
        exact hw0x
      have hright : w (L + 1) = z := by
        change (if L + 1 ≤ L then w0 (L + 1) else z) = z
        exact if_neg hLnle
      exact Or.inr (by simpa [hleft, hright] using hxz')

end HirschPolynomialAccess
