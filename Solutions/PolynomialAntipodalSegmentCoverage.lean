import Mathlib

/-!
# Antipodal segment-direction discovery: finite geometric certificate cores

The paper proves that a Minkowski segment factor induces a binary allocation on
vertices, with opposite values at opposite uniquely exposed endpoints. A change
of that allocation forces the edge to be parallel to the factor. These lemmas
formalize the actual row calculation, endpoint coefficient calculation, finite
coverage/count, and the disjoint extra-step lower bound.

NEW UNCOMPILED candidates. The complete polytope-to-allocation bridge and the
lexicographic discovery algorithm are not claimed as formalized by these cores.
No diameter assumption or conjectural short-route oracle occurs below.
-/
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschAntipodalDiscovery

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If a segment allocation changes from its lower to its upper endpoint, the
crossed endpoint segments are feasible. Any common tight row must annihilate g. -/
theorem common_row_annihilates_switch
    (a : E →ₗ[ℝ] ℝ) (b τ : ℝ) (x y g : E) (hτ : 0 < τ)
    (hx : a x = b) (hy : a y = b)
    (hforward : a (x + τ • g) ≤ b)
    (hbackward : a (y - τ • g) ≤ b) : a g = 0 := by
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hx, hy] at hforward hbackward
  nlinarith

/-- The original-row common kernel is exactly the ordinary edge line. This
uses feasible cross endpoints, not an assumption that the candidate is an edge. -/
theorem switch_direction_in_edge_line
    {ι : Type*} (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (τ : ℝ) (x y g : E) (hτ : 0 < τ)
    (hx : ∀ i, a i x = b i) (hy : ∀ i, a i y = b i)
    (hforward : ∀ i, a i (x + τ • g) ≤ b i)
    (hbackward : ∀ i, a i (y - τ • g) ≤ b i)
    (hkernel : ∀ z : E, (∀ i, a i z = 0) → ∃ r : ℝ, z = r • (y-x)) :
    ∃ r : ℝ, g = r • (y-x) := by
  apply hkernel g
  intro i
  exact common_row_annihilates_switch (a i) (b i) τ x y g hτ
    (hx i) (hy i) (hforward i) (hbackward i)

/-- A positive exposing functional forces the upper endpoint of a segment.
The premise is the actual upper support bound at its other feasible endpoint. -/
theorem positive_exposer_forces_upper
    (c : E →ₗ[ℝ] ℝ) (p g : E) (t τ : ℝ)
    (hg : 0 < c g) (ht : t ≤ τ)
    (hmax : c (p + τ • g) ≤ c (p + t • g)) : t = τ := by
  simp only [map_add, map_smul, smul_eq_mul] at hmax
  nlinarith

/-- The opposite sign forces the lower endpoint. -/
theorem negative_exposer_forces_lower
    (c : E →ₗ[ℝ] ℝ) (p g : E) (t : ℝ)
    (hg : c g < 0) (ht : 0 ≤ t)
    (hmax : c p ≤ c (p + t • g)) : t = 0 := by
  simp only [map_add, map_smul, smul_eq_mul] at hmax
  nlinarith

/-- A uniquely exposed point cannot contain a nonzero segment orthogonal to
its exposing functional. Both candidate endpoints are actual feasible points. -/
theorem unique_exposure_excludes_zero_gain
    (P : Set E) (c : E →ₗ[ℝ] ℝ) (x p g : E) (τ t : ℝ)
    (hg : g ≠ 0) (hτ : τ ≠ 0) (hx : x = p + t • g)
    (hp : p ∈ P) (hpt : p + τ • g ∈ P)
    (hunique : ∀ z ∈ P, c z = c x → z = x) : c g ≠ 0 := by
  intro hzero
  have hpvalue : c p = c x := by simp [hx, hzero]
  have htvalue : c (p + τ • g) = c x := by simp [hx, hzero]
  have he₁ := hunique p hp hpvalue
  have he₂ := hunique (p + τ • g) hpt htvalue
  have he : p + τ • g = p := he₂.trans he₁.symm
  have hsmul : τ • g = 0 := by
    have := add_left_cancel (show p + τ • g = p + 0 by simpa using he)
    exact this
  exact hg ((smul_eq_zero.mp hsmul).resolve_left hτ)

/-- Opposite bit values require an actual adjacent change. -/
theorem exists_adjacent_change {α : Type*} (s : ℕ → α) (L : ℕ)
    (h : s 0 ≠ s L) : ∃ i : ℕ, i < L ∧ s i ≠ s (i+1) := by
  induction L with
  | zero => exact False.elim (h rfl)
  | succ L ih =>
    by_cases he : s L = s (L+1)
    · have h' : s 0 ≠ s L := fun hz => h (hz.trans he)
      obtain ⟨i, hi, hs⟩ := ih h'
      exact ⟨i, by omega, hs⟩
    · exact ⟨L, by omega, he⟩

/-- One walk direction labels every factor transition. This is set coverage,
so it proves finiteness even before assuming there are finitely many factors. -/
theorem direction_set_finite_of_cover
    {D : Type*} (L : ℕ) (edgeDir : Fin L → D) (S : Set D)
    (hcover : ∀ g ∈ S, ∃ i : Fin L, edgeDir i = g) : S.Finite := by
  apply (Set.finite_range edgeDir).subset
  intro g hg
  exact hcover g hg

/-- Distinct factor directions require distinct edge positions. This works for
ANY actual walk; monotonicity is not needed for the lower bound or coverage. -/
theorem changing_factor_count_le_length
    {F D : Type*} [Fintype F] (L : ℕ)
    (edgeDir : Fin L → D) (factorDir : F → D)
    (hinj : Function.Injective factorDir) (side : F → ℕ → Bool)
    (hends : ∀ f, side f 0 ≠ side f L)
    (hswitch : ∀ f i (hi : i < L), side f i ≠ side f (i+1) →
      edgeDir ⟨i,hi⟩ = factorDir f) : Fintype.card F ≤ L := by
  classical
  have hc : ∀ f, ∃ i : Fin L, edgeDir i = factorDir f := by
    intro f
    obtain ⟨i,hi,hs⟩ := exists_adjacent_change (side f) L (hends f)
    exact ⟨⟨i,hi⟩,hswitch f i hi hs⟩
  choose chosen hchosen using hc
  have hchosen_inj : Function.Injective chosen := by
    intro f g h
    apply hinj
    calc
      factorDir f = edgeDir (chosen f) := (hchosen f).symm
      _ = edgeDir (chosen g) := congrArg edgeDir h
      _ = factorDir g := hchosen g
  simpa using Fintype.card_le_of_injective chosen hchosen_inj

/-- An additional step outside every factor direction is disjoint from all
required factor switches. In the application a linear functional annihilates
all factors but separates the endpoints, forcing such an extra step. -/
theorem changing_factor_count_plus_extra
    {F D : Type*} [Fintype F] (L : ℕ)
    (edgeDir : Fin L → D) (factorDir : F → D)
    (hinj : Function.Injective factorDir)
    (hcover : ∀ f, ∃ i : Fin L, edgeDir i = factorDir f)
    (extra : Fin L) (hextra : ∀ f, edgeDir extra ≠ factorDir f) :
    Fintype.card F + 1 ≤ L := by
  classical
  choose chosen hchosen using hcover
  let f : Option F → Fin L := fun x => match x with
    | none => extra
    | some a => chosen a
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b =>
        have h : extra = chosen b := hxy
        exact False.elim (hextra b (by rw [h]; exact hchosen b))
    | some a =>
      cases y with
      | none =>
        have h : chosen a = extra := hxy
        exact False.elim (hextra a (by rw [←h]; exact hchosen a))
      | some b =>
        have h : chosen a = chosen b := hxy
        have hab : a = b := hinj ((hchosen a).symm.trans
          ((congrArg edgeDir h).trans (hchosen b)))
        simpa using congrArg Option.some hab
  simpa using Fintype.card_le_of_injective f hf

#print axioms common_row_annihilates_switch
#print axioms switch_direction_in_edge_line
#print axioms positive_exposer_forces_upper
#print axioms negative_exposer_forces_lower
#print axioms unique_exposure_excludes_zero_gain
#print axioms exists_adjacent_change
#print axioms direction_set_finite_of_cover
#print axioms changing_factor_count_le_length
#print axioms changing_factor_count_plus_extra
end HirschAntipodalDiscovery
