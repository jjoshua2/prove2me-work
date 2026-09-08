import Solutions.CircuitSlackBounded
import Solutions.CircuitSlackWalkEquiv
import Solutions.CircuitSlackExtreme

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- A nonnegative affine slice, independent of any H-presentation. Every
finite-dimensional linear subspace can be presented as a matrix kernel. -/
def StandardSlice {n : ℕ} (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ) :
    Set (Fin n → ℝ) := {s | s - c ∈ K ∧ ∀ i, 0 ≤ s i}

/-- Sign-reversed elementary direction, as in SlackCircuitStep. Nonzero
rescaling invariance identifies this with the source's forward direction. -/
def StandardCircuitStep {n : ℕ} (K : Submodule ℝ (Fin n → ℝ))
    (c x y : Fin n → ℝ) : Prop :=
  x ∈ StandardSlice K c ∧ y ∈ StandardSlice K c ∧
    IsElementaryIn K (x - y) ∧
    ∀ t : ℝ, 1 < t → x + t • (y - x) ∉ StandardSlice K c

def StandardCircuitWalk {n : ℕ} (K : Submodule ℝ (Fin n → ℝ))
    (c : Fin n → ℝ) (L : ℕ) (u v : Fin n → ℝ) : Prop :=
  ∃ w : ℕ → (Fin n → ℝ), w 0 = u ∧ w L = v ∧
    (∀ j ≤ L, w j ∈ StandardSlice K c) ∧
    ∀ j < L, w j = w (j + 1) ∨ StandardCircuitStep K c (w j) (w (j + 1))

theorem slackPoly_eq_standardSlice {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    SlackPoly a b = StandardSlice (LinearMap.range (rowMap a)) b := by
  ext s
  constructor
  · rintro ⟨⟨x, rfl⟩, hs⟩
    refine ⟨⟨-x, ?_⟩, hs⟩
    funext i
    change ⟪a i, -x⟫ = (b i - ⟪a i, x⟫) - b i
    rw [inner_neg_right]
    ring
  · rintro ⟨⟨g, hg⟩, hs⟩
    refine ⟨⟨-g, ?_⟩, hs⟩
    funext i
    have hi := congrFun hg i
    change ⟪a i, g⟫ = s i - b i at hi
    change s i = b i - ⟪a i, -g⟫
    rw [inner_neg_right]
    linarith

theorem slackCircuitWalk_iff_standardCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (L : ℕ) (u v : Fin n → ℝ) :
    SlackCircuitWalk a b L u v ↔
      StandardCircuitWalk (LinearMap.range (rowMap a)) b L u v := by
  simp only [SlackCircuitWalk, StandardCircuitWalk, SlackCircuitStep,
    StandardCircuitStep, slackPoly_eq_standardSlice]

/-- Complete bounded H-presentation to nonnegative-affine-slice walk bridge. -/
theorem bounded_rowCircuitWalk_iff_standardCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    RowCircuitWalk a b L u v ↔
      StandardCircuitWalk (LinearMap.range (rowMap a)) b L
        (slack a b u) (slack a b v) := by
  exact (rowCircuitWalk_iff_slackCircuitWalk a b
    (rowMap_injective_of_bounded a b hb x hx) L u v).trans
      (slackCircuitWalk_iff_standardCircuitWalk a b L _ _)

theorem rowCircuitWalk_mono {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {L M : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (h : RowCircuitWalk a b L u v) (hLM : L ≤ M) :
    RowCircuitWalk a b M u v := by
  obtain ⟨w, hw0, hwL, hf, hs⟩ := h
  refine ⟨fun j => w (min j L), ?_, ?_, ?_, ?_⟩
  · simpa using hw0
  · simpa only [Nat.min_eq_right hLM] using hwL
  · intro j _
    exact hf _ (Nat.min_le_right _ _)
  · intro j _
    by_cases hj : j < L
    · simpa only [Nat.min_eq_left (Nat.le_of_lt hj),
        Nat.min_eq_left (Nat.succ_le_iff.mpr hj)] using hs j hj
    · left
      rw [Nat.min_eq_right (Nat.le_of_not_gt hj),
        Nat.min_eq_right (by omega : L ≤ j + 1)]

/-- Local source hypothesis, NOT an asserted theorem or an Open platform child.
A cubic relaxation of Natura's standard-form circuit-diameter conclusion.
The source's constructive proof still needs formalization, including the
support-loss reference reset documented in research/NaturaSourceAudit.md. -/
def StandardCubicCircuitBound : Prop :=
  ∃ C : ℕ, ∀ (n : ℕ) (K : Submodule ℝ (Fin n → ℝ)) (c : Fin n → ℝ),
    ∀ u ∈ Set.extremePoints ℝ (StandardSlice K c),
    ∀ v ∈ Set.extremePoints ℝ (StandardSlice K c),
      StandardCircuitWalk K c (C * n ^ 3) u v

/-- Admission-free conditional theorem with the exact existing Child A result.
It DOES NOT prove its StandardCubicCircuitBound hypothesis. No target imports. -/
theorem cubic_circuit_walk_bound_of_standard
    (hsource : StandardCubicCircuitBound) :
    ∃ C : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
        Hirsch.Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hirsch.Hpoly a b ∧
        Hirsch.RowPresentationIrredundant (fun j => a (e j)) (fun j => b (e j)) ∧
        Hirsch.StrictlyFeasibleRows (fun j => a (e j)) (fun j => b (e j)) ∧
        Hirsch.RowCircuitWalk (fun j => a (e j)) (fun j => b (e j))
          (C * (m + d) ^ 3) u v := by
  obtain ⟨C, hC⟩ := hsource
  refine ⟨C, ?_⟩
  intro d n a b hb u hu v hv hsep
  obtain ⟨m, hmn, e, hP, hirr, hstrict⟩ :=
    exists_irredundant_strict_model d n a b u v hu.1 hv.1 hsep
  let ar := fun j => a (e j)
  let br := fun j => b (e j)
  have hP' : Hpoly ar br = Hpoly a b := hP
  have hb' : Bornology.IsBounded (Hpoly ar br) := by rwa [hP']
  have hu' : u ∈ Set.extremePoints ℝ (Hpoly ar br) := by rwa [hP']
  have hv' : v ∈ Set.extremePoints ℝ (Hpoly ar br) := by rwa [hP']
  have hinj := rowMap_injective_of_bounded ar br hb' u hu'.1
  have hsu := slack_mem_extremePoints_of_mem_extremePoints ar br hinj u hu'
  have hsv := slack_mem_extremePoints_of_mem_extremePoints ar br hinj v hv'
  rw [slackPoly_eq_standardSlice] at hsu hsv
  have hw := hC m (LinearMap.range (rowMap ar)) br (slack ar br u) hsu
    (slack ar br v) hsv
  have hrow := (bounded_rowCircuitWalk_iff_standardCircuitWalk ar br hb' u hu'.1
    (C * m ^ 3) u v).mpr hw
  refine ⟨m, hmn, e, hP, hirr, hstrict, ?_⟩
  exact rowCircuitWalk_mono ar br hrow
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.le_add_right m d)))

#print axioms slackPoly_eq_standardSlice
#print axioms bounded_rowCircuitWalk_iff_standardCircuitWalk
#print axioms rowCircuitWalk_mono
#print axioms cubic_circuit_walk_bound_of_standard
end HirschCircuit
