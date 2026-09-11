import Solutions.PolynomialProductWalk
import Solutions.PolynomialAffineDiameterTransport
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Bornology.Constructions
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschRowBlocks

/-- An algebraic row-block certificate identifies the entire feasible set with
an actual Cartesian product. Unlike a face-cover certificate, every combination
of factor points is feasible; there is no missing portal or compatibility premise. -/
theorem image_hpoly_eq_pi_of_row_blocks
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫) :
    T '' Hpoly a b = Set.univ.pi
      (fun i => Hpoly (A i) (fun j => b (e ⟨i, j⟩))) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_univ_pi]
    intro i j
    have hr := hrows (T x) i j
    rw [T.symm_apply_apply] at hr
    rw [← hr]
    exact hx (e ⟨i, j⟩)
  · intro hz
    rw [Set.mem_univ_pi] at hz
    refine ⟨T.symm z, ?_, T.apply_symm_apply z⟩
    intro r
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective r
    rw [hrows]
    exact hz i j

/-- Factor boundedness is inherited from a nonempty bounded parent; it is not
an additional geometric assumption supplied by the certificate. -/
theorem factors_bounded_of_row_blocks
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty) :
    ∀ i, Bornology.IsBounded (Hpoly (A i) (fun j => b (e ⟨i, j⟩))) := by
  have himage := image_hpoly_eq_pi_of_row_blocks dims counts a b T e A hrows
  have hb : Bornology.IsBounded (T '' Hpoly a b) :=
    T.toContinuousLinearEquiv.toContinuousLinearMap.lipschitz.isBounded_image hbd
  have hn : (T '' Hpoly a b).Nonempty := hne.image T
  rw [himage] at hb hn
  exact (Bornology.isBounded_pi_of_nonempty hn).mp hb

/-- The row and coordinate equivalences force additive presentation excess.
The lower row-count checks make natural subtraction honest. -/
theorem row_block_excess_sum
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (hcount : ∀ i, dims i ≤ counts i) :
    (∑ i, (counts i - dims i)) = n - d := by
  have hd : d = ∑ i, dims i := by
    simpa [Module.finrank_pi_fintype] using T.finrank_eq
  have hn : (∑ i, counts i) = n := by
    simpa using Fintype.card_congr e
  have hsplit : (∑ i, counts i) = (∑ i, dims i) +
      ∑ i, (counts i - dims i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (Nat.add_sub_of_le (hcount i)).symm
  omega

/-- A high-excess parent is Hirsch-bounded when each algebraically independent
row block has excess at most three. The only imported diameter input is the
already-proved low-excess H-polyhedron theorem, supplied explicitly so no
platform theorem stub or unproved global claim enters the axiom closure.
There is NO restriction on total `n-d` or on the number of factors. -/
theorem hpoly_diamLE_excess_of_small_row_blocks
    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n - d))
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3) :
    DiamLE (Hpoly a b) (n - d) := by
  have hfactorbd := factors_bounded_of_row_blocks dims counts a b T e A hrows hbd hne
  have hD := HirschProduct.diamLE_pi
    (fun i => Hpoly (A i) (fun j => b (e ⟨i, j⟩)))
    (fun i => counts i - dims i)
    (fun i => hsmall (A i) (fun j => b (e ⟨i, j⟩)) (hfactorbd i) (hsmallcount i))
  rw [row_block_excess_sum dims counts T e hcount] at hD
  rw [← image_hpoly_eq_pi_of_row_blocks dims counts a b T e A hrows] at hD
  exact (Hirsch.affineEquiv_diamLE_image_iff T.toAffineEquiv (Hpoly a b) (n - d)).mp hD

#print axioms image_hpoly_eq_pi_of_row_blocks
#print axioms factors_bounded_of_row_blocks
#print axioms row_block_excess_sum
#print axioms hpoly_diamLE_excess_of_small_row_blocks

end HirschRowBlocks
