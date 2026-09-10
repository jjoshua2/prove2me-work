import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_larman_bound
import Solutions.PolynomialAffineProductFace
import Solutions.PolynomialBoundaryWalk

open scoped RealInnerProductSpace
open Set Hirsch HirschProduct

set_option maxHeartbeats 5000000

noncomputable section

/-- Prescribed supporting-face access via affine product faces.
For every edge entering the fixed row i, its outside endpoint and u must lie
in an affine product face. Factor dimensions are bounded by r, and the TOTAL
number of factor describing rows is at most M. Total dimension and total
residual rank may be arbitrarily large. This is a structural restriction,
not an assertion that every polytope has such product faces. -/
theorem solution
    (d n M r : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (i : Fin n) (hiv : ⟪a i, v⟫ = b i)
    (hfactor : ∀ x z, Adj (Hpoly a b) x z →
      ⟪a i, x⟫ ≠ b i → ⟪a i, z⟫ = b i →
      ∃ (m : ℕ) (ds ns : Fin m → ℕ)
        (aa : (k : Fin m) → Fin (ns k) → EuclideanSpace ℝ (Fin (ds k)))
        (bb : (k : Fin m) → Fin (ns k) → ℝ)
        (f : ((k : Fin m) → EuclideanSpace ℝ (Fin (ds k))) →ᵃ[ℝ]
          EuclideanSpace ℝ (Fin d)),
        Function.Injective f ∧
        IsExtreme ℝ (Hpoly a b) (f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k))) ∧
        u ∈ f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k)) ∧
        x ∈ f '' Set.univ.pi (fun k => Hpoly (aa k) (bb k)) ∧
        (∀ k, Bornology.IsBounded (Hpoly (aa k) (bb k))) ∧
        (∀ k, ds k ≤ r) ∧ (∑ k, ns k) ≤ M) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (M * 2 ^ (r - 3) + 1) = z ∧
        ∀ j < M * 2 ^ (r - 3) + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  classical
  let B : ℕ := M * 2 ^ (r - 3)
  have hconn : ∃ D : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w D = v ∧
      ∀ j < D, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
    obtain ⟨w, hw0, hwD, hws⟩ :=
      Hirsch.larman_bound d n a b ⟨u, hu.1⟩ hbd u hu v hv
    exact ⟨n * 2 ^ (d - 3), w, hw0, hwD, hws⟩
  apply access_of_boundary_walks (Hpoly a b) u v hu
    (fun y => ⟪a i, y⟫ = b i) hiv B hconn
  intro x z hxz hxi hzi
  obtain ⟨m, ds, ns, aa, bb, f, hinj, hface, hui, hxi', hbounded, hdim, hrows⟩ :=
    hfactor x z hxz hxi hzi
  let Q : Set ((k : Fin m) → EuclideanSpace ℝ (Fin (ds k))) :=
    Set.univ.pi (fun k => Hpoly (aa k) (bb k))
  have hQne : Q.Nonempty := by
    obtain ⟨q, hq, _⟩ := hui
    exact ⟨q, hq⟩
  have hne (k : Fin m) : (Hpoly (aa k) (bb k)).Nonempty :=
    ⟨hQne.choose k, (Set.mem_univ_pi.mp hQne.choose_spec) k⟩
  let L : ℕ := ∑ k, ns k * 2 ^ (ds k - 3)
  have hDQ : DiamLE Q L :=
    diamLE_pi (fun k => Hpoly (aa k) (bb k))
      (fun k => ns k * 2 ^ (ds k - 3))
      (fun k => Hirsch.larman_bound (ds k) (ns k) (aa k) (bb k) (hne k) (hbounded k))
  have hLB : L ≤ B := by
    calc
      L ≤ ∑ k, ns k * 2 ^ (r - 3) := by
        apply Finset.sum_le_sum
        intro k _
        exact Nat.mul_le_mul_left (ns k)
          (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right (hdim k) 3))
      _ = (∑ k, ns k) * 2 ^ (r - 3) := by rw [Finset.sum_mul]
      _ ≤ B := Nat.mul_le_mul_right (2 ^ (r - 3)) hrows
  have hxext := HirschPolynomialAccess.adj_left_extreme (Hpoly a b) hxz
  obtain ⟨w, hw0, hwL, hws⟩ :=
    walk_via_affine_face (Hpoly a b) Q f hinj hface u x hu hxext hui hxi' L hDQ
  exact HirschProduct.pad_walk (Adj (Hpoly a b)) hLB w hw0 hwL hws

#print axioms solution
