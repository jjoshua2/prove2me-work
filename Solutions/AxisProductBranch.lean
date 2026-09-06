import Mathlib
import Solutions.AxisProductEdges
import Solutions.AxisWalkCompression

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisProduct

variable {d n : ℕ}

/-- If the given H-description has a redundant row, Santos' one-step conclusion
is easier than the perturbation case: replace that row by the upper face of an
interval and append the lower face.  The result is literally `P × [0,1]` in
coordinates, and one vertical step is forced in every apex-to-apex walk. -/
theorem redundant_row_step
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) (r : Fin n)
    (hred : RowRedundant a b r)
    (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
        ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)))
      (b' : Fin (n + 1) → ℝ)
      (u' v' : EuclideanSpace ℝ (Fin (d + 1))),
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      u' ∈ extremePoints ℝ (Hpoly a' b') ∧
      v' ∈ extremePoints ℝ (Hpoly a' b') ∧
      (∀ i, (⟪a' i, u'⟫ = b' i) ↔ ⟪a' i, v'⟫ ≠ b' i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin (d + 1)),
        ¬ (w 0 = u' ∧ w (d + 1) = v' ∧
          ∀ j < d + 1, w j = w (j + 1) ∨
            Adj (Hpoly a' b') (w j) (w (j + 1))) := by
  let A := productA a r
  let B := productB b r
  let U := Hirsch.embed u 0
  let V := Hirsch.embed v 1
  refine ⟨A, B, U, V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact product_nonempty a b r hred hne
  · exact product_bounded a b r hred hbd
  · exact product_endpoint_extreme a b r hred hu (Or.inl rfl)
  · exact product_endpoint_extreme a b r hred hv (Or.inr rfl)
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · simp [A, B, U, V, productA_last, productB_last, inner_embed]
    · intro i
      by_cases hir : i = r
      · subst i
        simp [A, B, U, V, productA_castSucc, productB_castSucc, inner_embed]
      · simpa [A, B, U, V, productA_castSucc, productB_castSucc, hir, inner_embed]
          using hspindle i
  · intro w hwbad
    rcases hwbad with ⟨hw0, hwN, hwstep⟩
    let pw : ℕ → EuclideanSpace ℝ (Fin d) := fun k => Hirsch.proj (w k)
    have hpstep : ∀ k < d + 1,
        pw k = pw (k + 1) ∨ Adj (Hpoly a b) (pw k) (pw (k + 1)) := by
      intro k hk
      rcases hwstep k hk with heq | hadj
      · exact Or.inl (congrArg Hirsch.proj heq)
      · simpa [A, B, pw] using product_proj_adj a b r hred hadj
    have hheight :
        (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) (w 0) ≠
        (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) (w (d + 1)) := by
      rw [hw0, hwN]
      simp [U, V, embed_last]
    obtain ⟨j, hj, hjchange⟩ :=
      HirschAxisWalk.exists_changed_step
        (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) w (d + 1) hheight
    have hjadj : Adj (Hpoly A B) (w j) (w (j + 1)) := by
      rcases hwstep j hj with heq | hadj
      · exact False.elim (hjchange (congrArg
          (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) heq))
      · exact hadj
    have hjstat : pw j = pw (j + 1) := by
      rcases product_adj_proj_or_height_eq a b r hred hjadj with hproj | ht
      · simpa [pw] using hproj
      · exact False.elim (hjchange ht)
    obtain ⟨w', hw'0, hw'd, hw'step⟩ :=
      HirschAxisWalk.compress_stationary_step (Adj (Hpoly a b)) pw d j hj hjstat hpstep
    apply hlong w'
    refine ⟨?_, ?_, hw'step⟩
    · calc
        w' 0 = pw 0 := hw'0
        _ = Hirsch.proj U := by rw [hw0]
        _ = u := proj_embed u 0
    · calc
        w' d = pw (d + 1) := hw'd
        _ = Hirsch.proj V := by rw [hwN]
        _ = v := proj_embed v 1

end HirschAxisProduct
