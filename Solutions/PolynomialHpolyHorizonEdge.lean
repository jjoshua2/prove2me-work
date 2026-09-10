import Solutions.PolynomialHpolyHorizonFirstHit

/-! The first-hit segment from a genuinely new horizon vertex is an actual edge
of the capped H-polyhedron. -/

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section
namespace HirschHpolyCap

variable {d n : ℕ}

/-- If `r` spans the old-active kernel at a horizon vertex, moving a positive
time `t` inward reaches an old row `j` for the first time, and the resulting
point is feasible, then the segment between the endpoints is an extreme
one-dimensional face of the cap. -/
lemma first_hit_segment_adjacent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (T : ℝ)
    (x r : EuclideanSpace ℝ (Fin d)) (t : ℝ) (j : Fin n)
    (hx : x ∈ extremePoints ℝ (cappedHpoly a b T))
    (horizon : ⟪capNormal a, x⟫ = T)
    (hr0 : r ≠ 0) (ht : 0 < t)
    (hrActive : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, r⟫ = 0)
    (hrCap : ⟪capNormal a, r⟫ < 0)
    (hjpos : 0 < ⟪a j, r⟫)
    (hyH : x + t • r ∈ Hpoly a b)
    (hjhit : ⟪a j, x + t • r⟫ = b j) :
    Adj (cappedHpoly a b T) (x + t • r) x := by
  let y := x + t • r
  have hyCapStrict : ⟪capNormal a, y⟫ < T := by
    dsimp [y]
    rw [inner_add_right, inner_smul_right, horizon]
    have hprod : t * ⟪capNormal a, r⟫ < 0 := mul_neg_of_pos_of_neg ht hrCap
    linarith
  have hy : y ∈ cappedHpoly a b T := ⟨hyH, hyCapStrict.le⟩
  have hy_ne_x : y ≠ x := by
    intro h
    have htr : t • r = 0 := by
      have hh := congrArg (fun z => z - x) h
      simpa [y] using hh
    exact hr0 ((smul_eq_zero.mp htr).resolve_left ht.ne')
  refine ⟨hy_ne_x, ?_⟩
  constructor
  · intro z hz
    obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hz
    constructor
    · intro i
      have hyi := hyH i
      have hxi := hx.1.1 i
      change ⟪a i, α • y + β • x⟫ ≤ b i
      simp only [inner_add_right, inner_smul_right]
      nlinarith
    · change ⟪capNormal a, α • y + β • x⟫ ≤ T
      simp only [inner_add_right, inner_smul_right]
      nlinarith [hyCapStrict.le]
  · intro p hp q hq w hwseg hwopen
    have hOldTightY : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = b i := by
      intro i hi
      dsimp [y]
      rw [inner_add_right, inner_smul_right, hrActive i hi, mul_zero, add_zero, hi]
    have hOldTightW : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, w⟫ = b i := by
      intro i hi
      obtain ⟨α, β, hα, hβ, hab, hw⟩ := hwseg
      rw [← hw, inner_add_right, inner_smul_right, inner_smul_right,
        hOldTightY i hi, hi]
      nlinarith
    have hOldTightP : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, p⟫ = b i := by
      intro i hi
      obtain ⟨α, β, hα, hβ, hab, hw⟩ := hwopen
      have hp_i := hp.1 i
      have hq_i := hq.1 i
      have havg : b i = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
        rw [← hOldTightW i hi, ← hw, inner_add_right, inner_smul_right, inner_smul_right]
      nlinarith
    obtain ⟨c, hpc⟩ := horizon_old_active_kernel_spanned
      a b T x hx horizon r hr0 hrActive (p - x) (by
        intro i hi
        rw [inner_sub_right, hOldTightP i hi, hi, sub_self])
    have hpform : p = x + c • r := by
      have : p - x = c • r := hpc
      module
    have hc0 : 0 ≤ c := by
      have hpcap := hp.2
      change ⟪capNormal a, p⟫ ≤ T at hpcap
      rw [hpform, inner_add_right, inner_smul_right, horizon] at hpcap
      nlinarith
    have hct : c ≤ t := by
      have hpj := hp.1 j
      have hyj : ⟪a j, y⟫ = b j := by simpa [y] using hjhit
      rw [hpform, inner_add_right, inner_smul_right] at hpj
      dsimp [y] at hyj
      rw [inner_add_right, inner_smul_right] at hyj
      nlinarith
    let γ : ℝ := c / t
    have hγ0 : 0 ≤ γ := div_nonneg hc0 ht.le
    have hγ1 : γ ≤ 1 := (div_le_one ht).2 hct
    have hγt : γ * t = c := div_mul_cancel₀ c ht.ne'
    refine ⟨γ, 1 - γ, hγ0, by linarith, by ring, ?_⟩
    dsimp [γ, y]
    rw [hpform]
    module

#print axioms first_hit_segment_adjacent

end HirschHpolyCap
