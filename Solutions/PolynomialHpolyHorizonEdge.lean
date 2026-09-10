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
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      have hy' : α * ⟪a i, y⟫ ≤ α * b i := mul_le_mul_of_nonneg_left hyi hα
      have hx' : β * ⟪a i, x⟫ ≤ β * b i := mul_le_mul_of_nonneg_left hxi hβ
      calc
        α * ⟪a i, y⟫ + β * ⟪a i, x⟫ ≤ α * b i + β * b i := add_le_add hy' hx'
        _ = (α + β) * b i := by ring
        _ = b i := by rw [hab, one_mul]
    · change ⟪capNormal a, α • y + β • x⟫ ≤ T
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      have hy' : α * ⟪capNormal a, y⟫ ≤ α * T :=
        mul_le_mul_of_nonneg_left hyCapStrict.le hα
      have hx' : β * ⟪capNormal a, x⟫ ≤ β * T :=
        mul_le_mul_of_nonneg_left hx.1.2 hβ
      calc
        α * ⟪capNormal a, y⟫ + β * ⟪capNormal a, x⟫ ≤ α * T + β * T :=
          add_le_add hy' hx'
        _ = (α + β) * T := by ring
        _ = T := by rw [hab, one_mul]
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
      calc
        α * b i + β * b i = (α + β) * b i := by ring
        _ = b i := by rw [hab, one_mul]
    have hOldTightP : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, p⟫ = b i := by
      intro i hi
      obtain ⟨α, β, hα, hβ, hab, hw⟩ := hwopen
      have hp_i := hp.1 i
      have hq_i := hq.1 i
      have havg : b i = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
        rw [← hOldTightW i hi, ← hw, inner_add_right, inner_smul_right, inner_smul_right]
      apply le_antisymm hp_i
      by_contra hnot
      have hp_lt : ⟪a i, p⟫ < b i := lt_of_not_ge hnot
      have hp_mul : α * ⟪a i, p⟫ < α * b i := mul_lt_mul_of_pos_left hp_lt hα
      have hq_mul : β * ⟪a i, q⟫ ≤ β * b i :=
        mul_le_mul_of_nonneg_left hq_i hβ.le
      have hsum : α * ⟪a i, p⟫ + β * ⟪a i, q⟫ < α * b i + β * b i :=
        add_lt_add_of_lt_of_le hp_mul hq_mul
      have hright : α * b i + β * b i = b i := by
        calc
          α * b i + β * b i = (α + β) * b i := by ring
          _ = b i := by rw [hab, one_mul]
      have hcontra : b i < b i := by
        calc
          b i = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := havg
          _ < α * b i + β * b i := hsum
          _ = b i := hright
      exact (lt_irrefl (b i)) hcontra
    obtain ⟨c, hpc⟩ := horizon_old_active_kernel_spanned
      a b T x hx horizon r hr0 hrActive (p - x) (by
        intro i hi
        rw [inner_sub_right, hOldTightP i hi, hi, sub_self])
    have hpform : p = x + c • r := by
      have hpform' : p = c • r + x := sub_eq_iff_eq_add.mp hpc
      simpa [add_comm] using hpform'
    have hc0 : 0 ≤ c := by
      have hpcap := hp.2
      change ⟪capNormal a, p⟫ ≤ T at hpcap
      rw [hpform, inner_add_right, inner_smul_right, horizon] at hpcap
      have hmul : c * ⟪capNormal a, r⟫ ≤ 0 := by linarith
      by_contra hc
      have hcneg : c < 0 := lt_of_not_ge hc
      have hpos : 0 < c * ⟪capNormal a, r⟫ := mul_pos_of_neg_of_neg hcneg hrCap
      exact (not_lt_of_ge hmul) hpos
    have hct : c ≤ t := by
      have hpj := hp.1 j
      have hyj : ⟪a j, y⟫ = b j := by simpa [y] using hjhit
      rw [hpform, inner_add_right, inner_smul_right] at hpj
      dsimp [y] at hyj
      rw [inner_add_right, inner_smul_right] at hyj
      have hmul : c * ⟪a j, r⟫ ≤ t * ⟪a j, r⟫ := by linarith
      exact le_of_mul_le_mul_right hmul hjpos
    let γ : ℝ := c / t
    have hγ0 : 0 ≤ γ := div_nonneg hc0 ht.le
    have hγ1 : γ ≤ 1 := (div_le_one ht).2 hct
    have hγt : γ * t = c := div_mul_cancel₀ c ht.ne'
    refine ⟨γ, 1 - γ, hγ0, by linarith, by ring, ?_⟩
    calc
      γ • y + (1 - γ) • x = x + (γ * t) • r := by
        dsimp [y]
        module
      _ = x + c • r := by rw [hγt]
      _ = p := hpform.symm

#print axioms first_hit_segment_adjacent

end HirschHpolyCap
