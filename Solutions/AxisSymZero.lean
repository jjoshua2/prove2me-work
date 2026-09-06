import Mathlib
import Solutions.AxisSymExtremes

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisSym

variable {d n : ℕ}

lemma proj_add
    (x y : EuclideanSpace ℝ (Fin (d + 1))) :
    Hirsch.proj (x + y) = Hirsch.proj x + Hirsch.proj y := by
  ext i
  simp [proj_apply]

lemma proj_smul
    (a : ℝ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    Hirsch.proj (a • x) = a • Hirsch.proj x := by
  ext i
  simp [proj_apply]

lemma embed_add
    (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    Hirsch.embed (x + y) (t + s) = Hirsch.embed x t + Hirsch.embed y s := by
  refine PiLp.ext fun i => ?_
  simp only [Hirsch.embed, ofLp_add, PiLp.toLp_apply, Pi.add_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j
    simp [Fin.snoc_castSucc, Pi.add_apply]

lemma embed_smul
    (a : ℝ) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Hirsch.embed (a • x) (a * t) = a • Hirsch.embed x t := by
  refine PiLp.ext fun i => ?_
  simp only [Hirsch.embed, ofLp_smul, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j
    simp [Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul]

lemma embed_affine
    (α β : ℝ) (hαβ : α + β = 1)
    (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    Hirsch.embed (α • x + β • y) (α * t + β * s) =
      α • Hirsch.embed x t + β • Hirsch.embed y s := by
  rw [embed_add, embed_smul, embed_smul]

lemma convex_Hpoly
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy α β hα hβ hαβ i
  have hi : ⟪a i, α • x + β • y⟫ =
      α * ⟪a i, x⟫ + β * ⟪a i, y⟫ := by
    simp [inner_add_right, inner_smul_right]
  rw [hi]
  have h1 := mul_le_mul_of_nonneg_left (hx i) hα
  have h2 := mul_le_mul_of_nonneg_left (hy i) hβ
  have hb : α * b i + β * b i = b i := by
    rw [← add_mul, hαβ, one_mul]
  linarith

/-- Exact description of the zero-tilt symmetric wedge. -/
lemma mem_sym_zero_iff
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n)
    (hfg : f ≠ g)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    z ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) ↔
      Hirsch.proj z ∈ Hpoly c (fun _ => (1 : ℝ)) ∧
      |z (Fin.last d)| ≤ 1 - ⟪c f, Hirsch.proj z⟫ := by
  constructor
  · intro hz
    have hfplus := hz f.castSucc
    have hfminus := hz (Fin.last n)
    have hg := hz g.castSucc
    simp [symPerturbA_castSucc, symPerturbA_last, symPerturbB,
      hfg, inner_embed_any] at hfplus hfminus hg
    have hxP : Hirsch.proj z ∈ Hpoly c (fun _ => (1 : ℝ)) := by
      intro i
      by_cases hif : i = f
      · subst i
        linarith
      · by_cases hig : i = g
        · subst i
          exact hg
        · have hi := hz i.castSucc
          simpa [symPerturbA_castSucc, symPerturbB, hif, hig,
            inner_embed_any] using hi
    refine ⟨hxP, ?_⟩
    rw [abs_le]
    constructor <;> linarith
  · rintro ⟨hxP, ht⟩
    have ht' := (abs_le.mp ht)
    intro j
    refine Fin.lastCases ?_ ?_ j
    · rw [symPerturbA_last, inner_embed_any]
      simp [symPerturbB]
      linarith [ht'.1]
    · intro i
      rw [symPerturbA_castSucc]
      by_cases hig : i = g
      · subst i
        simp [symPerturbB, inner_embed_any]
        exact hxP g
      · by_cases hif : i = f
        · subst i
          simp [hig, symPerturbB, inner_embed_any]
          linarith [ht'.2]
        · simp [hig, hif, symPerturbB, inner_embed_any]
          exact hxP i

/-- The fiber over an old feasible point in the zero-tilt wedge is the
symmetric interval cut out by the slack of the foot facet. -/
lemma vertical_mem_zero_iff
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n)
    (hfg : f ≠ g)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Hpoly c (fun _ => (1 : ℝ)))
    (t : ℝ) :
    Hirsch.embed x t ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) ↔
      |t| ≤ 1 - ⟪c f, x⟫ := by
  simpa [proj_embed, embed_last, hx] using
    (mem_sym_zero_iff c f g hfg (Hirsch.embed x t))

/-- If the wedge foot is not incident to an old vertex `v`, the zero-tilt
symmetric wedge has a genuine vertical edge over `v`.  Its midpoint is
`embed v 0`, the vertex created by the subsequent tilt. -/
lemma vertical_edge_over_extreme
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n)
    (hfg : f ≠ g)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly c (fun _ => (1 : ℝ))))
    (hfnot : ⟪c f, v⟫ ≠ 1) :
    let s : ℝ := 1 - ⟪c f, v⟫
    let p := Hirsch.embed v (-s)
    let q := Hirsch.embed v s
    0 < s ∧ Adj (Hpoly (symPerturbA c f g 0) (symPerturbB (n := n))) p q ∧
      midpoint ℝ p q = Hirsch.embed v 0 := by
  let s : ℝ := 1 - ⟪c f, v⟫
  let p := Hirsch.embed v (-s)
  let q := Hirsch.embed v s
  have hfle : ⟪c f, v⟫ ≤ 1 := hv.1 f
  have hs : 0 < s := by
    dsimp [s]
    exact sub_pos.2 (lt_of_le_of_ne hfle hfnot)
  have hp : p ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) := by
    apply (vertical_mem_zero_iff c f g hfg v hv.1 (-s)).2
    simp [abs_of_pos hs, s]
  have hq : q ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) := by
    apply (vertical_mem_zero_iff c f g hfg v hv.1 s).2
    simp [abs_of_pos hs, s]
  have hpq : p ≠ q := by
    intro h
    have hh := congrArg
      (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) h
    simp [p, q, embed_last] at hh
    linarith
  have hext : IsExtreme ℝ
      (Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)))
      (segment ℝ p q) := by
    refine ⟨(convex_Hpoly _ _).segment_subset hp hq, ?_⟩
    intro r hr w hw z hzseg hzopen
    have hrP : Hirsch.proj r ∈ Hpoly c (fun _ => (1 : ℝ)) :=
      (mem_sym_zero_iff c f g hfg r).1 hr |>.1
    have hwP : Hirsch.proj w ∈ Hpoly c (fun _ => (1 : ℝ)) :=
      (mem_sym_zero_iff c f g hfg w).1 hw |>.1
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzseg
    have hzproj : Hirsch.proj z = v := by
      have h := congrArg Hirsch.proj hzcomb
      simp [proj_add, proj_smul, p, q, proj_embed, ← add_smul, hαβ] at h
      exact h.symm
    obtain ⟨γ, δ, hγ, hδ, hγδ, hopencomb⟩ := hzopen
    have hopenP : v ∈ openSegment ℝ (Hirsch.proj r) (Hirsch.proj w) := by
      refine ⟨γ, δ, hγ, hδ, hγδ, ?_⟩
      have h := congrArg Hirsch.proj hopencomb
      rw [proj_add, proj_smul, proj_smul, hzproj] at h
      exact h
    have hrproj : Hirsch.proj r = v := hv.2 hrP hwP hopenP
    have hrzero := (mem_sym_zero_iff c f g hfg r).1 hr
    have hrheight : |r (Fin.last d)| ≤ s := by
      simpa [hrproj, s] using hrzero.2
    have hrlo : -s ≤ r (Fin.last d) := (abs_le.mp hrheight).1
    have hrhi : r (Fin.last d) ≤ s := (abs_le.mp hrheight).2
    let A : ℝ := (s - r (Fin.last d)) / (2 * s)
    let B : ℝ := (s + r (Fin.last d)) / (2 * s)
    have hden : 0 < 2 * s := by positivity
    have hA : 0 ≤ A := div_nonneg (by linarith) hden.le
    have hB : 0 ≤ B := div_nonneg (by linarith) hden.le
    have hAB : A + B = 1 := by
      dsimp [A, B]
      field_simp [hs.ne']
      ring
    have htAB : A * (-s) + B * s = r (Fin.last d) := by
      dsimp [A, B]
      field_simp [hs.ne']
      ring
    refine ⟨A, B, hA, hB, hAB, ?_⟩
    calc
      A • p + B • q =
          Hirsch.embed (A • v + B • v) (A * (-s) + B * s) := by
            symm
            exact embed_affine A B hAB v v (-s) s
      _ = Hirsch.embed v (r (Fin.last d)) := by
            rw [htAB, ← add_smul, hAB, one_smul]
      _ = r := by
            rw [← hrproj]
            exact embed_proj r
  have hmid : midpoint ℝ p q = Hirsch.embed v 0 := by
    rw [midpoint_eq_smul_add]
    have hhalf : (1 / 2 : ℝ) + 1 / 2 = 1 := by ring
    rw [← embed_affine (1 / 2) (1 / 2) hhalf]
    simp
  exact ⟨hs, ⟨hpq, hext⟩, hmid⟩

end HirschAxisSym
