import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_wedge

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

noncomputable section

namespace HirschAxisSym

variable {d n : ℕ}

lemma embed_castSucc (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) (i : Fin d) :
    Hirsch.embed x t i.castSucc = x i := by
  simp [Hirsch.embed, Fin.snoc_castSucc]

lemma embed_last (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Hirsch.embed x t (Fin.last d) = t := by
  simp [Hirsch.embed, Fin.snoc_last]

lemma proj_apply (z : EuclideanSpace ℝ (Fin (d + 1))) (i : Fin d) :
    Hirsch.proj z i = z i.castSucc := by
  rw [Hirsch.proj, PiLp.toLp_apply]
  rfl

lemma proj_embed (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    Hirsch.proj (Hirsch.embed x t) = x := by
  ext i
  rw [proj_apply, embed_castSucc]

lemma embed_proj (z : EuclideanSpace ℝ (Fin (d + 1))) :
    Hirsch.embed (Hirsch.proj z) (z (Fin.last d)) = z := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [embed_last]
  · intro j
    simp [embed_castSucc, proj_apply]

lemma inner_embed (x y : EuclideanSpace ℝ (Fin d)) (t s : ℝ) :
    ⟪Hirsch.embed x t, Hirsch.embed y s⟫ = ⟪x, y⟫ + t * s := by
  simp [Hirsch.embed, inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- Standard symmetric Klee--Walkup wedge over `f`, with the old row `g`
tilted by `ε` in the new coordinate.  This is the direct primal coordinate
form of the wedge-plus-perturbation in Santos' strong d-step construction. -/
noncomputable def symPerturbA
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)) :=
  Fin.snoc
    (fun i =>
      if i = g then Hirsch.embed (c i) ε
      else if i = f then Hirsch.embed (c i) 1
      else Hirsch.embed (c i) 0)
    (Hirsch.embed (c f) (-1))

noncomputable def symPerturbB : Fin (n + 1) → ℝ := fun _ => 1

lemma symPerturbA_castSucc
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ) (i : Fin n) :
    symPerturbA c f g ε i.castSucc =
      if i = g then Hirsch.embed (c i) ε
      else if i = f then Hirsch.embed (c i) 1
      else Hirsch.embed (c i) 0 := by
  simp [symPerturbA, Fin.snoc_castSucc]

lemma symPerturbA_last
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ) :
    symPerturbA c f g ε (Fin.last n) = Hirsch.embed (c f) (-1) := by
  simp [symPerturbA, Fin.snoc_last]

lemma sym_inner_castSucc_zero
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    ⟪symPerturbA c f g ε i.castSucc, Hirsch.embed x 0⟫ = ⟪c i, x⟫ := by
  rw [symPerturbA_castSucc]
  by_cases hig : i = g
  · simp [hig, inner_embed]
  · by_cases hif : i = f
    · simp [hig, hif, inner_embed]
    · simp [hig, hif, inner_embed]

lemma sym_inner_last_zero
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ⟪symPerturbA c f g ε (Fin.last n), Hirsch.embed x 0⟫ = ⟪c f, x⟫ := by
  rw [symPerturbA_last, inner_embed]
  ring

/-- The symmetric perturbed wedge preserves the spindle incidence pattern at
`(u,0)` and `(v,0)`.  The duplicated foot row is tight only at `u`, while the
tilted `g` row is tight only at `v`. -/
lemma sym_spindle_incidence
    (c : Fin n → EuclideanSpace ℝ (Fin d))
    (u v : EuclideanSpace ℝ (Fin d)) (f g : Fin n) (ε : ℝ)
    (hUle : ∀ i, ⟪c i, u⟫ ≤ 1)
    (hVle : ∀ i, ⟪c i, v⟫ ≤ 1)
    (hxor : ∀ i, (⟪c i, u⟫ = 1) ↔ ⟪c i, v⟫ ≠ 1) :
    let U := Hirsch.embed u 0
    let V := Hirsch.embed v 0
    U ∈ Hpoly (symPerturbA c f g ε) (symPerturbB (n := n)) ∧
    V ∈ Hpoly (symPerturbA c f g ε) (symPerturbB (n := n)) ∧
    ∀ j,
      (⟪symPerturbA c f g ε j, U⟫ = symPerturbB (n := n) j) ↔
      ⟪symPerturbA c f g ε j, V⟫ ≠ symPerturbB (n := n) j := by
  dsimp
  constructor
  · intro j
    refine Fin.lastCases ?_ ?_ j
    · simpa [symPerturbB, sym_inner_last_zero] using hUle f
    · intro i
      simpa [symPerturbB, sym_inner_castSucc_zero] using hUle i
  · constructor
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [symPerturbB, sym_inner_last_zero] using hVle f
      · intro i
        simpa [symPerturbB, sym_inner_castSucc_zero] using hVle i
    · intro j
      refine Fin.lastCases ?_ ?_ j
      · simpa [symPerturbB, sym_inner_last_zero] using hxor f
      · intro i
        simpa [symPerturbB, sym_inner_castSucc_zero] using hxor i

/-- A convenient converse to the usual active-normal criterion: if the only
direction orthogonal to all normals tight at a feasible point is zero, then the
point is extreme. -/
lemma extreme_of_active_orthogonal
    {m k : ℕ}
    {A : Fin m → EuclideanSpace ℝ (Fin k)} {B : Fin m → ℝ}
    {x : EuclideanSpace ℝ (Fin k)}
    (hx : x ∈ Hpoly A B)
    (hzero : ∀ y : EuclideanSpace ℝ (Fin k),
      (∀ i, ⟪A i, x⟫ = B i → ⟪A i, y⟫ = 0) → y = 0) :
    x ∈ extremePoints ℝ (Hpoly A B) := by
  refine ⟨hx, ?_⟩
  intro p hp q hq hop
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hop
  have horth : ∀ i, ⟪A i, x⟫ = B i → ⟪A i, p - x⟫ = 0 := by
    intro i hix
    have hp_le := hp i
    have hq_le := hq i
    have havg : α * ⟪A i, p⟫ + β * ⟪A i, q⟫ = B i := by
      have h := congrArg (fun z : EuclideanSpace ℝ (Fin k) => ⟪A i, z⟫) hcomb
      simpa [inner_add_right, inner_smul_right, hix] using h
    have hp_eq : ⟪A i, p⟫ = B i := by
      nlinarith
    simp [inner_sub_right, hp_eq, hix]
  exact sub_eq_zero.mp (hzero (p - x) horth)

end HirschAxisSym
