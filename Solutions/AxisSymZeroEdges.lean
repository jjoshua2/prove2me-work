import Mathlib
import Solutions.AxisSymZero

open scoped RealInnerProductSpace
open Set WithLp EuclideanSpace Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschAxisSym

variable {d n : ℕ}

noncomputable def slack
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 - ⟪c f, x⟫

noncomputable def topLift
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (d + 1)) :=
  Hirsch.embed x (slack c f x)

noncomputable def botLift
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (d + 1)) :=
  Hirsch.embed x (-slack c f x)

lemma slack_affine
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f : Fin n)
    (α β : ℝ) (hαβ : α + β = 1)
    (x y : EuclideanSpace ℝ (Fin d)) :
    slack c f (α • x + β • y) = α * slack c f x + β * slack c f y := by
  simp [slack, inner_add_right, inner_smul_right]
  linarith

lemma topLift_affine
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f : Fin n)
    (α β : ℝ) (hαβ : α + β = 1)
    (x y : EuclideanSpace ℝ (Fin d)) :
    topLift c f (α • x + β • y) =
      α • topLift c f x + β • topLift c f y := by
  rw [topLift, topLift, topLift]
  rw [slack_affine c f α β hαβ]
  exact embed_affine α β hαβ x y (slack c f x) (slack c f y)

lemma botLift_affine
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f : Fin n)
    (α β : ℝ) (hαβ : α + β = 1)
    (x y : EuclideanSpace ℝ (Fin d)) :
    botLift c f (α • x + β • y) =
      α • botLift c f x + β • botLift c f y := by
  rw [botLift, botLift, botLift]
  have hs := slack_affine c f α β hαβ x y
  rw [hs]
  have hneg : -(α * slack c f x + β * slack c f y) =
      α * (-slack c f x) + β * (-slack c f y) := by ring
  rw [hneg]
  exact embed_affine α β hαβ x y (-slack c f x) (-slack c f y)

lemma topLift_mem
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (hfg : f ≠ g)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly c (fun _ => (1 : ℝ))) :
    topLift c f x ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) := by
  have hs : 0 ≤ slack c f x := by
    dsimp [slack]
    linarith [hx f]
  apply (vertical_mem_zero_iff c f g hfg x hx (slack c f x)).2
  simpa [abs_of_nonneg hs]

lemma botLift_mem
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (hfg : f ≠ g)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly c (fun _ => (1 : ℝ))) :
    botLift c f x ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) := by
  have hs : 0 ≤ slack c f x := by
    dsimp [slack]
    linarith [hx f]
  apply (vertical_mem_zero_iff c f g hfg x hx (-slack c f x)).2
  simp [abs_of_nonneg hs]

lemma proj_topLift
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) :
    Hirsch.proj (topLift c f x) = x := by
  simp [topLift, proj_embed]

lemma proj_botLift
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f : Fin n)
    (x : EuclideanSpace ℝ (Fin d)) :
    Hirsch.proj (botLift c f x) = x := by
  simp [botLift, proj_embed]

lemma midpoint_proj
    (p q : EuclideanSpace ℝ (Fin (d + 1))) :
    Hirsch.proj (midpoint ℝ p q) = midpoint ℝ (Hirsch.proj p) (Hirsch.proj q) := by
  simp [midpoint_eq_smul_add, proj_add, proj_smul]

lemma midpoint_last
    (p q : EuclideanSpace ℝ (Fin (d + 1))) :
    (midpoint ℝ p q) (Fin.last d) =
      (p (Fin.last d) + q (Fin.last d)) / 2 := by
  simp [midpoint_eq_smul_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Every nonvertical edge of the zero-tilt symmetric wedge lies entirely on
one of its two graph boundaries `t = ± slack(x)`. -/
lemma zero_edge_boundary
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (hfg : f ≠ g)
    {p q : EuclideanSpace ℝ (Fin (d + 1))}
    (hadj : Adj (Hpoly (symPerturbA c f g 0) (symPerturbB (n := n))) p q)
    (hproj : Hirsch.proj p ≠ Hirsch.proj q) :
    (∀ z ∈ segment ℝ p q, z (Fin.last d) = slack c f (Hirsch.proj z)) ∨
    (∀ z ∈ segment ℝ p q, z (Fin.last d) = -slack c f (Hirsch.proj z)) := by
  obtain ⟨hpq, hextr⟩ := hadj
  have hpW := hextr.subset (left_mem_segment ℝ p q)
  have hqW := hextr.subset (right_mem_segment ℝ p q)
  have hp0 := (mem_sym_zero_iff c f g hfg p).1 hpW
  have hq0 := (mem_sym_zero_iff c f g hfg q).1 hqW
  let m := midpoint ℝ p q
  have hmseg : m ∈ segment ℝ p q := midpoint_mem_segment ℝ p q
  have hmW : m ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) :=
    hextr.subset hmseg
  have hm0 := (mem_sym_zero_iff c f g hfg m).1 hmW
  let sm : ℝ := slack c f (Hirsch.proj m)
  let tm : ℝ := m (Fin.last d)
  have hmbound : |tm| ≤ sm := by simpa [sm, tm, slack] using hm0.2
  have hmbdry : tm = sm ∨ tm = -sm := by
    by_contra hbdry
    have hhi_ne : tm ≠ sm := fun h => hbdry (Or.inl h)
    have hlo_ne : tm ≠ -sm := fun h => hbdry (Or.inr h)
    have hlo : -sm ≤ tm := (abs_le.mp hmbound).1
    have hhi : tm ≤ sm := (abs_le.mp hmbound).2
    have hlo' : -sm < tm := lt_of_le_of_ne hlo (Ne.symm hlo_ne)
    have hhi' : tm < sm := lt_of_le_of_ne hhi hhi_ne
    let η : ℝ := min (tm + sm) (sm - tm) / 2
    have hη : 0 < η := by
      have h1 : 0 < tm + sm := by linarith
      have h2 : 0 < sm - tm := by linarith
      have : 0 < min (tm + sm) (sm - tm) := lt_min h1 h2
      positivity
    have hηlo : -sm ≤ tm - η := by
      have hmin : min (tm + sm) (sm - tm) ≤ tm + sm := min_le_left _ _
      dsimp [η]
      linarith
    have hηhi : tm + η ≤ sm := by
      have hmin : min (tm + sm) (sm - tm) ≤ sm - tm := min_le_right _ _
      dsimp [η]
      linarith
    let mdn := Hirsch.embed (Hirsch.proj m) (tm - η)
    let mup := Hirsch.embed (Hirsch.proj m) (tm + η)
    have hdn : mdn ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) := by
      apply (mem_sym_zero_iff c f g hfg mdn).2
      refine ⟨?_, ?_⟩
      · simpa [mdn, proj_embed] using hm0.1
      · simp [mdn, proj_embed, embed_last, slack]
        rw [abs_le]
        constructor <;> linarith
    have hup : mup ∈ Hpoly (symPerturbA c f g 0) (symPerturbB (n := n)) := by
      apply (mem_sym_zero_iff c f g hfg mup).2
      refine ⟨?_, ?_⟩
      · simpa [mup, proj_embed] using hm0.1
      · simp [mup, proj_embed, embed_last, slack]
        rw [abs_le]
        constructor <;> linarith
    have hm_id : m = Hirsch.embed (Hirsch.proj m) tm := by
      simpa [tm] using (embed_proj m).symm
    have hop : m ∈ openSegment ℝ mdn mup := by
      refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by positivity, by positivity, by ring, ?_⟩
      calc
        (1 / 2 : ℝ) • mdn + (1 / 2 : ℝ) • mup =
            Hirsch.embed ((1 / 2 : ℝ) • Hirsch.proj m +
              (1 / 2 : ℝ) • Hirsch.proj m)
              ((1 / 2 : ℝ) * (tm - η) + (1 / 2 : ℝ) * (tm + η)) := by
                symm
                exact embed_affine (1 / 2) (1 / 2) (by ring)
                  (Hirsch.proj m) (Hirsch.proj m) (tm - η) (tm + η)
        _ = Hirsch.embed (Hirsch.proj m) tm := by
              congr 1
              · rw [← add_smul]
                norm_num
              · ring
        _ = m := hm_id.symm
    have hupseg : mup ∈ segment ℝ p q :=
      hextr.right_mem_of_mem_openSegment hdn hup hmseg hop
    obtain ⟨α, β, hα, hβ, hαβ, hmup⟩ := hupseg
    have hβeq : β = 1 - α := by linarith
    have hproj_eq : α • Hirsch.proj p + β • Hirsch.proj q =
        (1 / 2 : ℝ) • Hirsch.proj p + (1 / 2 : ℝ) • Hirsch.proj q := by
      have h1 : Hirsch.proj mup = α • Hirsch.proj p + β • Hirsch.proj q := by
        have h := congrArg Hirsch.proj hmup.symm
        simpa [mup, proj_embed, proj_add, proj_smul] using h
      have h2 : Hirsch.proj m =
          (1 / 2 : ℝ) • Hirsch.proj p + (1 / 2 : ℝ) • Hirsch.proj q := by
        simpa [midpoint_eq_smul_add, proj_add, proj_smul] using midpoint_proj p q
      have heq : Hirsch.proj mup = Hirsch.proj m := by simp [mup, proj_embed]
      rw [← h1, heq, h2]
    have huniq : α = (1 / 2 : ℝ) := by
      rw [hβeq] at hproj_eq
      obtain ⟨i, hi⟩ : ∃ i, Hirsch.proj p i ≠ Hirsch.proj q i := by
        by_contra h
        push Not at h
        exact hproj (PiLp.ext h)
      have hi_eq : α * Hirsch.proj p i + (1 - α) * Hirsch.proj q i =
          (1 / 2 : ℝ) * Hirsch.proj p i + (1 / 2 : ℝ) * Hirsch.proj q i := by
        have h := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) hproj_eq
        simpa [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using h
      have hprod : (α - 1 / 2) * (Hirsch.proj p i - Hirsch.proj q i) = 0 := by
        linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.2 hi))
    have hβhalf : β = (1 / 2 : ℝ) := by linarith
    have hmexpr : m = (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q := by
      simp [m, midpoint_eq_smul_add]
    have hmup_eq : mup = m := by
      rw [huniq, hβhalf, ← hmexpr] at hmup
      exact hmup.symm
    have hlast := congrArg
      (fun z : EuclideanSpace ℝ (Fin (d + 1)) => z (Fin.last d)) hmup_eq
    simp [mup, embed_last] at hlast
    linarith
  have hpAbs := hp0.2
  have hqAbs := hq0.2
  have hpLo : -slack c f (Hirsch.proj p) ≤ p (Fin.last d) :=
    (abs_le.mp (by simpa [slack] using hpAbs)).1
  have hpHi : p (Fin.last d) ≤ slack c f (Hirsch.proj p) :=
    (abs_le.mp (by simpa [slack] using hpAbs)).2
  have hqLo : -slack c f (Hirsch.proj q) ≤ q (Fin.last d) :=
    (abs_le.mp (by simpa [slack] using hqAbs)).1
  have hqHi : q (Fin.last d) ≤ slack c f (Hirsch.proj q) :=
    (abs_le.mp (by simpa [slack] using hqAbs)).2
  have hmLast : tm = (p (Fin.last d) + q (Fin.last d)) / 2 := by
    simpa [tm, m] using midpoint_last p q
  have hmSlack : sm =
      (slack c f (Hirsch.proj p) + slack c f (Hirsch.proj q)) / 2 := by
    have hpj := midpoint_proj p q
    dsimp [sm, m]
    rw [hpj]
    have hs := slack_affine c f (1 / 2) (1 / 2) (by ring)
      (Hirsch.proj p) (Hirsch.proj q)
    simpa [midpoint_eq_smul_add] using hs
  rcases hmbdry with htop | hbot
  · have hpTop : p (Fin.last d) = slack c f (Hirsch.proj p) := by
      have hsum :
          (slack c f (Hirsch.proj p) - p (Fin.last d)) +
          (slack c f (Hirsch.proj q) - q (Fin.last d)) = 0 := by
        linarith [htop, hmLast, hmSlack]
      nlinarith
    have hqTop : q (Fin.last d) = slack c f (Hirsch.proj q) := by
      have hsum :
          (slack c f (Hirsch.proj p) - p (Fin.last d)) +
          (slack c f (Hirsch.proj q) - q (Fin.last d)) = 0 := by
        linarith [htop, hmLast, hmSlack]
      nlinarith
    exact Or.inl (by
      intro z hz
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
      have hs := slack_affine c f α β hαβ (Hirsch.proj p) (Hirsch.proj q)
      rw [proj_add, proj_smul, proj_smul] at hs
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      linarith)
  · have hpBot : p (Fin.last d) = -slack c f (Hirsch.proj p) := by
      have hsum :
          (slack c f (Hirsch.proj p) + p (Fin.last d)) +
          (slack c f (Hirsch.proj q) + q (Fin.last d)) = 0 := by
        linarith [hbot, hmLast, hmSlack]
      nlinarith
    have hqBot : q (Fin.last d) = -slack c f (Hirsch.proj q) := by
      have hsum :
          (slack c f (Hirsch.proj p) + p (Fin.last d)) +
          (slack c f (Hirsch.proj q) + q (Fin.last d)) = 0 := by
        linarith [hbot, hmLast, hmSlack]
      nlinarith
    exact Or.inr (by
      intro z hz
      obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hz
      have hs := slack_affine c f α β hαβ (Hirsch.proj p) (Hirsch.proj q)
      rw [proj_add, proj_smul, proj_smul] at hs
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      linarith)

/-- Under the zero-tilt symmetric wedge projection, an edge becomes either a
stationary step or an edge of the old polytope. -/
lemma zero_proj_adj
    (c : Fin n → EuclideanSpace ℝ (Fin d)) (f g : Fin n) (hfg : f ≠ g)
    {p q : EuclideanSpace ℝ (Fin (d + 1))}
    (hadj : Adj (Hpoly (symPerturbA c f g 0) (symPerturbB (n := n))) p q) :
    Hirsch.proj p = Hirsch.proj q ∨
      Adj (Hpoly c (fun _ => (1 : ℝ))) (Hirsch.proj p) (Hirsch.proj q) := by
  by_cases hproj : Hirsch.proj p = Hirsch.proj q
  · exact Or.inl hproj
  refine Or.inr ⟨hproj, ?_⟩
  obtain ⟨hpq, hextr⟩ := hadj
  have hpW := hextr.subset (left_mem_segment ℝ p q)
  have hqW := hextr.subset (right_mem_segment ℝ p q)
  have hpP := (mem_sym_zero_iff c f g hfg p).1 hpW |>.1
  have hqP := (mem_sym_zero_iff c f g hfg q).1 hqW |>.1
  have hsegP : segment ℝ (Hirsch.proj p) (Hirsch.proj q) ⊆
      Hpoly c (fun _ => (1 : ℝ)) :=
    (convex_Hpoly c (fun _ => (1 : ℝ))).segment_subset hpP hqP
  refine ⟨hsegP, ?_⟩
  intro r hr s hs z hz hzopen
  rcases zero_edge_boundary c f g hfg hadj hproj with htop | hbot
  · have hpTop := htop p (left_mem_segment ℝ p q)
    have hqTop := htop q (right_mem_segment ℝ p q)
    have hp_id : p = topLift c f (Hirsch.proj p) := by
      rw [topLift]
      simpa [hpTop] using (embed_proj p).symm
    have hq_id : q = topLift c f (Hirsch.proj q) := by
      rw [topLift]
      simpa [hqTop] using (embed_proj q).symm
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hz
    have hzW : topLift c f z ∈ segment ℝ p q := by
      refine ⟨α, β, hα, hβ, hαβ, ?_⟩
      rw [hp_id, hq_id, ← topLift_affine c f α β hαβ]
      rw [hzcomb]
    obtain ⟨γ, δ, hγ, hδ, hγδ, hopencomb⟩ := hzopen
    have hrW := topLift_mem c f g hfg hr
    have hsW := topLift_mem c f g hfg hs
    have hopenW : topLift c f z ∈ openSegment ℝ (topLift c f r) (topLift c f s) := by
      refine ⟨γ, δ, hγ, hδ, hγδ, ?_⟩
      rw [← topLift_affine c f γ δ hγδ]
      rw [hopencomb]
    have hrseg : topLift c f r ∈ segment ℝ p q :=
      hextr.left_mem_of_mem_openSegment hrW hsW hzW hopenW
    obtain ⟨α', β', hα', hβ', hαβ', hrcomb⟩ := hrseg
    refine ⟨α', β', hα', hβ', hαβ', ?_⟩
    have h := congrArg Hirsch.proj hrcomb
    simpa [proj_topLift, proj_add, proj_smul] using h
  · have hpBot := hbot p (left_mem_segment ℝ p q)
    have hqBot := hbot q (right_mem_segment ℝ p q)
    have hp_id : p = botLift c f (Hirsch.proj p) := by
      rw [botLift]
      simpa [hpBot] using (embed_proj p).symm
    have hq_id : q = botLift c f (Hirsch.proj q) := by
      rw [botLift]
      simpa [hqBot] using (embed_proj q).symm
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hz
    have hzW : botLift c f z ∈ segment ℝ p q := by
      refine ⟨α, β, hα, hβ, hαβ, ?_⟩
      rw [hp_id, hq_id, ← botLift_affine c f α β hαβ]
      rw [hzcomb]
    obtain ⟨γ, δ, hγ, hδ, hγδ, hopencomb⟩ := hzopen
    have hrW := botLift_mem c f g hfg hr
    have hsW := botLift_mem c f g hfg hs
    have hopenW : botLift c f z ∈ openSegment ℝ (botLift c f r) (botLift c f s) := by
      refine ⟨γ, δ, hγ, hδ, hγδ, ?_⟩
      rw [← botLift_affine c f γ δ hγδ]
      rw [hopencomb]
    have hrseg : botLift c f r ∈ segment ℝ p q :=
      hextr.left_mem_of_mem_openSegment hrW hsW hzW hopenW
    obtain ⟨α', β', hα', hβ', hαβ', hrcomb⟩ := hrseg
    refine ⟨α', β', hα', hβ', hαβ', ?_⟩
    have h := congrArg Hirsch.proj hrcomb
    simpa [proj_botLift, proj_add, proj_smul] using h

end HirschAxisSym
