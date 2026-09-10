import Mathlib
import Definitions.Def_Hirsch_model
import Solutions.PolynomialClipWalk

open Set Hirsch HirschClip

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCubeCut

variable {d : ℕ}

def cost (a x : Fin d → ℝ) : ℝ := ∑ i, a i * x i

def Box (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

def Clip (a : Fin d → ℝ) (β : ℝ) : Set (Fin d → ℝ) :=
  Box d ∩ {x | cost a x ≤ β}

def Corner (x : Fin d → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1

lemma cost_add (a x y : Fin d → ℝ) :
    cost a (x + y) = cost a x + cost a y := by
  simp [cost, mul_add, Finset.sum_add_distrib]

lemma cost_sub (a x y : Fin d → ℝ) :
    cost a (x - y) = cost a x - cost a y := by
  simp [cost, mul_sub, Finset.sum_sub_distrib]

lemma cost_smul (a x : Fin d → ℝ) (t : ℝ) :
    cost a (t • x) = t * cost a x := by
  simp [cost, Finset.mul_sum, mul_left_comm]

lemma cost_combo (a x y : Fin d → ℝ) (s t : ℝ) :
    cost a (s • x + t • y) = s * cost a x + t * cost a y := by
  rw [cost_add, cost_smul, cost_smul]

lemma cost_single (a : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    cost a (Pi.single i t) = a i * t := by
  classical
  simp [cost, Pi.single_apply, mul_ite]

lemma update_eq_add_single (x : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    Function.update x i t = x + (t - x i) • Pi.single i (1 : ℝ) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h, Pi.single_eq_of_ne h]

lemma cost_update (a x : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    cost a (Function.update x i t) = cost a x + a i * (t - x i) := by
  rw [update_eq_add_single, cost_add, cost_smul, cost_single]
  ring

lemma clip_convex (a : Fin d → ℝ) (β : ℝ) : Convex ℝ (Clip a β) := by
  intro x hx y hy s t hs ht hst
  refine ⟨?_, ?_⟩
  · intro i
    change 0 ≤ s * x i + t * y i ∧ s * x i + t * y i ≤ 1
    have hxi := hx.1 i
    have hyi := hy.1 i
    constructor
    · exact add_nonneg (mul_nonneg hs hxi.1) (mul_nonneg ht hyi.1)
    · calc
        s * x i + t * y i ≤ s * 1 + t * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left hxi.2 hs)
            (mul_le_mul_of_nonneg_left hyi.2 ht)
        _ = 1 := by simpa using hst
  · change cost a (s • x + t • y) ≤ β
    rw [cost_combo]
    calc
      s * cost a x + t * cost a y ≤ s * β + t * β :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 hs)
          (mul_le_mul_of_nonneg_left hy.2 ht)
      _ = β := by rw [← add_mul, hst, one_mul]

lemma fixed_bound_left
    {p q z : Fin d → ℝ} (hp : p ∈ Box d) (hq : q ∈ Box d)
    (hop : z ∈ openSegment ℝ p q) (i : Fin d)
    (hz : z i = 0 ∨ z i = 1) : p i = z i := by
  obtain ⟨s, t, hs, ht, hst, heq⟩ := hop
  have hi := congrFun heq i
  change s * p i + t * q i = z i at hi
  have hpi := hp i
  have hqi := hq i
  rcases hz with hz | hz
  · rw [hz] at hi ⊢
    nlinarith [mul_nonneg hs.le hpi.1, mul_nonneg ht.le hqi.1]
  · rw [hz] at hi ⊢
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hpi.2),
      mul_nonneg ht.le (sub_nonneg.mpr hqi.2)]

/-- A segment between feasible cube corners differing in one coordinate is
an actual edge of the cut cube, not merely a feasible segment. -/
lemma corner_flip_adj (a : Fin d → ℝ) (β : ℝ)
    {x y : Fin d → ℝ} (hx : x ∈ Clip a β) (hy : y ∈ Clip a β)
    (hxc : Corner x) (hyc : Corner y)
    (i : Fin d) (hdiff : x i ≠ y i)
    (hsame : ∀ j, j ≠ i → x j = y j) : Adj (Clip a β) x y := by
  have hxy : x ≠ y := fun h => hdiff (congrFun h i)
  refine ⟨hxy, (clip_convex a β).segment_subset hx hy, ?_⟩
  intro p hp q hq z hz hop
  have hpfix : ∀ j, j ≠ i → p j = x j := by
    intro j hji
    have hzj : z j = x j := by
      obtain ⟨s, t, hs, ht, hst, heq⟩ := hz
      have hj := congrFun heq j
      change s * x j + t * y j = z j at hj
      rw [← hsame j hji, ← add_mul, hst, one_mul] at hj
      exact hj.symm
    have hzb : z j = 0 ∨ z j = 1 := by simpa only [hzj] using hxc j
    exact (fixed_bound_left hp.1 hq.1 hop j hzb).trans hzj
  rcases hxc i with hxi | hxi <;> rcases hyc i with hyi | hyi
  · exact False.elim (hdiff (hxi.trans hyi.symm))
  · refine ⟨1 - p i, p i, by linarith [(hp.1 i).2], (hp.1 i).1, by ring, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp [hxi, hyi]
    · change (1 - p i) * x j + p i * y j = p j
      rw [← hsame j hji, hpfix j hji]
      ring
  · refine ⟨p i, 1 - p i, (hp.1 i).1, by linarith [(hp.1 i).2], by ring, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp [hxi, hyi]
    · change p i * x j + (1 - p i) * y j = p j
      rw [← hsame j hji, hpfix j hji]
      ring
  · exact False.elim (hdiff (hxi.trans hyi.symm))

lemma one_step_walk {P : Set (Fin d → ℝ)} {x y : Fin d → ℝ}
    (h : x = y ∨ Adj P x y) : Walk P 1 x y := by
  refine ⟨fun k => if k = 0 then x else y, by simp, by simp, ?_⟩
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa using h

end HirschCubeCut
