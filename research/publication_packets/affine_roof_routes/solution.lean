import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.CoordinateRoute

variable {V : Type*} [DecidableEq V]

/-- A finite walk whose entire visited sequence lies in the specified set. -/
structure Route (R : V → V → Prop) (S : Finset V) (u v : V) where
  length : ℕ
  point : ℕ → V
  first : point 0 = u
  last : point length = v
  mem : ∀ i, i ≤ length → point i ∈ S
  step : ∀ i, i < length → R (point i) (point (i+1))

namespace Route

variable {R : V → V → Prop} {S T : Finset V} {u v w : V}

def nil (hu : u ∈ S) : Route R S u u where
  length := 0
  point := fun _ => u
  first := rfl
  last := rfl
  mem := fun _ _ => hu
  step := by intro i hi; omega

def prepend (hu : u ∈ S) (h : R u v) (p : Route R S v w) : Route R S u w where
  length := p.length+1
  point := fun i => if i = 0 then u else p.point (i-1)
  first := by simp
  last := by simpa using p.last
  mem := by
    intro i hi
    by_cases hz : i = 0
    · simpa [hz] using hu
    · simpa [hz] using p.mem (i-1) (by omega)
  step := by
    intro i hi
    cases i with
    | zero => simpa [p.first] using h
    | succ i => simpa using p.step i (by omega)

def mono (p : Route R S u v) (hST : S ⊆ T) : Route R T u v where
  length := p.length
  point := p.point
  first := p.first
  last := p.last
  mem := fun i hi => hST (p.mem i hi)
  step := p.step

def reverse (p : Route R S u v) (hsym : ∀ a b, R a b → R b a) : Route R S v u where
  length := p.length
  point := fun i => p.point (p.length-i)
  first := by simpa using p.last
  last := by simpa using p.first
  mem := fun i _ => p.mem (p.length-i) (Nat.sub_le _ _)
  step := by
    intro i hi
    have h := hsym _ _ (p.step (p.length-(i+1)) (by omega))
    have he : p.length-(i+1)+1 = p.length-i := by omega
    simpa only [he] using h

def append (p : Route R S u v) (q : Route R S v w) : Route R S u w where
  length := p.length+q.length
  point := fun i => if i ≤ p.length then p.point i else q.point (i-p.length)
  first := by simpa using p.first
  last := by
    by_cases hz : q.length = 0
    · have hvw : v = w := q.first.symm.trans (by simpa [hz] using q.last)
      simpa [hz] using p.last.trans hvw
    · have hn : ¬ p.length+q.length ≤ p.length := by omega
      simpa [hn] using q.last
  mem := by
    intro i hi
    by_cases h : i ≤ p.length
    · simpa only [if_pos h] using p.mem i h
    · simpa only [if_neg h] using q.mem (i-p.length) (by omega)
  step := by
    intro i hi
    by_cases h : i < p.length
    · have h0 : i ≤ p.length := by omega
      have h1 : i+1 ≤ p.length := by omega
      simpa only [if_pos h0, if_pos h1] using p.step i h
    · by_cases he : i = p.length
      · subst i
        have hn : ¬ p.length+1 ≤ p.length := by omega
        have hq := q.step 0 (by omega)
        simpa [hn, p.last, q.first] using hq
      · have h0 : ¬ i ≤ p.length := by omega
        have h1 : ¬ i+1 ≤ p.length := by omega
        have hadd : i+1-p.length = (i-p.length)+1 := by omega
        simpa only [if_neg h0, if_neg h1, hadd] using q.step (i-p.length) (by omega)

end Route

/-- Integer progress builds a route to an attained minimum. No path is input. -/
theorem descend
    (R : V → V → Prop) (S : Finset V) (f : V → ℕ) (m : ℕ)
    (hmin : ∀ x ∈ S, m ≤ f x)
    (hstep : ∀ x ∈ S, m < f x → ∃ y ∈ S, R x y ∧ f y < f x)
    (x : V) (hx : x ∈ S) :
    ∃ z : V, ∃ p : Route R S x z, f z = m ∧ p.length+m ≤ f x := by
  have aux : ∀ k : ℕ, ∀ a : V, a ∈ S → f a = k →
      ∃ z : V, ∃ p : Route R S a z, f z = m ∧ p.length+m ≤ f a := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a ha hak
      by_cases he : f a = m
      · exact ⟨a, Route.nil ha, he, by simpa [Route.nil, he]⟩
      · have hma : m < f a := by have hh := hmin a ha; omega
        obtain ⟨b, hb, hab, hba⟩ := hstep a ha hma
        obtain ⟨z, p, hpz, hlen⟩ := ih (f b) (by omega) b hb rfl
        refine ⟨z, Route.prepend ha hab p, hpz, ?_⟩
        change p.length+1+m ≤ f a
        omega
  exact aux (f x) x hx rfl

/-- Reverse ranks turn the same construction into an ascent to a maximum. -/
theorem ascend
    (R : V → V → Prop) (S : Finset V) (f : V → ℕ) (M K : ℕ)
    (hmax : ∀ x ∈ S, f x ≤ M) (hMK : M ≤ K)
    (hstep : ∀ x ∈ S, f x < M → ∃ y ∈ S, R x y ∧ f x < f y)
    (x : V) (hx : x ∈ S) :
    ∃ z : V, ∃ p : Route R S x z, f z = M ∧ p.length+f x ≤ M := by
  have hl : ∀ a ∈ S, K-M ≤ K-f a := by
    intro a ha
    have hh := hmax a ha
    omega
  have hs : ∀ a ∈ S, K-M < K-f a →
      ∃ b ∈ S, R a b ∧ K-f b < K-f a := by
    intro a ha hn
    have haM := hmax a ha
    have haK : f a ≤ K := haM.trans hMK
    obtain ⟨b, hb, hab, hlt⟩ := hstep a ha (by omega)
    have hbM := hmax b hb
    refine ⟨b, hb, hab, ?_⟩
    omega
  obtain ⟨z, p, he, hlen⟩ := descend R S (fun a => K-f a) (K-M) hl hs x hx
  have hzM := hmax z (by rw [← p.last]; exact p.mem _ le_rfl)
  have hxM := hmax x hx
  refine ⟨z, p, ?_, ?_⟩ <;> omega

/-- The two-front face induction. Coordinates here are integer ranks. -/
theorem rank_routes
    (d : ℕ) (R : V → V → Prop) (hsym : ∀ a b, R a b → R b a)
    (c : V → Fin d → ℕ) (hinj : Function.Injective c) (K : Fin d → ℕ)
    (Face : Finset V → Prop)
    (hminface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c a j ≤ c x j) → Face (F.filter (fun x => c x j = c a j)))
    (hmaxface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c x j ≤ c a j) → Face (F.filter (fun x => c x j = c a j)))
    (hdown : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c y j < c x j → ∃ z ∈ F, R x z ∧ c z j < c x j)
    (hup : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c x j < c y j → ∃ z ∈ F, R x z ∧ c x j < c z j) :
    ∀ J : Finset (Fin d), ∀ F, Face F →
      (∀ x ∈ F, ∀ j, c x j ≤ K j) →
      (∀ j, j ∉ J → ∀ x ∈ F, ∀ y ∈ F, c x j = c y j) →
      ∀ u, u ∈ F → ∀ v, v ∈ F →
      ∃ p : Route R F u v, p.length ≤ ∑ j ∈ J, K j := by
  classical
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro F hF hK hfixed u hu v hv
    have huv : u = v := hinj (funext (fun j => hfixed j (by simp) u hu v hv))
    subst v
    exact ⟨Route.nil hu, by simp [Route.nil]⟩
  | @insert j J hj ih =>
    intro F hF hK hfixed u hu v hv
    have finish : ∀ (t : ℕ) (a b : V) (p : Route R F u a) (q : Route R F v b),
        c a j = t → c b j = t →
        Face (F.filter (fun x => c x j = t)) →
        p.length+q.length ≤ K j →
        ∃ r : Route R F u v, r.length ≤ ∑ i ∈ insert j J, K i := by
      intro t a b p q ha hb hface hcost
      let F' := F.filter (fun x => c x j = t)
      have hsub : F' ⊆ F := Finset.filter_subset _ _
      have hfa : a ∈ F' := Finset.mem_filter.mpr
        ⟨by rw [← p.last]; exact p.mem _ le_rfl, ha⟩
      have hfb : b ∈ F' := Finset.mem_filter.mpr
        ⟨by rw [← q.last]; exact q.mem _ le_rfl, hb⟩
      have hfix' : ∀ i, i ∉ J → ∀ x ∈ F', ∀ y ∈ F', c x i = c y i := by
        intro i hi x hx y hy
        by_cases he : i = j
        · subst i
          exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
        · exact hfixed i (by simp [he, hi]) x (hsub hx) y (hsub hy)
      obtain ⟨middle, hmiddle⟩ := ih F' hface
        (fun x hx i => hK x (hsub hx) i) hfix' a hfa b hfb
      let r := p.append ((middle.mono hsub).append (q.reverse hsym))
      refine ⟨r, ?_⟩
      have hsum : (∑ i ∈ insert j J, K i) = K j + ∑ i ∈ J, K i :=
        Finset.sum_insert hj
      rw [hsum]
      change p.length+(middle.length+q.length) ≤ K j + ∑ i ∈ J, K i
      omega
    by_cases hside : c u j+c v j ≤ K j
    · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image F (fun x => c x j) ⟨u, hu⟩
      have hs : ∀ x ∈ F, c a j < c x j → ∃ y ∈ F, R x y ∧ c y j < c x j :=
        fun x hx hh => hdown F hF j x hx a ha hh
      obtain ⟨a', p, hpa, hp⟩ := descend R F (fun x => c x j) (c a j) hmin hs u hu
      obtain ⟨b', q, hqa, hq⟩ := descend R F (fun x => c x j) (c a j) hmin hs v hv
      exact finish (c a j) a' b' p q hpa hqa (hminface F hF j a ha hmin) (by omega)
    · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image F (fun x => c x j) ⟨u, hu⟩
      have hs : ∀ x ∈ F, c x j < c a j → ∃ y ∈ F, R x y ∧ c x j < c y j :=
        fun x hx hh => hup F hF j x hx a ha hh
      obtain ⟨a', p, hpa, hp⟩ := ascend R F (fun x => c x j) (c a j) (K j)
        hmax (hK a ha j) hs u hu
      obtain ⟨b', q, hqa, hq⟩ := ascend R F (fun x => c x j) (c a j) (K j)
        hmax (hK a ha j) hs v hv
      have haK := hK a ha j
      exact finish (c a j) a' b' p q hpa hqa (hmaxface F hF j a ha hmax) (by omega)

/-- Rank of an actual real coordinate in its finite observed level set. -/
def levelRank (S : Finset ℝ) (x : ℝ) : ℕ := (S.filter (fun t => t < x)).card

lemma levelRank_mono (S : Finset ℝ) {x y : ℝ} (hxy : x ≤ y) :
    levelRank S x ≤ levelRank S y := by
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
    (Finset.mem_filter.mp hz).2.trans_le hxy⟩

lemma levelRank_strict (S : Finset ℝ) {x y : ℝ} (hx : x ∈ S) (hxy : x < y) :
    levelRank S x < levelRank S y := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
      (Finset.mem_filter.mp hz).2.trans hxy⟩
  · intro he
    have hm : x ∈ S.filter (fun z => z < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← he] at hm
    exact (lt_irrefl x) (Finset.mem_filter.mp hm).2

lemma levelRank_lt_iff (S : Finset ℝ) {x y : ℝ} (hx : x ∈ S) :
    levelRank S x < levelRank S y ↔ x < y := by
  constructor
  · intro h
    by_contra hn
    have hh := levelRank_mono S (le_of_not_gt hn)
    omega
  · exact levelRank_strict S hx

lemma levelRank_eq_iff (S : Finset ℝ) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    levelRank S x = levelRank S y ↔ x = y := by
  constructor
  · intro he
    rcases lt_trichotomy x y with h | h | h
    · have hh := levelRank_strict S hx h
      omega
    · exact h
    · have hh := levelRank_strict S hy h
      omega
  · intro he
    rw [he]

lemma levelRank_bound (S : Finset ℝ) {x : ℝ} (hx : x ∈ S) :
    levelRank S x ≤ S.card-1 := by
  have h : levelRank S x < S.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hm : x ∈ S.filter (fun t => t < x) := by rw [he]; exact hx
    exact (lt_irrefl x) (Finset.mem_filter.mp hm).2
  omega

#print axioms descend
#print axioms ascend
#print axioms rank_routes
#print axioms levelRank_bound

end Hirsch.CoordinateRoute

/-- A finite-face coordinate routing theorem. The local hypotheses are one-step
improvement and extreme-face closure, never a pre-existing short route. -/
theorem finite_coordinate_route_bound
    (n d : ℕ) (R : Fin n → Fin n → Prop)
    (hsym : ∀ a b, R a b → R b a)
    (c : Fin n → Fin d → ℝ) (hinj : Function.Injective c)
    (Face : Finset (Fin n) → Prop)
    (hminface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c a j ≤ c x j) → Face (F.filter (fun x => c x j = c a j)))
    (hmaxface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c x j ≤ c a j) → Face (F.filter (fun x => c x j = c a j)))
    (hdown : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c y j < c x j → ∃ z ∈ F, R x z ∧ c z j < c x j)
    (hup : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c x j < c y j → ∃ z ∈ F, R x z ∧ c x j < c z j)
    (F : Finset (Fin n)) (hF : Face F)
    (u v : Fin n) (hu : u ∈ F) (hv : v ∈ F) :
    ∃ L : ℕ, L ≤ ∑ j : Fin d,
        ((Finset.univ.image (fun x : Fin n => c x j)).card-1) ∧
      ∃ p : ℕ → Fin n, p 0 = u ∧ p L = v ∧
        (∀ i, i ≤ L → p i ∈ F) ∧ (∀ i, i < L → R (p i) (p (i+1))) := by
  classical
  let levels : Fin d → Finset ℝ := fun j => Finset.univ.image (fun x : Fin n => c x j)
  let rank : Fin n → Fin d → ℕ := fun x j => Hirsch.CoordinateRoute.levelRank (levels j) (c x j)
  let K : Fin d → ℕ := fun j => (levels j).card-1
  have hmem : ∀ x j, c x j ∈ levels j :=
    fun x j => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hlt : ∀ x y j, rank x j < rank y j ↔ c x j < c y j :=
    fun x y j => Hirsch.CoordinateRoute.levelRank_lt_iff (levels j) (hmem x j)
  have heq : ∀ x y j, rank x j = rank y j ↔ c x j = c y j :=
    fun x y j => Hirsch.CoordinateRoute.levelRank_eq_iff (levels j) (hmem x j) (hmem y j)
  have hle : ∀ x y j, rank x j ≤ rank y j → c x j ≤ c y j := by
    intro x y j hh
    by_contra hn
    have hr := (hlt y x j).mpr (lt_of_not_ge hn)
    omega
  have hrinj : Function.Injective rank := by
    intro x y he
    apply hinj
    funext j
    exact (heq x y j).mp (congrFun he j)
  have hfilter : ∀ G : Finset (Fin n), ∀ j a,
      G.filter (fun x => rank x j = rank a j) = G.filter (fun x => c x j = c a j) := by
    intro G j a
    apply Finset.filter_congr
    intro x hx
    exact heq x a j
  have hm : ∀ G, Face G → ∀ j a, a ∈ G →
      (∀ x ∈ G, rank a j ≤ rank x j) → Face (G.filter (fun x => rank x j = rank a j)) := by
    intro G hG j a ha hh
    rw [hfilter]
    exact hminface G hG j a ha (fun x hx => hle a x j (hh x hx))
  have hM : ∀ G, Face G → ∀ j a, a ∈ G →
      (∀ x ∈ G, rank x j ≤ rank a j) → Face (G.filter (fun x => rank x j = rank a j)) := by
    intro G hG j a ha hh
    rw [hfilter]
    exact hmaxface G hG j a ha (fun x hx => hle x a j (hh x hx))
  have hd : ∀ G, Face G → ∀ j x, x ∈ G → ∀ y, y ∈ G →
      rank y j < rank x j → ∃ z ∈ G, R x z ∧ rank z j < rank x j := by
    intro G hG j x hx y hy hh
    obtain ⟨z, hz, hxz, hh'⟩ := hdown G hG j x hx y hy ((hlt y x j).mp hh)
    exact ⟨z, hz, hxz, (hlt z x j).mpr hh'⟩
  have hu' : ∀ G, Face G → ∀ j x, x ∈ G → ∀ y, y ∈ G →
      rank x j < rank y j → ∃ z ∈ G, R x z ∧ rank x j < rank z j := by
    intro G hG j x hx y hy hh
    obtain ⟨z, hz, hxz, hh'⟩ := hup G hG j x hx y hy ((hlt x y j).mp hh)
    exact ⟨z, hz, hxz, (hlt x z j).mpr hh'⟩
  obtain ⟨p, hp⟩ := Hirsch.CoordinateRoute.rank_routes d R hsym rank hrinj K Face hm hM hd hu'
    Finset.univ F hF
    (fun x hx j => Hirsch.CoordinateRoute.levelRank_bound (levels j) (hmem x j))
    (by intro j hj; exact False.elim (hj (Finset.mem_univ j))) u hu v hv
  refine ⟨p.length, ?_, p.point, p.first, p.last, p.mem, p.step⟩
  simpa only [K, levels] using hp

#print axioms finite_coordinate_route_bound

namespace Hirsch.HullCoordinate

open Set

lemma finite_margin {ι : Type*} (S : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ S, 0 < a i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i ∈ S, e * |t i| < a i := by
  classical
  revert ha
  induction S using Finset.induction_on with
  | empty =>
      intro ha
      exact ⟨1, by norm_num, by simp⟩
  | @insert i S hi ih =>
      intro ha
      obtain ⟨e, he, hS⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai : 0 < a i := ha i (Finset.mem_insert_self i S)
      have hd : 0 < |t i| + 1 := by positivity
      let f : ℝ := a i / (|t i| + 1)
      have hf : 0 < f := div_pos hai hd
      have hfeq : f * (|t i| + 1) = a i := by
        dsimp [f]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      refine ⟨min e f, lt_min he hf, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have hb := mul_le_mul_of_nonneg_right (min_le_right e f) (abs_nonneg (t i))
        nlinarith
      · exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (min_le_left e f) (abs_nonneg (t j))) (hS j hj)

lemma small_shift (a b e : ℝ) (ha : a ≠ 0) (he : 0 < e)
    (hsmall : e * |b| < |a|) :
    a + e*b ≠ 0 ∧ (0 < a + e*b ↔ 0 < a) := by
  have hlo := mul_le_mul_of_nonneg_left (neg_abs_le b) he.le
  have hhi := mul_le_mul_of_nonneg_left (le_abs_self b) he.le
  by_cases hp : 0 < a
  · rw [abs_of_pos hp] at hsmall
    have hpos : 0 < a + e*b := by nlinarith
    exact ⟨ne_of_gt hpos, iff_of_true hpos hp⟩
  · have hn : a < 0 := lt_of_le_of_ne (le_of_not_gt hp) ha
    rw [abs_of_neg hn] at hsmall
    have hneg : a + e*b < 0 := by nlinarith
    exact ⟨ne_of_lt hneg, iff_of_false (not_lt.mpr hneg.le) hp⟩

/-- Resolve every nonzero vector in a finite test set, preserving every
already nonzero sign. The separating functional and perturbation are derived. -/
theorem regularize_on {d : ℕ} (S : Finset (Fin d → ℝ))
    (g : (Fin d → ℝ) →ₗ[ℝ] ℝ) :
    ∃ k : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ v ∈ S, v ≠ 0 → k v ≠ 0) ∧
      ∀ v ∈ S, g v ≠ 0 → (0 < k v ↔ 0 < g v) := by
  classical
  let U := S.filter (fun v => v ≠ 0)
  obtain ⟨h, hh⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun v : U => v.val) (fun v => (Finset.mem_filter.mp v.property).2)
  let J := U.filter (fun v => g v ≠ 0)
  have hpos : ∀ v ∈ J, 0 < |g v| := by
    intro v hv
    exact abs_pos.mpr (Finset.mem_filter.mp hv).2
  obtain ⟨e, he, hsmall⟩ := finite_margin J (fun v => |g v|) (fun v => h v) hpos
  let k : (Fin d → ℝ) →ₗ[ℝ] ℝ := g + e • h
  have hval : ∀ v, k v = g v + e * h v := by intro v; simp [k]
  have hkeep : ∀ v ∈ S, g v ≠ 0 → k v ≠ 0 ∧ (0 < k v ↔ 0 < g v) := by
    intro v hv hgv
    have hv0 : v ≠ 0 := by intro hzero; rw [hzero,map_zero] at hgv; exact hgv rfl
    have hvU : v ∈ U := Finset.mem_filter.mpr ⟨hv,hv0⟩
    have hvJ : v ∈ J := Finset.mem_filter.mpr ⟨hvU,hgv⟩
    rw [hval]
    exact small_shift (g v) (h v) e hgv he (hsmall v hvJ)
  refine ⟨k, ?_, fun v hv hg => (hkeep v hv hg).2⟩
  intro v hv hv0
  by_cases hgv : g v = 0
  · have hvU : v ∈ U := Finset.mem_filter.mpr ⟨hv,hv0⟩
    have hhv : h v ≠ 0 := hh ⟨v,hvU⟩
    rw [hval,hgv,zero_add]
    exact mul_ne_zero (ne_of_gt he) hhv
  · exact (hkeep v hv hgv).1


private lemma segment_parameter {d : ℕ} (u v z : Fin d → ℝ)
    (hz : z ∈ segment ℝ u v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = u + t • (v-u) := by
  obtain ⟨s,t,hs,ht,hst,he⟩ := hz
  refine ⟨t,ht,by linarith,?_⟩
  have hs' : s = 1-t := by linarith
  rw [← he,hs']
  module

private lemma line_injective {d : ℕ} (D : Fin d → ℝ) (hD : D ≠ 0) :
    Function.Injective (fun t : ℝ => t • D) := by
  have hex : ∃ i, D i ≠ 0 := by
    by_contra hn
    apply hD
    funext i
    by_contra hi
    exact hn ⟨i,hi⟩
  obtain ⟨i,hi⟩ := hex
  intro s t he
  have hh := congrFun he i
  change s * D i = t * D i at hh
  exact mul_right_cancel₀ hi hh

lemma left_extreme_segment {d : ℕ} (u v : Fin d → ℝ) (hne : u ≠ v) :
    u ∈ (segment ℝ u v).extremePoints ℝ := by
  refine ⟨left_mem_segment ℝ _ _,?_⟩
  intro x hx y hy hseg
  obtain ⟨a,ha0,ha1,hxa⟩ := segment_parameter u v x hx
  obtain ⟨b,hb0,hb1,hyb⟩ := segment_parameter u v y hy
  obtain ⟨s,t,hs,ht,hst,he⟩ := hseg
  have hs' : s = 1-t := by linarith
  have hline : u+(s*a+t*b) • (v-u) = u := by
    calc
      u+(s*a+t*b) • (v-u) = s • (u+a • (v-u))+t • (u+b • (v-u)) := by
        rw [hs']
        module
      _ = u := by rw [← hxa,← hyb]; exact he
  have hD : v-u ≠ 0 := fun h => hne (sub_eq_zero.mp h).symm
  have hh : (s*a+t*b) • (v-u) = (0 : ℝ) • (v-u) := by
    apply add_left_cancel (a := u)
    simpa only [zero_smul,add_zero] using hline
  have hzero := line_injective (v-u) hD hh
  have hpa := mul_nonneg hs.le ha0
  have hpb := mul_nonneg ht.le hb0
  have hsa : s*a = 0 := by linarith
  have ha : a = 0 := (mul_eq_zero.mp hsa).resolve_left (ne_of_gt hs)
  simpa only [ha,zero_smul,add_zero] using hxa


end Hirsch.HullCoordinate

namespace Hirsch.HullCoordinate

open Set

variable {d : ℕ}

/-- Linear upper bounds extend from the original generators to their entire hull. -/
lemma hull_le (C : Finset (Fin d → ℝ)) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (M : ℝ) (hC : ∀ x ∈ C, f x ≤ M) :
    ∀ x ∈ convexHull ℝ (C : Set (Fin d → ℝ)), f x ≤ M := by
  apply convexHull_min hC
  intro x hx y hy a b ha hb hab
  change f (a • x+b • y) ≤ M
  simp only [map_add, map_smul, smul_eq_mul]
  calc
    a*f x+b*f y ≤ a*M+b*M := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = M := by rw [← add_mul, hab, one_mul]

/-- Equality in an upper support bound uses only maximizing generators.
The target K may be any convex set, not a supplied face or edge. -/
lemma hull_support (C : Finset (Fin d → ℝ)) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (M : ℝ) (K : Set (Fin d → ℝ)) (hK : Convex ℝ K)
    (hC : ∀ x ∈ C, f x ≤ M ∧ (f x=M → x ∈ K)) :
    ∀ x ∈ convexHull ℝ (C : Set (Fin d → ℝ)),
      f x ≤ M ∧ (f x=M → x ∈ K) := by
  apply convexHull_min hC
  intro x hx y hy a b ha hb hab
  change f (a • x+b • y) ≤ M ∧ (f (a • x+b • y)=M → a • x+b • y ∈ K)
  have hval : f (a • x+b • y)=a*f x+b*f y := by
    simp only [map_add, map_smul, smul_eq_mul]
  constructor
  · rw [hval]
    calc
      a*f x+b*f y ≤ a*M+b*M := add_le_add
        (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
      _ = M := by rw [← add_mul, hab, one_mul]
  · intro he
    by_cases ha0 : a=0
    · have hb1 : b=1 := by linarith
      have hyM : f y=M := by simpa [ha0, hb1] using he
      simpa [ha0, hb1] using hy.2 hyM
    by_cases hb0 : b=0
    · have ha1 : a=1 := by linarith
      have hxM : f x=M := by simpa [ha1, hb0] using he
      simpa [ha1, hb0] using hx.2 hxM
    have hsum : a*(M-f x)+b*(M-f y)=0 := by
      calc
        a*(M-f x)+b*(M-f y) = (a+b)*M-(a*f x+b*f y) := by ring
        _ = 0 := by rw [hab, one_mul, ← hval, he, sub_self]
    have hax := mul_nonneg ha (sub_nonneg.mpr hx.1)
    have hby := mul_nonneg hb (sub_nonneg.mpr hy.1)
    have hax0 : a*(M-f x)=0 := by linarith
    have hby0 : b*(M-f y)=0 := by linarith
    have hxM : f x=M :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hax0).resolve_left ha0)).symm
    have hyM : f y=M :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hby0).resolve_left hb0)).symm
    exact hK (hx.2 hxM) (hy.2 hyM) ha hb hab

/-- The strict functional is derived from the requested actual vertex.
This generalizes the finite-corner separation argument used in accepted #316. -/
lemma strict_vertex_functional (C : Finset (Fin d → ℝ)) (u : Fin d → ℝ)
    (hu : u ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) :
    ∃ h : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      ∀ x ∈ C, x ≠ u → 0 < h (x-u) := by
  classical
  let P := convexHull ℝ (C : Set (Fin d → ℝ))
  have hcv : Convex ℝ P := convex_convexHull ℝ _
  have hremove : Convex ℝ (P \ {u}) :=
    (hcv.mem_extremePoints_iff_convex_diff.mp hu).2
  have hsub : convexHull ℝ ((C : Set (Fin d → ℝ)) \ {u}) ⊆ P \ {u} :=
    convexHull_min (fun x hx => ⟨subset_convexHull ℝ _ hx.1, hx.2⟩) hremove
  have hnot : u ∉ convexHull ℝ ((C : Set (Fin d → ℝ)) \ {u}) := by
    intro h
    exact (hsub h).2 (Set.mem_singleton u)
  have hfinite : ((C : Set (Fin d → ℝ)) \ {u}).Finite :=
    C.finite_toSet.subset Set.diff_subset
  obtain ⟨f, c, hfc, hcu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (hfinite.isClosed_convexHull ℝ) hnot
  refine ⟨-f.toLinearMap, ?_⟩
  intro x hx hxu
  have hx' : x ∈ (C : Set (Fin d → ℝ)) \ {u} :=
    ⟨hx, by simpa only [Set.mem_singleton_iff] using hxu⟩
  have hlt : f x < f u := (hfc x (subset_convexHull ℝ _ hx')).trans hcu
  change 0 < -(f.toLinearMap (x-u))
  rw [map_sub]
  change 0 < -(f x-f u)
  linarith

/-- A better feasible value supplies a better original generator. -/
lemma improving_generator (C : Finset (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (u y : Fin d → ℝ)
    (hy : y ∈ convexHull ℝ (C : Set (Fin d → ℝ))) (hfy : f u < f y) :
    ∃ x ∈ C, f u < f x := by
  by_contra hn
  have hC : ∀ x ∈ C, f x ≤ f u := by
    intro x hx
    by_contra hh
    exact hn ⟨x, hx, lt_of_not_ge hh⟩
  exact (not_le_of_gt hfy) (hull_le C f (f u) hC y hy)

/-- From an actual vertex and any better feasible point, construct a better
actual vertex joined by a whole nondegenerate ORIGINAL exposed segment.
The finite generator list may contain redundant/interior points. -/
theorem improving_edge (C : Finset (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (u y : Fin d → ℝ)
    (hu : u ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)
    (hy : y ∈ convexHull ℝ (C : Set (Fin d → ℝ))) (hfy : f u < f y) :
    ∃ v ∈ C, v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ ∧
      f u < f v ∧ u ≠ v ∧
      IsExposed ℝ (convexHull ℝ (C : Set (Fin d → ℝ))) (segment ℝ u v) := by
  classical
  obtain ⟨h, hh⟩ := strict_vertex_functional C u hu
  obtain ⟨a, haC, hfa⟩ := improving_generator C f u y hy hfy
  have hau : a ≠ u := by intro he; rw [he] at hfa; exact (lt_irrefl _) hfa
  let D := C.erase u
  have haD : a ∈ D := Finset.mem_erase.mpr ⟨hau, haC⟩
  have hD : ∀ x ∈ D, 0 < h (x-u) :=
    fun x hx => hh x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1
  let contrast : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ) :=
    fun x z => h (x-u) • (z-u)-h (z-u) • (x-u)
  let S := (D.product D).image (fun p => contrast p.1 p.2)
  have hS : ∀ x ∈ D, ∀ z ∈ D, contrast x z ∈ S := by
    intro x hx z hz
    exact Finset.mem_image.mpr ⟨(x,z), Finset.mem_product.mpr ⟨hx,hz⟩, rfl⟩
  obtain ⟨g, hreg, hkeep⟩ := regularize_on S f
  obtain ⟨r, hrD, hrmax⟩ := Finset.exists_max_image D
    (fun x => g (x-u)/h (x-u)) ⟨a,haD⟩
  let M := g (r-u)/h (r-u)
  let q : (Fin d → ℝ) →ₗ[ℝ] ℝ := g-M • h
  have hq : ∀ z, q z=g z-M*h z := by intro z; simp [q, smul_eq_mul]
  have hMr : M*h (r-u)=g (r-u) := div_mul_cancel₀ _ (ne_of_gt (hD r hrD))
  have hqr : q (r-u)=0 := by rw [hq, hMr, sub_self]
  have hbound : ∀ x ∈ D, g (x-u) ≤ M*h (x-u) := by
    intro x hx
    exact (div_le_iff₀ (hD x hx)).mp (hrmax x hx)
  have hqbound : ∀ x ∈ C, q (x-u) ≤ 0 := by
    intro x hx
    by_cases he : x=u
    · simp [he]
    · rw [hq]
      exact sub_nonpos.mpr (hbound x (Finset.mem_erase.mpr ⟨he,hx⟩))
  let T := D.filter (fun x => q (x-u)=0)
  have hrT : r ∈ T := Finset.mem_filter.mpr ⟨hrD,hqr⟩
  obtain ⟨v, hvT, hvmax⟩ := Finset.exists_max_image T (fun x => h (x-u)) ⟨r,hrT⟩
  have hvD : v ∈ D := (Finset.mem_filter.mp hvT).1
  have hvC : v ∈ C := (Finset.mem_erase.mp hvD).2
  have hvu : v ≠ u := (Finset.mem_erase.mp hvD).1
  have hqv : q (v-u)=0 := (Finset.mem_filter.mp hvT).2
  have hgv : g (v-u)=M*h (v-u) := by
    have ht := hqv
    rw [hq] at ht
    exact sub_eq_zero.mp ht
  have hcontrast : ∀ l : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∀ x z,
      l (contrast x z)=h (x-u)*l (z-u)-h (z-u)*l (x-u) := by
    intro l x z
    simp only [contrast, map_sub, map_smul, smul_eq_mul]
  have hfv : f u < f v := by
    have hfa' : 0 < f (a-u) := by rw [map_sub]; exact sub_pos.mpr hfa
    have hfv' : 0 < f (v-u) := by
      by_contra hn
      have hnon : f (v-u) ≤ 0 := le_of_not_gt hn
      have hpos : 0 < f (contrast v a) := by
        rw [hcontrast]
        have hp := mul_pos (hD v hvD) hfa'
        have hn' := mul_nonpos_of_nonneg_of_nonpos (hD a haD).le hnon
        linarith
      have hgpos : 0 < g (contrast v a) :=
        (hkeep _ (hS v hvD a haD) (ne_of_gt hpos)).mpr hpos
      have hgle : g (contrast v a) ≤ 0 := by
        rw [hcontrast, hgv]
        calc
          h (v-u)*g (a-u)-h (a-u)*(M*h (v-u)) ≤
              h (v-u)*(M*h (a-u))-h (a-u)*(M*h (v-u)) :=
            sub_le_sub_right (mul_le_mul_of_nonneg_left (hbound a haD) (hD v hvD).le) _
          _ = 0 := by ring
      exact (not_le_of_gt hgpos) hgle
    rw [map_sub] at hfv'
    exact sub_pos.mp hfv'
  have htied : ∀ x ∈ C, q x=q u → x ∈ segment ℝ u v := by
    intro x hx he
    by_cases hxu : x=u
    · rw [hxu]
      exact left_mem_segment ℝ _ _
    have hxD : x ∈ D := Finset.mem_erase.mpr ⟨hxu,hx⟩
    have hqx : q (x-u)=0 := by rw [map_sub,he,sub_self]
    have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hxD,hqx⟩
    have hgx : g (x-u)=M*h (x-u) := by
      rw [hq] at hqx
      exact sub_eq_zero.mp hqx
    have hgc : g (contrast v x)=0 := by rw [hcontrast,hgx,hgv]; ring
    have hc0 : contrast v x=0 := by
      by_contra hc
      exact hreg _ (hS v hvD x hxD) hc hgc
    have hscaled : h (v-u) • (x-u)=h (x-u) • (v-u) := sub_eq_zero.mp hc0
    let t : ℝ := h (x-u)/h (v-u)
    have ht0 : 0 ≤ t := (div_pos (hD x hxD) (hD v hvD)).le
    have ht1 : t ≤ 1 := (div_le_one (hD v hvD)).mpr (hvmax x hxT)
    have hdiff : x-u=t • (v-u) := by
      calc
        x-u = (h (v-u))⁻¹ • (h (v-u) • (x-u)) := by
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (hD v hvD)), one_smul]
        _ = t • (v-u) := by
          rw [hscaled,smul_smul]
          congr 1
          dsimp [t]
          rw [div_eq_mul_inv, mul_comm]
    have hxeq : x=u+t • (v-u) := by rw [← hdiff]; abel
    refine ⟨1-t,t,sub_nonneg.mpr ht1,ht0,by ring,?_⟩
    rw [hxeq]
    module
  have hC : ∀ x ∈ C, q x ≤ q u ∧ (q x=q u → x ∈ segment ℝ u v) := by
    intro x hx
    refine ⟨?_,htied x hx⟩
    have hle := hqbound x hx
    rw [map_sub] at hle
    linarith
  have hsupport := hull_support C q (q u) (segment ℝ u v) (convex_segment u v) hC
  have hvP : v ∈ convexHull ℝ (C : Set (Fin d → ℝ)) := subset_convexHull ℝ _ hvC
  have hqvu : q v=q u := by
    rw [map_sub] at hqv
    exact sub_eq_zero.mp hqv
  have hex : IsExposed ℝ (convexHull ℝ (C : Set (Fin d → ℝ))) (segment ℝ u v) := by
    intro _
    refine ⟨q.toContinuousLinearMap,?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨a,b,ha,hb,hab,heq⟩ := hx
      have hxP := heq ▸ (convex_convexHull ℝ (C : Set (Fin d → ℝ))) hu.1 hvP ha hb hab
      have hqx : q x=q u := by
        rw [← heq,map_add,map_smul,map_smul,hqvu]
        change a*q u+b*q u=q u
        rw [← add_mul,hab,one_mul]
      refine ⟨hxP,?_⟩
      intro z hz
      change q z ≤ q x
      rw [hqx]
      exact (hsupport z hz).1
    · rintro ⟨hx,hmax⟩
      have hlow := hmax u hu.1
      change q u ≤ q x at hlow
      exact (hsupport x hx).2 (le_antisymm (hsupport x hx).1 hlow)
  have hvext : v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ := by
    apply hex.isExtreme.extremePoints_subset_extremePoints
    rw [segment_symm]
    exact left_extreme_segment v u hvu
  exact ⟨v,hvC,hvext,hfv,Ne.symm hvu,hex⟩

end Hirsch.HullCoordinate

namespace Hirsch.HullCoordinate

open Set

variable {d : ℕ}

def coordinate (j : Fin d) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Filtering original generators at an attained linear maximum gives the
entire exposed hull face, not just a subset of its vertices. -/
lemma hull_filter_exposed {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (c : ι → (Fin d → ℝ))
    (f : (Fin d → ℝ) →ₗ[ℝ] ℝ) (a : ι) (ha : a ∈ F)
    (hmax : ∀ x ∈ F, f (c x) ≤ f (c a)) :
    IsExposed ℝ (convexHull ℝ (F.image c : Set (Fin d → ℝ)))
      (convexHull ℝ ((F.filter (fun x => f (c x)=f (c a))).image c : Set (Fin d → ℝ))) := by
  classical
  let T := F.filter (fun x => f (c x)=f (c a))
  let K := convexHull ℝ (T.image c : Set (Fin d → ℝ))
  have hsub : K ⊆ convexHull ℝ (F.image c : Set (Fin d → ℝ)) := by
    apply convexHull_mono
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i,(Finset.mem_filter.mp hi).1,rfl⟩
  have hconst : ∀ x ∈ K, f x=f (c a) := by
    apply convexHull_min
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro x hx y hy s t hs ht hst
      change f (s • x+t • y)=f (c a)
      rw [map_add,map_smul,map_smul,hx,hy]
      change s*f (c a)+t*f (c a)=f (c a)
      rw [← add_mul,hst,one_mul]
  have hC : ∀ x ∈ F.image c, f x ≤ f (c a) ∧ (f x=f (c a) → x ∈ K) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    refine ⟨hmax i hi,?_⟩
    intro he
    apply subset_convexHull ℝ _
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,he⟩,rfl⟩
  have hsup := hull_support (F.image c) f (f (c a)) K (convex_convexHull ℝ _) hC
  have haP : c a ∈ convexHull ℝ (F.image c : Set (Fin d → ℝ)) :=
    subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  intro _
  refine ⟨f.toContinuousLinearMap,?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨hsub hx,?_⟩
    intro y hy
    change f y ≤ f x
    rw [hconst x hx]
    exact (hsup y hy).1
  · rintro ⟨hx,hmaxx⟩
    have hlo := hmaxx (c a) haP
    change f (c a) ≤ f x at hlo
    exact (hsup x hx).2 (le_antisymm (hsup x hx).1 hlo)

noncomputable def vertices (C : Finset (Fin d → ℝ)) : Finset (Fin d → ℝ) := by
  classical
  exact C.filter (fun x => x ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)

/-- Prune arbitrary finite generators to the ACTUAL vertices without assuming
a supplied complete vertex catalogue. -/
lemma vertex_hull (C : Finset (Fin d → ℝ)) :
    convexHull ℝ (vertices C : Set (Fin d → ℝ)) = convexHull ℝ (C : Set (Fin d → ℝ)) := by
  classical
  let V := vertices C
  have hV : (V : Set (Fin d → ℝ)) = (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset hx,hx⟩
  have he := closure_convexHull_extremePoints (C.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ (C : Set (Fin d → ℝ)))
  have hclosed := V.finite_toSet.isClosed_convexHull ℝ
  rw [← hV, hclosed.closure_eq] at he
  exact he

/-- The geometric adapter: actual vertices, actual original extreme segments,
and actual coordinate levels. All local graph/face hypotheses are derived. -/
theorem original_routes (C : Finset (Fin d → ℝ)) (u v : Fin d → ℝ)
    (hu : u ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)
    (hv : v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) :
    let V := vertices C
    ∃ L : ℕ, L ≤ ∑ j : Fin d, ((V.image (fun x => x j)).card-1) ∧
      ∃ p : Fin (L+1) → (Fin d → ℝ), p 0=u ∧ p (Fin.last L)=v ∧
        (∀ i, p i ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) ∧
        ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
          IsExtreme ℝ (convexHull ℝ (C : Set (Fin d → ℝ)))
            (segment ℝ (p i.castSucc) (p i.succ)) := by
  classical
  let P := convexHull ℝ (C : Set (Fin d → ℝ))
  let V := vertices C
  let E := Fintype.equivFin V
  let c : Fin (Fintype.card V) → (Fin d → ℝ) := fun i => (E.symm i).val
  have hc : Function.Injective c := by
    intro i j hij
    apply E.symm.injective
    exact Subtype.ext hij
  have hvertices : ∀ i, c i ∈ P.extremePoints ℝ :=
    fun i => (Finset.mem_filter.mp (E.symm i).property).2
  let Face : Finset (Fin (Fintype.card V)) → Prop :=
    fun F => IsExtreme ℝ P (convexHull ℝ (F.image c : Set (Fin d → ℝ)))
  let R : Fin (Fintype.card V) → Fin (Fintype.card V) → Prop :=
    fun i j => c i ≠ c j ∧ IsExtreme ℝ P (segment ℝ (c i) (c j))
  have hsym : ∀ i j, R i j → R j i := by
    intro i j hij
    exact ⟨Ne.symm hij.1, by rw [segment_symm]; exact hij.2⟩
  have hmaxface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c x j ≤ c a j) → Face (F.filter (fun x => c x j=c a j)) := by
    intro F hF j a ha hm
    exact hF.trans (hull_filter_exposed F c (coordinate j) a ha hm).isExtreme
  have hminface : ∀ F, Face F → ∀ j a, a ∈ F →
      (∀ x ∈ F, c a j ≤ c x j) → Face (F.filter (fun x => c x j=c a j)) := by
    intro F hF j a ha hm
    have hn : ∀ x ∈ F, (-coordinate j) (c x) ≤ (-coordinate j) (c a) := by
      intro x hx
      change -c x j ≤ -c a j
      exact neg_le_neg (hm x hx)
    have he : F.filter (fun x => (-coordinate j) (c x)=(-coordinate j) (c a)) =
        F.filter (fun x => c x j=c a j) := by
      apply Finset.filter_congr
      intro x hx
      change (-c x j = -c a j) ↔ c x j=c a j
      exact neg_inj
    have h := hF.trans (hull_filter_exposed F c (-coordinate j) a ha hn).isExtreme
    rw [he] at h
    exact h
  have himprove : ∀ F, Face F → ∀ f : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      ∀ x, x ∈ F → ∀ y, y ∈ F → f (c x) < f (c y) →
      ∃ z ∈ F, R x z ∧ f (c x) < f (c z) := by
    intro F hF f x hx y hy hf
    have hxK : c x ∈ convexHull ℝ (F.image c : Set (Fin d → ℝ)) :=
      subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    have hyK : c y ∈ convexHull ℝ (F.image c : Set (Fin d → ℝ)) :=
      subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
    have hxE : c x ∈ (convexHull ℝ (F.image c : Set (Fin d → ℝ))).extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset hF.subset ⟨hxK,hvertices x⟩
    obtain ⟨z,hz,_,hfz,hxz,hseg⟩ := improving_edge (F.image c) f (c x) (c y) hxE hyK hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i,hi,⟨hxz,hF.trans hseg.isExtreme⟩,hfz⟩
  have hdown : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c y j < c x j → ∃ z ∈ F, R x z ∧ c z j < c x j := by
    intro F hF j x hx y hy hh
    have hneg : (-coordinate j) (c x) < (-coordinate j) (c y) := neg_lt_neg hh
    obtain ⟨z,hz,hr,hf⟩ := himprove F hF (-coordinate j) x hx y hy hneg
    refine ⟨z,hz,hr,?_⟩
    change -c x j < -c z j at hf
    linarith
  have hup : ∀ F, Face F → ∀ j x, x ∈ F → ∀ y, y ∈ F →
      c x j < c y j → ∃ z ∈ F, R x z ∧ c x j < c z j := by
    intro F hF j x hx y hy hh
    exact himprove F hF (coordinate j) x hx y hy hh
  have himage : Finset.univ.image c=V := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact (E.symm i).property
    · intro hx
      refine Finset.mem_image.mpr ⟨E ⟨x,hx⟩,Finset.mem_univ _,?_⟩
      change (E.symm (E ⟨x,hx⟩)).val=x
      rw [E.symm_apply_apply]
  have hFace : Face Finset.univ := by
    change IsExtreme ℝ P (convexHull ℝ (Finset.univ.image c : Set (Fin d → ℝ)))
    rw [himage,vertex_hull C]
  have huV : u ∈ V := Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset hu,hu⟩
  have hvV : v ∈ V := Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset hv,hv⟩
  let i := E ⟨u,huV⟩
  let j := E ⟨v,hvV⟩
  have hci : c i=u := by change (E.symm (E ⟨u,huV⟩)).val=u; rw [E.symm_apply_apply]
  have hcj : c j=v := by change (E.symm (E ⟨v,hvV⟩)).val=v; rw [E.symm_apply_apply]
  obtain ⟨L,hL,p,hp0,hpL,hpm,hpe⟩ := finite_coordinate_route_bound
    (Fintype.card V) d R hsym c hc Face hminface hmaxface hdown hup
    Finset.univ hFace i j (Finset.mem_univ _) (Finset.mem_univ _)
  have hlevels : ∀ k : Fin d,
      Finset.univ.image (fun a => c a k)=V.image (fun x => x k) := by
    intro k
    simpa only [Finset.image_image] using
      congrArg (fun S : Finset (Fin d → ℝ) => S.image (fun x => x k)) himage
  refine ⟨L,?_,fun t => c (p t.val),?_,?_,?_,?_⟩
  · simpa only [hlevels] using hL
  · change c (p 0)=u
    rw [hp0,hci]
  · change c (p L)=v
    rw [hpL,hcj]
  · intro t
    exact hvertices _
  · intro t
    exact hpe t.val t.isLt

/-- A concrete polynomial class consequence: every hull of arbitrary 0/1
points has original ordinary-edge routes of length at most the ambient d. -/
theorem zero_one_routes (C : Finset (Fin d → ℝ))
    (h01 : ∀ x ∈ C, ∀ j : Fin d, x j=0 ∨ x j=1) (u v : Fin d → ℝ)
    (hu : u ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ)
    (hv : v ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) :
    ∃ L : ℕ, L ≤ d ∧ ∃ p : Fin (L+1) → (Fin d → ℝ),
      p 0=u ∧ p (Fin.last L)=v ∧
      (∀ i, p i ∈ (convexHull ℝ (C : Set (Fin d → ℝ))).extremePoints ℝ) ∧
      ∀ i : Fin L, p i.castSucc ≠ p i.succ ∧
        IsExtreme ℝ (convexHull ℝ (C : Set (Fin d → ℝ)))
          (segment ℝ (p i.castSucc) (p i.succ)) := by
  classical
  obtain ⟨L,hL,p,hp⟩ := original_routes C u v hu hv
  refine ⟨L,?_,p,hp⟩
  apply hL.trans
  calc
    (∑ j : Fin d, (((vertices C).image (fun x => x j)).card-1))
        ≤ ∑ _j : Fin d, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      have hs : (vertices C).image (fun x => x j) ⊆ ({0,1} : Finset ℝ) := by
        intro t ht
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
        have h := h01 x (Finset.mem_filter.mp hx).1 j
        simpa only [Finset.mem_insert,Finset.mem_singleton] using h
      have hc := Finset.card_le_card hs
      have hc2 : ((vertices C).image (fun x => x j)).card ≤ 2 := by simpa using hc
      omega
    _ = d := by simp

end Hirsch.HullCoordinate

namespace Hirsch.AffineRoofs

open Set

variable {n k : ℕ}

/-- The height of a fiber is an original affine expression in base coordinates. -/
def height (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (j : Fin k) (x : Fin n → ℝ) : ℝ := c j + A j x

/-- This is the ORIGINAL body, not an auxiliary projection or completion. -/
def body (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ) :
    Set ((Fin n → ℝ) × (Fin k → ℝ)) :=
  {z | z.1 ∈ P ∧ ∀ j, 0 ≤ z.2 j ∧ z.2 j ≤ height A c j z.1}

def sectionPoint (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (s : Fin k → ℝ) (x : Fin n → ℝ) : (Fin n → ℝ) × (Fin k → ℝ) :=
  (x, fun j => s j * height A c j x)

def bit (b : Bool) : ℝ := if b then 1 else 0

def corner (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (b : Fin k → Bool) (x : Fin n → ℝ) : (Fin n → ℝ) × (Fin k → ℝ) :=
  sectionPoint A c (fun j => bit (b j)) x

lemma bit_bounds (b : Bool) : 0 ≤ bit b ∧ bit b ≤ 1 := by
  cases b <;> norm_num [bit]

lemma height_mix (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (j : Fin k) (x y : Fin n → ℝ) (a b : ℝ) (hab : a+b=1) :
    height A c j (a • x+b • y)=a*height A c j x+b*height A c j y := by
  simp only [height,map_add,map_smul,smul_eq_mul]
  calc
    c j+(a*A j x+b*A j y) = (a+b)*c j+a*A j x+b*A j y := by rw [hab]; ring
    _ = a*(c j+A j x)+b*(c j+A j y) := by ring

lemma section_mix (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (s : Fin k → ℝ) (x y : Fin n → ℝ) (a b : ℝ) (hab : a+b=1) :
    sectionPoint A c s (a • x+b • y)=a • sectionPoint A c s x+b • sectionPoint A c s y := by
  apply Prod.ext
  · rfl
  · funext j
    change s j*height A c j (a • x+b • y)=
      a*(s j*height A c j x)+b*(s j*height A c j y)
    rw [height_mix A c j x y a b hab]
    ring

lemma section_mem (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x)
    (s : Fin k → ℝ) (hs : ∀ j, 0 ≤ s j ∧ s j ≤ 1)
    (x : Fin n → ℝ) (hx : x ∈ P) : sectionPoint A c s x ∈ body P A c := by
  refine ⟨hx,?_⟩
  intro j
  refine ⟨mul_nonneg (hs j).1 (hpos x hx j).le,?_⟩
  exact (mul_le_mul_of_nonneg_right (hs j).2 (hpos x hx j).le).trans_eq (one_mul _)

lemma corner_mem (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x)
    (b : Fin k → Bool) (x : Fin n → ℝ) (hx : x ∈ P) :
    corner A c b x ∈ body P A c :=
  section_mem P A c hpos (fun j => bit (b j)) (fun j => bit_bounds _) x hx

lemma body_convex (P : Set (Fin n → ℝ)) (hP : Convex ℝ P)
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ) : Convex ℝ (body P A c) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hP hx.1 hy.1 ha hb hab,?_⟩
  intro j
  change 0 ≤ a*x.2 j+b*y.2 j ∧ a*x.2 j+b*y.2 j ≤ height A c j (a • x.1+b • y.1)
  rw [height_mix A c j x.1 y.1 a b hab]
  exact ⟨add_nonneg (mul_nonneg ha (hx.2 j).1) (mul_nonneg hb (hy.2 j).1),
    add_le_add (mul_le_mul_of_nonneg_left (hx.2 j).2 ha)
      (mul_le_mul_of_nonneg_left (hy.2 j).2 hb)⟩

lemma zero_of_positive_mix (a b s t : ℝ) (ha : 0<a) (hb : 0 ≤ b)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (he : a*s+b*t=0) : s=0 := by
  have hp := mul_nonneg ha.le hs
  have hq := mul_nonneg hb ht
  have haz : a*s=0 := by linarith
  exact (mul_eq_zero.mp haz).resolve_left (ne_of_gt ha)

/-- Every actual extreme point projects to an actual BASE extreme point. -/
lemma extreme_base (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x)
    (z : (Fin n → ℝ) × (Fin k → ℝ)) (hz : z ∈ (body P A c).extremePoints ℝ) :
    z.1 ∈ P.extremePoints ℝ := by
  let s : Fin k → ℝ := fun j => z.2 j / height A c j z.1
  have hs : ∀ j, 0 ≤ s j ∧ s j ≤ 1 := by
    intro j
    exact ⟨div_nonneg (hz.1.2 j).1 (hpos z.1 hz.1.1 j).le,
      (div_le_one (hpos z.1 hz.1.1 j)).mpr (hz.1.2 j).2⟩
  have hsz : sectionPoint A c s z.1=z := by
    apply Prod.ext
    · rfl
    funext j
    exact div_mul_cancel₀ _ (ne_of_gt (hpos z.1 hz.1.1 j))
  refine ⟨hz.1.1,?_⟩
  intro x hx y hy hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hzseg : z ∈ openSegment ℝ (sectionPoint A c s x) (sectionPoint A c s y) := by
    refine ⟨a,b,ha,hb,hab,?_⟩
    rw [← section_mix A c s x y a b hab,he,hsz]
  have heq := hz.2 (section_mem P A c hpos s hs x hx)
    (section_mem P A c hpos s hs y hy) hzseg
  exact congrArg Prod.fst heq

/-- Each fiber coordinate of an actual vertex is on its own original boundary. -/
lemma extreme_fiber (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x)
    (z : (Fin n → ℝ) × (Fin k → ℝ)) (hz : z ∈ (body P A c).extremePoints ℝ)
    (j : Fin k) : z.2 j=0 ∨ z.2 j=height A c j z.1 := by
  classical
  by_cases hz0 : z.2 j=0
  · exact Or.inl hz0
  right
  by_contra hzH
  have hH := hpos z.1 hz.1.1 j
  have ht0 : 0<z.2 j := lt_of_le_of_ne (hz.1.2 j).1 (Ne.symm hz0)
  have htH : z.2 j<height A c j z.1 := lt_of_le_of_ne (hz.1.2 j).2 hzH
  let a := (z.1,Function.update z.2 j 0)
  let b := (z.1,Function.update z.2 j (height A c j z.1))
  have ha : a ∈ body P A c := by
    refine ⟨hz.1.1,?_⟩
    intro i
    by_cases hi : i=j
    · subst i
      simpa only [a,Function.update_self] using (show 0 ≤ (0:ℝ) ∧ 0 ≤ height A c j z.1 from ⟨le_rfl,hH.le⟩)
    · simpa only [a,Function.update_of_ne hi] using hz.1.2 i
  have hb : b ∈ body P A c := by
    refine ⟨hz.1.1,?_⟩
    intro i
    by_cases hi : i=j
    · subst i
      simpa only [b,Function.update_self] using (show 0 ≤ height A c j z.1 ∧ height A c j z.1 ≤ height A c j z.1 from ⟨hH.le,le_rfl⟩)
    · simpa only [b,Function.update_of_ne hi] using hz.1.2 i
  let t := z.2 j / height A c j z.1
  have ht : 0<t ∧ t<1 := ⟨div_pos ht0 hH,(div_lt_one hH).mpr htH⟩
  have hprod : t*height A c j z.1=z.2 j := div_mul_cancel₀ _ (ne_of_gt hH)
  have heq : (1-t) • a+t • b=z := by
    apply Prod.ext
    · change (1-t) • z.1+t • z.1=z.1
      module
    · funext i
      by_cases hi : i=j
      · subst i
        change (1-t)*Function.update z.2 j 0 j+t*Function.update z.2 j (height A c j z.1) j=z.2 j
        simp only [Function.update_self,mul_zero,zero_add,hprod]
      · change (1-t)*Function.update z.2 j 0 i+t*Function.update z.2 j (height A c j z.1) i=z.2 i
        rw [Function.update_of_ne hi,Function.update_of_ne hi]
        ring
  have haz := hz.2 ha hb ⟨1-t,t,sub_pos.mpr ht.2,ht.1,by ring,heq⟩
  have he := congrArg (fun p : (Fin n → ℝ) × (Fin k → ℝ) => p.2 j) haz
  change Function.update z.2 j 0 j=z.2 j at he
  rw [Function.update_self] at he
  exact hz0 he.symm

/-- This classification is derived from Mathlib extremality; no vertex catalogue is assumed. -/
theorem extreme_classification (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x)
    (z : (Fin n → ℝ) × (Fin k → ℝ)) (hz : z ∈ (body P A c).extremePoints ℝ) :
    z.1 ∈ P.extremePoints ℝ ∧ ∃ b : Fin k → Bool, corner A c b z.1=z := by
  classical
  refine ⟨extreme_base P A c hpos z hz,?_,?_⟩
  · exact fun j => if z.2 j=0 then false else true
  · apply Prod.ext
    · rfl
    funext j
    by_cases hj : z.2 j=0
    · simp [corner,sectionPoint,bit,hj]
    · have he : z.2 j=height A c j z.1 := (extreme_fiber P A c hpos z hz j).resolve_left hj
      simp [corner,sectionPoint,bit,hj,he]

/-- Boundary equality in a positive convex combination fixes that boundary
at each endpoint, even when the two roof heights differ. -/
lemma boundary_mix (b : Bool) (a t U V y z : ℝ)
    (ha : 0<a) (ht : 0 ≤ t) (hy : 0 ≤ y ∧ y ≤ U) (hz : 0 ≤ z ∧ z ≤ V)
    (he : a*y+t*z=bit b*(a*U+t*V)) : y=bit b*U := by
  cases b with
  | false =>
    simp only [bit, Bool.false_eq_true, if_false, zero_mul] at he ⊢
    exact zero_of_positive_mix a t y z ha ht hy.1 hz.1 he
  | true =>
    simp only [bit, if_true, one_mul] at he ⊢
    have hs : a*(U-y)+t*(V-z)=0 := by nlinarith [he]
    have hh := zero_of_positive_mix a t (U-y) (V-z) ha ht
      (sub_nonneg.mpr hy.2) (sub_nonneg.mpr hz.2) hs
    exact (sub_eq_zero.mp hh).symm

/-- A full fixed-boundary lift of an original extreme set remains extreme. -/
theorem lift_extreme (P F : Set (Fin n → ℝ)) (hF : IsExtreme ℝ P F)
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x) (bits : Fin k → Bool) :
    IsExtreme ℝ (body P A c) (corner A c bits '' F) := by
  refine ⟨?_,?_⟩
  · rintro z ⟨x,hx,rfl⟩
    exact corner_mem P A c hpos bits x (hF.subset hx)
  · intro u hu v hv z hz hseg
    obtain ⟨x,hx,rfl⟩ := hz
    obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
    have hebase : a • u.1+b • v.1=x := congrArg Prod.fst he
    have hubase : u.1 ∈ F := hF.2 hu.1 hv.1 hx ⟨a,b,ha,hb,hab,hebase⟩
    refine ⟨u.1,hubase,?_⟩
    apply Prod.ext
    · rfl
    funext j
    have hj : a*u.2 j+b*v.2 j=bit (bits j)*height A c j x :=
      congrArg (fun p : (Fin n → ℝ) × (Fin k → ℝ) => p.2 j) he
    rw [← hebase,height_mix A c j u.1 v.1 a b hab] at hj
    exact (boundary_mix (bits j) a b _ _ _ _ ha hb.le (hu.2 j) (hv.2 j) hj).symm

lemma corner_extreme (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x)
    (bits : Fin k → Bool) (x : Fin n → ℝ) (hx : x ∈ P.extremePoints ℝ) :
    corner A c bits x ∈ (body P A c).extremePoints ℝ := by
  have h := lift_extreme P {x} (isExtreme_singleton.mpr hx) A c hpos bits
  rw [Set.image_singleton] at h
  exact h.mem_extremePoints

lemma corner_segment (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (bits : Fin k → Bool) (x y : Fin n → ℝ) :
    corner A c bits '' segment ℝ x y = segment ℝ (corner A c bits x) (corner A c bits y) := by
  ext z
  constructor
  · rintro ⟨w,⟨a,b,ha,hb,hab,he⟩,rfl⟩
    refine ⟨a,b,ha,hb,hab,?_⟩
    change a • sectionPoint A c (fun j => bit (bits j)) x+
      b • sectionPoint A c (fun j => bit (bits j)) y=sectionPoint A c (fun j => bit (bits j)) w
    rw [← section_mix A c (fun j => bit (bits j)) x y a b hab,he]
  · rintro ⟨a,b,ha,hb,hab,he⟩
    refine ⟨a • x+b • y,⟨a,b,ha,hb,hab,rfl⟩,?_⟩
    exact (section_mix A c (fun j => bit (bits j)) x y a b hab).trans he

lemma horizontal_edge (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x)
    (bits : Fin k → Bool) (x y : Fin n → ℝ) (hne : x≠y)
    (he : IsExtreme ℝ P (segment ℝ x y)) :
    corner A c bits x ≠ corner A c bits y ∧
      IsExtreme ℝ (body P A c) (segment ℝ (corner A c bits x) (corner A c bits y)) := by
  refine ⟨fun h => hne (congrArg Prod.fst h),?_⟩
  rw [← corner_segment]
  exact lift_extreme P _ he A c hpos bits

/-- The fiber over an actual base vertex is extreme in the original body. -/
lemma fiber_extreme (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ P.extremePoints ℝ) :
    IsExtreme ℝ (body P A c) {z | z ∈ body P A c ∧ z.1=x} := by
  refine ⟨fun z hz => hz.1,?_⟩
  intro u hu v hv z hz hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  refine ⟨hu,?_⟩
  have hbase : a • u.1+b • v.1=x := (congrArg Prod.fst he).trans hz.2
  exact hx.2 hu.1 hv.1 ⟨a,b,ha,hb,hab,hbase⟩

/-- A nondegenerate whole coordinate edge of a positive box is extreme. -/
lemma box_edge (H : Fin k → ℝ) (hH : ∀ j, 0<H j)
    (bits : Fin k → Bool) (q : Fin k) :
    let a := fun j => bit (Function.update bits q false j)*H j
    let b := fun j => bit (Function.update bits q true j)*H j
    a ≠ b ∧ IsExtreme ℝ {y : Fin k → ℝ | ∀ j, 0 ≤ y j ∧ y j ≤ H j} (segment ℝ a b) := by
  classical
  let a := fun j => bit (Function.update bits q false j)*H j
  let b := fun j => bit (Function.update bits q true j)*H j
  have hbnd : ∀ (s : Fin k → Bool) j, 0 ≤ bit (s j)*H j ∧ bit (s j)*H j ≤ H j := by
    intro s j
    exact ⟨mul_nonneg (bit_bounds _).1 (hH j).le,
      (mul_le_mul_of_nonneg_right (bit_bounds _).2 (hH j).le).trans_eq (one_mul _)⟩
  have ha : ∀ j, 0 ≤ a j ∧ a j ≤ H j := hbnd _
  have hb : ∀ j, 0 ≤ b j ∧ b j ≤ H j := hbnd _
  have haq : a q=0 := by simp [a,bit]
  have hbq : b q=H q := by simp [b,bit]
  have hne : a≠b := by
    intro he
    have ht := congrFun he q
    rw [haq,hbq] at ht
    exact (ne_of_gt (hH q)) ht.symm
  refine ⟨hne,⟨?_,?_⟩⟩
  · rintro z ⟨s,t,hs,ht,hst,he⟩ j
    have hej : s*a j+t*b j=z j := congrFun he j
    rw [← hej]
    refine ⟨add_nonneg (mul_nonneg hs (ha j).1) (mul_nonneg ht (hb j).1),?_⟩
    calc
      s*a j+t*b j ≤ s*H j+t*H j := add_le_add
        (mul_le_mul_of_nonneg_left (ha j).2 hs) (mul_le_mul_of_nonneg_left (hb j).2 ht)
      _ = H j := by rw [← add_mul,hst,one_mul]
  · intro u hu v hv z hz hseg
    obtain ⟨s,t,hs,ht,hst,he⟩ := hz
    obtain ⟨r,l,hr,hl,hrl,hmix⟩ := hseg
    have hfixed : ∀ j, j≠q → u j=bit (bits j)*H j := by
      intro j hj
      have hej := congrFun he j
      have haz : a j=bit (bits j)*H j := by simp only [a,Function.update_of_ne hj]
      have hbz : b j=bit (bits j)*H j := by simp only [b,Function.update_of_ne hj]
      have hzj : z j=bit (bits j)*H j := by
        change s*a j+t*b j=z j at hej
        rw [haz,hbz,← add_mul,hst,one_mul] at hej
        exact hej.symm
      have humix : r*u j+l*v j=bit (bits j)*(r*H j+l*H j) := by
        have hh := congrFun hmix j
        change r*u j+l*v j=z j at hh
        rw [hzj] at hh
        simpa only [← add_mul,hrl,one_mul] using hh
      exact boundary_mix (bits j) r l _ _ _ _ hr hl.le (hu j) (hv j) humix
    let t' := u q/H q
    have ht' : 0 ≤ t' ∧ t' ≤ 1 := ⟨div_nonneg (hu q).1 (hH q).le,(div_le_one (hH q)).mpr (hu q).2⟩
    have htprod : t'*H q=u q := div_mul_cancel₀ _ (ne_of_gt (hH q))
    refine ⟨1-t',t',sub_nonneg.mpr ht'.2,ht'.1,by ring,?_⟩
    funext j
    change (1-t')*a j+t'*b j=u j
    by_cases hj : j=q
    · subst j
      rw [haq,hbq,mul_zero,zero_add,htprod]
    · rw [hfixed j hj]
      simp only [a,b,Function.update_of_ne hj]
      ring

/-- Affine injection of a fixed fiber preserves its whole extreme segments. -/
lemma fixed_base_extreme (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ P.extremePoints ℝ)
    (a b : Fin k → ℝ)
    (he : IsExtreme ℝ {y : Fin k → ℝ | ∀ j,0 ≤ y j ∧ y j ≤ height A c j x} (segment ℝ a b)) :
    IsExtreme ℝ (body P A c) (segment ℝ (x,a) (x,b)) := by
  have hf := fiber_extreme P A c x hx
  apply hf.trans
  refine ⟨?_,?_⟩
  · rintro z ⟨s,t,hs,ht,hst,heq⟩
    have hzbase : z.1=x := by
      have h := congrArg Prod.fst heq
      change s • x+t • x=z.1 at h
      rw [← add_smul,hst,one_smul] at h
      exact h.symm
    have hzfiber : z.2 ∈ segment ℝ a b := ⟨s,t,hs,ht,hst,congrArg Prod.snd heq⟩
    exact ⟨⟨hzbase.symm ▸ hx.1,by simpa only [hzbase] using he.subset hzfiber⟩,hzbase⟩
  · intro u hu v hv z hz hseg
    obtain ⟨s,t,hs,ht,hst,heq⟩ := hz
    obtain ⟨r,l,hr,hl,hrl,hmix⟩ := hseg
    have huz : u.2 ∈ segment ℝ a b := he.2
      (by simpa only [hu.2] using hu.1.2) (by simpa only [hv.2] using hv.1.2)
      ⟨s,t,hs,ht,hst,congrArg Prod.snd heq⟩
      ⟨r,l,hr,hl,hrl,congrArg Prod.snd hmix⟩
    obtain ⟨s',t',hs',ht',hst',hfib⟩ := huz
    refine ⟨s',t',hs',ht',hst',?_⟩
    apply Prod.ext
    · change s' • x+t' • x=u.1
      rw [← add_smul,hst',one_smul,hu.2]
    · exact hfib

lemma vertical_edge (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0 < height A c j x)
    (x : Fin n → ℝ) (hx : x ∈ P.extremePoints ℝ)
    (bits : Fin k → Bool) (q : Fin k) :
    corner A c (Function.update bits q false) x ≠ corner A c (Function.update bits q true) x ∧
      IsExtreme ℝ (body P A c)
        (segment ℝ (corner A c (Function.update bits q false) x)
          (corner A c (Function.update bits q true) x)) := by
  obtain ⟨hne,he⟩ := box_edge (fun j => height A c j x) (hpos x hx.1) bits q
  exact ⟨fun h => hne (congrArg Prod.snd h),fixed_base_extreme P A c x hx _ _ he⟩

end Hirsch.AffineRoofs
namespace Hirsch.AffineRoofs

open Set

variable {n k : ℕ}

noncomputable def allCorners (C : Finset (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ) :
    Finset ((Fin n → ℝ) × (Fin k → ℝ)) := by
  classical
  exact ((HullCoordinate.vertices C).product (Finset.univ : Finset (Fin k → Bool))).image
    (fun t => corner A c t.2 t.1)

def Edge (Q : Set ((Fin n → ℝ) × (Fin k → ℝ)))
    (u v : (Fin n → ℝ) × (Fin k → ℝ)) : Prop :=
  u≠v ∧ IsExtreme ℝ Q (segment ℝ u v)

lemma corner_member (C : Finset (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ (convexHull ℝ (C : Set (Fin n → ℝ))).extremePoints ℝ)
    (b : Fin k → Bool) : corner A c b x ∈ allCorners C A c := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(x,b),Finset.mem_product.mpr ⟨?_,Finset.mem_univ _⟩,rfl⟩
  exact Finset.mem_filter.mpr ⟨extremePoints_convexHull_subset hx,hx⟩

lemma allCorners_extreme (C : Finset (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ convexHull ℝ (C : Set (Fin n → ℝ)), ∀ j, 0<height A c j x)
    (z : (Fin n → ℝ) × (Fin k → ℝ)) (hz : z ∈ allCorners C A c) :
    z ∈ (body (convexHull ℝ (C : Set (Fin n → ℝ))) A c).extremePoints ℝ := by
  classical
  obtain ⟨⟨x,b⟩,hm,rfl⟩ := Finset.mem_image.mp hz
  have hx := (Finset.mem_filter.mp (Finset.mem_product.mp hm).1).2
  exact corner_extreme _ A c hpos b x hx

lemma vertical_change (P : Set (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ P, ∀ j, 0<height A c j x)
    (x : Fin n → ℝ) (hx : x ∈ P.extremePoints ℝ)
    (bits : Fin k → Bool) (q : Fin k) (t : Bool) (hne : bits q≠t) :
    Edge (body P A c) (corner A c bits x) (corner A c (Function.update bits q t) x) := by
  classical
  have hself : Function.update bits q (bits q)=bits := by
    funext j
    by_cases hj : j=q
    · subst j
      rw [Function.update_self]
    · rw [Function.update_of_ne hj]
  have h := vertical_edge P A c hpos x hx bits q
  cases hb : bits q with
  | false =>
    cases t with
    | false => exact False.elim (hne hb)
    | true =>
      rw [hb] at hself
      simpa only [hself] using h
  | true =>
    cases t with
    | true => exact False.elim (hne hb)
    | false =>
      rw [hb] at hself
      rw [hself] at h
      exact ⟨Ne.symm h.1,by rw [segment_symm]; exact h.2⟩

/-- Change only differing roof bits, using at most k genuine original edges. -/
theorem fiber_route (C : Finset (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ convexHull ℝ (C : Set (Fin n → ℝ)), ∀ j, 0<height A c j x)
    (x : Fin n → ℝ) (hx : x ∈ (convexHull ℝ (C : Set (Fin n → ℝ))).extremePoints ℝ)
    (a b : Fin k → Bool) :
    ∃ p : CoordinateRoute.Route
      (Edge (body (convexHull ℝ (C : Set (Fin n → ℝ))) A c))
      (allCorners C A c) (corner A c a x) (corner A c b x), p.length ≤ k := by
  classical
  let diff := fun a : Fin k → Bool => Finset.univ.filter (fun j => a j≠b j)
  have aux : ∀ r : ℕ, ∀ a : Fin k → Bool, (diff a).card=r →
      ∃ p : CoordinateRoute.Route
        (Edge (body (convexHull ℝ (C : Set (Fin n → ℝ))) A c))
        (allCorners C A c) (corner A c a x) (corner A c b x), p.length ≤ (diff a).card := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro a har
      by_cases he : a=b
      · subst a
        exact ⟨CoordinateRoute.Route.nil (corner_member C A c x hx b),by simp [CoordinateRoute.Route.nil]⟩
      have hex : ∃ q, a q≠b q := by
        by_contra hn
        apply he
        funext q
        by_contra hq
        exact hn ⟨q,hq⟩
      obtain ⟨q,hq⟩ := hex
      let a' := Function.update a q (b q)
      have hsub : diff a' ⊆ diff a := by
        intro j hj
        have hneq := (Finset.mem_filter.mp hj).2
        have hjq : j≠q := by
          intro hh
          subst j
          exact hneq (Function.update_self _ _ _)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,by simpa only [a',Function.update_of_ne hjq] using hneq⟩
      have hstrict : diff a' ⊂ diff a := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
        intro hh
        have hm : q ∈ diff a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩
        rw [← hh] at hm
        exact (Finset.mem_filter.mp hm).2 (Function.update_self _ _ _)
      have hcard := Finset.card_lt_card hstrict
      obtain ⟨p,hp⟩ := ih (diff a').card (by omega) a' rfl
      refine ⟨CoordinateRoute.Route.prepend (corner_member C A c x hx a)
        (vertical_change _ A c hpos x hx a q (b q) hq) p,?_⟩
      change p.length+1 ≤ (diff a).card
      omega
  obtain ⟨p,hp⟩ := aux (diff a).card a rfl
  refine ⟨p,hp.trans ?_⟩
  simpa only [Finset.card_univ,Fintype.card_fin] using
    Finset.card_le_card (Finset.filter_subset (fun j => a j≠b j) Finset.univ)

/-- Every finite base walk lifts along the target's fixed roof boundaries. -/
lemma lift_walk (C : Finset (Fin n → ℝ))
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ convexHull ℝ (C : Set (Fin n → ℝ)), ∀ j, 0<height A c j x)
    (bits : Fin k → Bool) (L : ℕ) (p : Fin (L+1) → (Fin n → ℝ))
    (x y : Fin n → ℝ) (hp0 : p 0=x) (hpL : p (Fin.last L)=y)
    (hm : ∀ i, p i ∈ (convexHull ℝ (C : Set (Fin n → ℝ))).extremePoints ℝ)
    (he : ∀ i : Fin L, p i.castSucc≠p i.succ ∧
      IsExtreme ℝ (convexHull ℝ (C : Set (Fin n → ℝ))) (segment ℝ (p i.castSucc) (p i.succ))) :
    ∃ q : CoordinateRoute.Route
      (Edge (body (convexHull ℝ (C : Set (Fin n → ℝ))) A c))
      (allCorners C A c) (corner A c bits x) (corner A c bits y), q.length=L := by
  let idx : ℕ → Fin (L+1) := fun i => ⟨min i L,Nat.lt_succ_of_le (min_le_right i L)⟩
  have hzero : idx 0=0 := by
    apply Fin.ext
    simp [idx]
  have hlast : idx L=Fin.last L := by
    apply Fin.ext
    simp [idx]
  have hleft : ∀ i : Fin L, idx i.val=i.castSucc := by
    intro i
    apply Fin.ext
    exact min_eq_left i.isLt.le
  have hright : ∀ i : Fin L, idx (i.val+1)=i.succ := by
    intro i
    apply Fin.ext
    exact min_eq_left (Nat.succ_le_of_lt i.isLt)
  refine ⟨{ length := L
            point := fun i => corner A c bits (p (idx i))
            first := by rw [hzero,hp0]
            last := by rw [hlast,hpL]
            mem := fun i _ => corner_member C A c _ (hm (idx i)) bits
            step := ?_ },rfl⟩
  intro i hi
  have h := horizontal_edge _ A c hpos bits _ _ (he ⟨i,hi⟩).1 (he ⟨i,hi⟩).2
  simpa only [← hleft ⟨i,hi⟩,← hright ⟨i,hi⟩] using h

/-- The complete original-edge route; no base route is a public premise. -/
theorem roof_routes (C : Finset (Fin n → ℝ))
    (h01 : ∀ x ∈ C, ∀ j : Fin n, x j=0 ∨ x j=1)
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ convexHull ℝ (C : Set (Fin n → ℝ)), ∀ j, 0<height A c j x)
    (u v : (Fin n → ℝ) × (Fin k → ℝ))
    (hu : u ∈ (body (convexHull ℝ (C : Set (Fin n → ℝ))) A c).extremePoints ℝ)
    (hv : v ∈ (body (convexHull ℝ (C : Set (Fin n → ℝ))) A c).extremePoints ℝ) :
    ∃ L : ℕ, L ≤ n+k ∧ ∃ p : Fin (L+1) → ((Fin n → ℝ) × (Fin k → ℝ)),
      p 0=u ∧ p (Fin.last L)=v ∧
      (∀ i, p i ∈ (body (convexHull ℝ (C : Set (Fin n → ℝ))) A c).extremePoints ℝ) ∧
      ∀ i : Fin L, p i.castSucc≠p i.succ ∧
        IsExtreme ℝ (body (convexHull ℝ (C : Set (Fin n → ℝ))) A c)
          (segment ℝ (p i.castSucc) (p i.succ)) := by
  classical
  obtain ⟨huB,a,ha⟩ := extreme_classification _ A c hpos u hu
  obtain ⟨hvB,b,hb⟩ := extreme_classification _ A c hpos v hv
  obtain ⟨firstLeg,hprefix⟩ := fiber_route C A c hpos u.1 huB a b
  obtain ⟨L,hL,p,hp0,hpL,hpm,hpe⟩ := HullCoordinate.zero_one_routes C h01 u.1 v.1 huB hvB
  obtain ⟨secondLeg,hsuffix⟩ := lift_walk C A c hpos b L p u.1 v.1 hp0 hpL hpm hpe
  let q := firstLeg.append secondLeg
  refine ⟨q.length,?_,fun i => q.point i.val,?_,?_,?_,?_⟩
  · change firstLeg.length+secondLeg.length ≤ n+k
    omega
  · exact q.first.trans ha
  · exact q.last.trans hb
  · intro i
    exact allCorners_extreme C A c hpos _ (q.mem i.val (by have h := i.isLt; omega))
  · intro i
    exact q.step i.val i.isLt

/-- Original row count bounds ambient dimension whenever the H-body has a vertex.
This derives the count; no full rank, active basis or strict interior is supplied. -/
lemma original_row_count {m : ℕ}
    (D : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ ({x | ∀ i, D i x ≤ b i} : Set (Fin n → ℝ)).extremePoints ℝ) :
    n ≤ m := by
  let E : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun z i => D i z
      map_add' := by intro y z; funext i; exact map_add (D i) y z
      map_smul' := by intro a z; funext i; exact map_smul (D i) a z }
  have hker : ∀ z : Fin n → ℝ, (∀ i,D i z=0) → z=0 := by
    intro z hz
    have hp : x+z ∈ ({x | ∀ i,D i x ≤ b i} : Set (Fin n → ℝ)) := by
      intro i
      simpa only [map_add,hz i,add_zero] using hx.1 i
    have hn : x-z ∈ ({x | ∀ i,D i x ≤ b i} : Set (Fin n → ℝ)) := by
      intro i
      simpa only [map_sub,hz i,sub_zero] using hx.1 i
    have he : x+z=x := hx.2 hp hn ⟨(1/2:ℝ),(1/2:ℝ),by norm_num,by norm_num,by norm_num,by module⟩
    have he' : x+z=x+0 := by simpa only [add_zero] using he
    exact add_left_cancel he'
  have hinj : Function.Injective E := by
    intro y z he
    apply sub_eq_zero.mp
    apply hker
    intro i
    have hi : D i y=D i z := congrFun he i
    rw [map_sub,hi,sub_self]
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin] using h

end Hirsch.AffineRoofs

/-- Any number of positive independent affine roofs over a 0/1 base has a linear
ORIGINAL-edge route bound. The number of exceptional levels is unrestricted. -/
theorem solution (n k m : ℕ) (C : Finset (Fin n → ℝ))
    (h01 : ∀ x ∈ C, ∀ j : Fin n, x j=0 ∨ x j=1)
    (D : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hbase : convexHull ℝ (C : Set (Fin n → ℝ))={x | ∀ i,D i x ≤ b i})
    (A : Fin k → (Fin n → ℝ) →ₗ[ℝ] ℝ) (c : Fin k → ℝ)
    (hpos : ∀ x ∈ convexHull ℝ (C : Set (Fin n → ℝ)), ∀ j,0<c j+A j x)
    (u v : (Fin n → ℝ) × (Fin k → ℝ)) :
    let Q : Set ((Fin n → ℝ) × (Fin k → ℝ)) :=
      {z | (∀ i,D i z.1 ≤ b i) ∧ ∀ j,0 ≤ z.2 j ∧ z.2 j ≤ c j+A j z.1}
    u ∈ Q.extremePoints ℝ → v ∈ Q.extremePoints ℝ →
    ∃ L : ℕ, L ≤ n+k ∧ L ≤ m+k ∧
      ∃ p : Fin (L+1) → ((Fin n → ℝ) × (Fin k → ℝ)),
        p 0=u ∧ p (Fin.last L)=v ∧ (∀ i,p i ∈ Q.extremePoints ℝ) ∧
        ∀ i : Fin L, p i.castSucc≠p i.succ ∧
          IsExtreme ℝ Q (segment ℝ (p i.castSucc) (p i.succ)) := by
  dsimp only
  intro hu hv
  let P := convexHull ℝ (C : Set (Fin n → ℝ))
  have hQ : Hirsch.AffineRoofs.body P A c =
      {z : (Fin n → ℝ) × (Fin k → ℝ) |
        (∀ i,D i z.1 ≤ b i) ∧ ∀ j,0 ≤ z.2 j ∧ z.2 j ≤ c j+A j z.1} := by
    simp only [Hirsch.AffineRoofs.body,Hirsch.AffineRoofs.height,P,hbase,Set.mem_setOf_eq]
  have hu' : u ∈ (Hirsch.AffineRoofs.body P A c).extremePoints ℝ := hQ.symm ▸ hu
  have hv' : v ∈ (Hirsch.AffineRoofs.body P A c).extremePoints ℝ := hQ.symm ▸ hv
  have huB := Hirsch.AffineRoofs.extreme_base P A c hpos u hu'
  have huH : u.1 ∈ ({x | ∀ i,D i x ≤ b i} : Set (Fin n → ℝ)).extremePoints ℝ := by
    rw [← hbase]
    exact huB
  have hnm : n ≤ m := Hirsch.AffineRoofs.original_row_count D b u.1 huH
  obtain ⟨L,hL,p,hp0,hpL,hpm,hpe⟩ := Hirsch.AffineRoofs.roof_routes C h01 A c hpos u v hu' hv'
  refine ⟨L,hL,by omega,p,hp0,hpL,?_,?_⟩
  · intro i
    exact hQ ▸ hpm i
  · intro i
    exact ⟨(hpe i).1,hQ ▸ (hpe i).2⟩

#print axioms Hirsch.AffineRoofs.extreme_classification
#print axioms Hirsch.AffineRoofs.lift_extreme
#print axioms Hirsch.AffineRoofs.vertical_edge
#print axioms Hirsch.AffineRoofs.fiber_route
#print axioms Hirsch.AffineRoofs.roof_routes
#print axioms Hirsch.AffineRoofs.original_row_count
#print axioms solution
