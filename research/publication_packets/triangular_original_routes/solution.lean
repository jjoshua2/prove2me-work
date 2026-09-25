import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace TriangularFamily

def tail {n : ℕ} {α : Type*} (x : Fin (n+1) → α) : Fin n → α :=
  fun i => x i.succ

def lead : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | _+1, x => x 0

def branch (e : ℝ) (b : Bool) (x : ℝ) : ℝ :=
  if b then 1-e*x else e*x

def level (e : ℝ) : (n : ℕ) → (Fin n → Bool) → ℝ
  | 0, _ => 0
  | n+1, b => branch e (b 0) (level e n (tail b))

def point (e : ℝ) : (n : ℕ) → (Fin n → Bool) → (Fin n → ℝ)
  | 0, _ => fun i => Fin.elim0 i
  | n+1, b => Fin.cons (level e (n+1) b) (point e n (tail b))

def Feasible (e : ℝ) {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    ∀ (i j : Fin n), i.val+1 = j.val → e*x j ≤ x i ∧ x i ≤ 1-e*x j

private theorem branch_interval (e x : ℝ) (b : Bool)
    (he : 0 < e) (he2 : e < 1/2) (hx : 0 ≤ x ∧ x ≤ 1) :
    e*x ≤ branch e b x ∧ branch e b x ≤ 1-e*x := by
  have hle : e*x ≤ e := by nlinarith [mul_nonneg he.le (sub_nonneg.mpr hx.2)]
  cases b <;> simp [branch] <;> linarith

private theorem level_bounds (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (b : Fin n → Bool), 0 ≤ level e n b ∧ level e n b ≤ 1 := by
  intro n
  induction n with
  | zero => intro b; simp [level]
  | succ n ih =>
    intro b
    have hb := ih (tail b)
    have hz := mul_nonneg he.le hb.1
    have hi := branch_interval e (level e n (tail b)) (b 0) he he2 hb
    change 0 ≤ branch e (b 0) (level e n (tail b)) ∧
      branch e (b 0) (level e n (tail b)) ≤ 1
    constructor <;> linarith

private theorem level_injective (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n, Function.Injective (level e n) := by
  intro n
  induction n with
  | zero =>
    intro a b _
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro a b hab
    have ha := level_bounds e he he2 n (tail a)
    have hb := level_bounds e he he2 n (tail b)
    have hla : e*level e n (tail a) ≤ e :=
      (mul_le_mul_of_nonneg_left ha.2 he.le).trans_eq (mul_one e)
    have hlb : e*level e n (tail b) ≤ e :=
      (mul_le_mul_of_nonneg_left hb.2 he.le).trans_eq (mul_one e)
    have hhead : a 0 = b 0 := by
      cases h0 : a 0 <;> cases h1 : b 0
      · rfl
      · simp [level, branch, h0, h1] at hab
        linarith
      · simp [level, branch, h0, h1] at hab
        linarith
      · rfl
    have hprod : e*level e n (tail a) = e*level e n (tail b) := by
      change branch e (a 0) (level e n (tail a)) =
        branch e (b 0) (level e n (tail b)) at hab
      rw [hhead] at hab
      cases h0 : b 0 <;> simp [branch, h0, ne_of_gt he] at hab <;>
        exact congrArg (fun t : ℝ => e*t) hab
    have ht : tail a = tail b := ih (mul_left_cancel₀ (ne_of_gt he) hprod)
    funext i
    exact Fin.cases hhead (fun j => congrFun ht j) i

private theorem lead_point (e : ℝ) (n : ℕ) (b : Fin n → Bool) :
    lead n (point e n b) = level e n b := by
  cases n <;> rfl

private theorem point_injective (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    (n : ℕ) : Function.Injective (point e n) := by
  intro a b hab
  apply level_injective e he he2 n
  simpa only [lead_point] using congrArg (lead n) hab

private theorem tail_feasible {e : ℝ} {n : ℕ} {x : Fin (n+1) → ℝ}
    (hx : Feasible e x) : Feasible e (tail x) := by
  refine ⟨fun i => hx.1 i.succ, ?_⟩
  intro i j hij
  exact hx.2 i.succ j.succ (by simp only [Fin.val_succ]; omega)

private theorem head_interval {e : ℝ} {n : ℕ} {x : Fin (n+1) → ℝ}
    (hx : Feasible e x) :
    e*lead n (tail x) ≤ x 0 ∧ x 0 ≤ 1-e*lead n (tail x) := by
  cases n with
  | zero => simpa only [lead, mul_zero, sub_zero] using hx.1 0
  | succ n => exact hx.2 0 (0 : Fin (n+1)).succ (by rfl)

private theorem point_feasible (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (b : Fin n → Bool), Feasible e (point e n b) := by
  intro n
  induction n with
  | zero =>
    intro b
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro b
    have ht := ih (tail b)
    constructor
    · intro i
      exact Fin.cases (level_bounds e he he2 (n+1) b) (fun j => ht.1 j) i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases n with
        | zero => have hj := j.isLt; simp only [Fin.val_zero] at hij; omega
        | succ n =>
          have hj : j = (0 : Fin (n+1)).succ := by
            apply Fin.ext
            simpa only [Fin.val_zero, Fin.val_succ, zero_add] using hij.symm
          subst j
          exact branch_interval e (level e (n+1) (tail b)) (b 0) he he2
            (level_bounds e he he2 (n+1) (tail b))
      | succ i =>
        cases j using Fin.cases with
        | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
        | succ j => exact ht.2 i j (by simp only [Fin.val_succ] at hij; omega)

private theorem endpoint_combo (lo hi x y z a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hx : lo ≤ x ∧ x ≤ hi) (hy : lo ≤ y ∧ y ≤ hi)
    (hz : z=lo ∨ z=hi) (heq : a*x+b*y=z) : x=z ∧ y=z := by
  rcases hz with h | h
  · rw [h] at heq ⊢
    have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx.1)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy.1)
    have hs : a*(x-lo)+b*(y-lo)=0 := by
      calc
        a*(x-lo)+b*(y-lo) = (a*x+b*y)-(a+b)*lo := by ring
        _ = 0 := by rw [heq, hab]; ring
    have hax : a*(x-lo)=0 := by linarith
    have hby : b*(y-lo)=0 := by linarith
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left (ne_of_gt ha)),
      sub_eq_zero.mp ((mul_eq_zero.mp hby).resolve_left (ne_of_gt hb))⟩
  · rw [h] at heq ⊢
    have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx.2)
    have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy.2)
    have hs : a*(hi-x)+b*(hi-y)=0 := by
      calc
        a*(hi-x)+b*(hi-y) = (a+b)*hi-(a*x+b*y) := by ring
        _ = 0 := by rw [heq, hab]; ring
    have hax : a*(hi-x)=0 := by linarith
    have hby : b*(hi-y)=0 := by linarith
    exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left (ne_of_gt ha))).symm,
      (sub_eq_zero.mp ((mul_eq_zero.mp hby).resolve_left (ne_of_gt hb))).symm⟩

private theorem point_combo (e : ℝ) :
    ∀ n (bits : Fin n → Bool) (y z : Fin n → ℝ) (a b : ℝ),
      0 < a → 0 < b → a+b=1 → Feasible e y → Feasible e z →
      a • y + b • z = point e n bits →
      y = point e n bits ∧ z = point e n bits := by
  intro n
  induction n with
  | zero =>
    intro bits y z a b _ _ _ _ _ _
    constructor <;> funext i <;> exact Fin.elim0 i
  | succ n ih =>
    intro bits y z a b ha hb hab hy hz heq
    have htail : a • tail y + b • tail z = point e n (tail bits) := by
      funext i
      exact congrFun heq i.succ
    have ht := ih (tail bits) (tail y) (tail z) a b ha hb hab
      (tail_feasible hy) (tail_feasible hz) htail
    have hy0 := head_interval hy
    have hz0 := head_interval hz
    rw [ht.1] at hy0
    rw [ht.2] at hz0
    have hend : (point e (n+1) bits) 0 = e*lead n (point e n (tail bits)) ∨
        (point e (n+1) bits) 0 = 1-e*lead n (point e n (tail bits)) := by
      simp only [lead_point]
      change branch e (bits 0) (level e n (tail bits)) = e*level e n (tail bits) ∨
        branch e (bits 0) (level e n (tail bits)) = 1-e*level e n (tail bits)
      cases h : bits 0 <;> simp [branch, h]
    have h0 : a*y 0+b*z 0 = (point e (n+1) bits) 0 := congrFun heq 0
    have hh := endpoint_combo _ _ _ _ _ _ _ ha hb hab hy0 hz0 hend h0
    constructor
    · funext i
      exact Fin.cases hh.1 (fun j => congrFun ht.1 j) i
    · funext i
      exact Fin.cases hh.2 (fun j => congrFun ht.2 j) i

private theorem point_extreme (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    (n : ℕ) (bits : Fin n → Bool) :
    point e n bits ∈ ({x | Feasible e x} : Set (Fin n → ℝ)).extremePoints ℝ := by
  refine ⟨point_feasible e he he2 n bits, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  exact (point_combo e n bits y z a b ha hb hab hy hz heq).1


/-! New positive route construction. The preceding recursive point and
extremality helpers are reused from the accepted #280 source. -/

private theorem lead_bounds {e : ℝ} {n : ℕ} {x : Fin n → ℝ}
    (hx : Feasible e x) : 0 ≤ lead n x ∧ lead n x ≤ 1 := by
  cases n with
  | zero => simp [lead]
  | succ n => exact hx.1 0

private theorem cons_feasible (e : ℝ) (he : 0 < e) {n : ℕ}
    (x : Fin n → ℝ) (t : ℝ) (hx : Feasible e x)
    (ht : e*lead n x ≤ t ∧ t ≤ 1-e*lead n x) :
    Feasible e (Fin.cons t x) := by
  have hnon := mul_nonneg he.le (lead_bounds hx).1
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => hx.1 j) i
    change 0 ≤ t ∧ t ≤ 1
    constructor <;> linarith [ht.1, ht.2]
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases n with
      | zero => have hj := j.isLt; simp only [Fin.val_zero] at hij; omega
      | succ n =>
        have hj : j = (0 : Fin (n+1)).succ := by
          apply Fin.ext
          simpa only [Fin.val_zero, Fin.val_succ, zero_add] using hij.symm
        subst j
        exact ht
    | succ i =>
      cases j using Fin.cases with
      | zero => simp only [Fin.val_zero, Fin.val_succ] at hij; omega
      | succ j => exact hx.2 i j (by simp only [Fin.val_succ] at hij; omega)

private theorem feasible_combo (e : ℝ) {n : ℕ} (x y : Fin n → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hx : Feasible e x) (hy : Feasible e y) : Feasible e (a • x+b • y) := by
  constructor
  · intro i
    change 0 ≤ a*x i+b*y i ∧ a*x i+b*y i ≤ 1
    refine ⟨add_nonneg (mul_nonneg ha (hx.1 i).1) (mul_nonneg hb (hy.1 i).1), ?_⟩
    have h1 := mul_le_mul_of_nonneg_left (hx.1 i).2 ha
    have h2 := mul_le_mul_of_nonneg_left (hy.1 i).2 hb
    nlinarith
  · intro i j hij
    have h1 := mul_le_mul_of_nonneg_left (hx.2 i j hij).1 ha
    have h2 := mul_le_mul_of_nonneg_left (hy.2 i j hij).1 hb
    have h3 := mul_le_mul_of_nonneg_left (hx.2 i j hij).2 ha
    have h4 := mul_le_mul_of_nonneg_left (hy.2 i j hij).2 hb
    change e*(a*x j+b*y j) ≤ a*x i+b*y i ∧
      a*x i+b*y i ≤ 1-e*(a*x j+b*y j)
    constructor <;> nlinarith

private def lift (e : ℝ) {n : ℕ} (bit : Bool) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (branch e bit (lead n x)) x

private theorem tail_lift (e : ℝ) {n : ℕ} (bit : Bool) (x : Fin n → ℝ) :
    tail (lift e bit x) = x := by
  rfl

private theorem lift_injective (e : ℝ) {n : ℕ} (bit : Bool) :
    Function.Injective (lift e (n := n) bit) := by
  intro x y h
  exact congrArg tail h

private theorem lift_point (e : ℝ) {n : ℕ} (bit : Bool) (bits : Fin n → Bool) :
    lift e bit (point e n bits) = point e (n+1) (Fin.cons bit bits) := by
  change Fin.cons (branch e bit (lead n (point e n bits))) (point e n bits) =
    Fin.cons (branch e bit (level e n bits)) (point e n bits)
  rw [lead_point]

private theorem lead_combo {n : ℕ} (x y : Fin n → ℝ) (a b : ℝ) :
    lead n (a • x+b • y) = a*lead n x+b*lead n y := by
  cases n with
  | zero => simp [lead]
  | succ n => rfl

private theorem branch_combo (e : ℝ) (bit : Bool) (x y a b : ℝ) (hab : a+b=1) :
    branch e bit (a*x+b*y) = a*branch e bit x+b*branch e bit y := by
  cases bit <;> simp [branch] <;> nlinarith

private theorem lift_combo (e : ℝ) {n : ℕ} (bit : Bool) (x y : Fin n → ℝ)
    (a b : ℝ) (hab : a+b=1) :
    lift e bit (a • x+b • y) = a • lift e bit x+b • lift e bit y := by
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  change branch e bit (lead n (a • x+b • y)) =
    a*branch e bit (lead n x)+b*branch e bit (lead n y)
  rw [lead_combo]
  exact branch_combo e bit _ _ a b hab

private theorem lift_feasible (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    {n : ℕ} (bit : Bool) {x : Fin n → ℝ} (hx : Feasible e x) :
    Feasible e (lift e bit x) :=
  cons_feasible e he x _ hx (branch_interval e _ bit he he2 (lead_bounds hx))

private theorem lower_saturation (a b x y l r : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : l ≤ x) (hy : r ≤ y) (heq : a*x+b*y=a*l+b*r) : x=l := by
  have h1 := mul_nonneg ha.le (sub_nonneg.mpr hx)
  have h2 := mul_nonneg hb.le (sub_nonneg.mpr hy)
  have hz : a*(x-l)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt ha))

private theorem lift_extreme (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    {n : ℕ} (bit : Bool) (B : Set (Fin n → ℝ))
    (hB : IsExtreme ℝ {x | Feasible e x} B) :
    IsExtreme ℝ {x | Feasible e x} (lift e bit '' B) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact lift_feasible e he he2 bit (hB.subset hx)
  · intro y hy z hz w hw hseg
    obtain ⟨x,hx,rfl⟩ := hw
    obtain ⟨a,b,ha,hb,hab,hcomb⟩ := hseg
    have ht : a • tail y+b • tail z=x := by
      funext i
      exact congrFun hcomb i.succ
    have hym : tail y ∈ B := hB.left_mem_of_mem_openSegment
      (tail_feasible hy) (tail_feasible hz) hx ⟨a,b,ha,hb,hab,ht⟩
    have hlevels : a*lead n (tail y)+b*lead n (tail z)=lead n x := by
      rw [← lead_combo, ht]
    have h0 : a*y 0+b*z 0=branch e bit (lead n x) := congrFun hcomb 0
    have hsplit : a*y 0+b*z 0 =
        a*branch e bit (lead n (tail y))+b*branch e bit (lead n (tail z)) := by
      rw [h0, ← hlevels, branch_combo e bit _ _ a b hab]
    have hhead : y 0=branch e bit (lead n (tail y)) := by
      have hyI := head_interval hy
      have hzI := head_interval hz
      cases bit with
      | false =>
        exact lower_saturation a b _ _ _ _ ha hb hyI.1 hzI.1 hsplit
      | true =>
        have hneg : -y 0 = -(1-e*lead n (tail y)) :=
          lower_saturation a b (-y 0) (-z 0) _ _ ha hb
            (neg_le_neg hyI.2) (neg_le_neg hzI.2) (by
              change a*y 0+b*z 0=a*(1-e*lead n (tail y))+b*(1-e*lead n (tail z)) at hsplit
              nlinarith)
        change y 0=1-e*lead n (tail y)
        linarith
    refine ⟨tail y,hym,?_⟩
    funext i
    exact Fin.cases hhead.symm (fun j => rfl) i

private theorem image_segment (e : ℝ) {n : ℕ} (bit : Bool) (x y : Fin n → ℝ) :
    lift e bit '' segment ℝ x y = segment ℝ (lift e bit x) (lift e bit y) := by
  ext z
  constructor
  · rintro ⟨w,⟨a,b,ha,hb,hab,hw⟩,rfl⟩
    refine ⟨a,b,ha,hb,hab,?_⟩
    rw [← lift_combo e bit x y a b hab, hw]
  · rintro ⟨a,b,ha,hb,hab,hz⟩
    exact ⟨a • x+b • y,⟨a,b,ha,hb,hab,rfl⟩,(lift_combo e bit x y a b hab).trans hz⟩

private theorem lift_edge (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    {n : ℕ} (bit : Bool) (x y : Fin n → ℝ)
    (hxy : x ≠ y ∧ IsExtreme ℝ {z | Feasible e z} (segment ℝ x y)) :
    lift e bit x ≠ lift e bit y ∧
      IsExtreme ℝ {z | Feasible e z} (segment ℝ (lift e bit x) (lift e bit y)) := by
  refine ⟨fun h => hxy.1 (lift_injective e bit h), ?_⟩
  rw [← image_segment]
  exact lift_extreme e he he2 bit _ hxy.2

private theorem vertical_mem (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    {n : ℕ} (x : Fin n → ℝ) (hx : Feasible e x)
    (z : Fin (n+1) → ℝ) (hz : Feasible e z) (ht : tail z=x) :
    z ∈ segment ℝ (lift e false x) (lift e true x) := by
  let lo := e*lead n x
  let hi := 1-e*lead n x
  have hB := lead_bounds hx
  have hmul := mul_le_mul_of_nonneg_left hB.2 he.le
  have hgap : 0 < hi-lo := by dsimp [lo,hi]; nlinarith
  have hzi := head_interval hz
  rw [ht] at hzi
  change lo ≤ z 0 ∧ z 0 ≤ hi at hzi
  let a := (hi-z 0)/(hi-lo)
  let b := (z 0-lo)/(hi-lo)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hzi.2) hgap.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hzi.1) hgap.le
  have hab : a+b=1 := by
    dsimp [a,b]
    field_simp [ne_of_gt hgap]
    <;> ring
  have h0 : a*lo+b*hi=z 0 := by
    dsimp [a,b]
    field_simp [ne_of_gt hgap]
    <;> ring
  refine ⟨a,b,ha,hb,hab,?_⟩
  funext i
  refine Fin.cases h0 (fun j => ?_) i
  have hh : z j.succ=x j := congrFun ht j
  change a*x j+b*x j=z j.succ
  rw [hh, ← add_mul, hab, one_mul]

private theorem vertical_tail (e : ℝ) {n : ℕ} (x : Fin n → ℝ)
    {z : Fin (n+1) → ℝ}
    (hz : z ∈ segment ℝ (lift e false x) (lift e true x)) : tail z=x := by
  obtain ⟨a,b,ha,hb,hab,hz⟩ := hz
  funext i
  have h : a*x i+b*x i=z i.succ := congrFun hz i.succ
  change z i.succ=x i
  rw [← h, ← add_mul, hab, one_mul]

private theorem vertical_extreme (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ ({z | Feasible e z}).extremePoints ℝ) :
    IsExtreme ℝ {z | Feasible e z} (segment ℝ (lift e false x) (lift e true x)) := by
  refine ⟨?_, ?_⟩
  · rintro z ⟨a,b,ha,hb,hab,hz⟩
    rw [← hz]
    exact feasible_combo e _ _ a b ha hb hab
      (lift_feasible e he he2 false hx.1) (lift_feasible e he he2 true hx.1)
  · intro y hy z hz w hw hseg
    have ht := vertical_tail e x hw
    obtain ⟨a,b,ha,hb,hab,hcomb⟩ := hseg
    have htail : a • tail y+b • tail z=x := by
      rw [← ht]
      funext i
      exact congrFun hcomb i.succ
    have hyx : tail y=x := hx.2 (tail_feasible hy) (tail_feasible hz) ⟨a,b,ha,hb,hab,htail⟩
    exact vertical_mem e he he2 x hx.1 y hy hyx

private theorem vertical_edge (e : ℝ) (he : 0 < e) (he2 : e < 1/2)
    {n : ℕ} (bits : Fin n → Bool) (a b : Bool) (hab : a ≠ b) :
    point e (n+1) (Fin.cons a bits) ≠ point e (n+1) (Fin.cons b bits) ∧
      IsExtreme ℝ {z | Feasible e z}
        (segment ℝ (point e (n+1) (Fin.cons a bits)) (point e (n+1) (Fin.cons b bits))) := by
  have hx := point_extreme e he he2 n bits
  have hd : lift e false (point e n bits) ≠ lift e true (point e n bits) := by
    intro h
    have h0 := congrFun h 0
    change e*lead n (point e n bits) = 1-e*lead n (point e n bits) at h0
    have hm := mul_le_mul_of_nonneg_left (lead_bounds hx.1).2 he.le
    nlinarith
  have hf := vertical_extreme e he he2 (point e n bits) hx
  rw [← lift_point, ← lift_point]
  cases a <;> cases b
  · exact (hab rfl).elim
  · exact ⟨hd,hf⟩
  · exact ⟨Ne.symm hd,by rw [segment_symm]; exact hf⟩
  · exact (hab rfl).elim

private theorem cons_tail {n : ℕ} {α : Type*} (b : Fin (n+1) → α) :
    Fin.cons (b 0) (tail b)=b := by
  funext i
  exact Fin.cases rfl (fun j => rfl) i

/-- Every actual extreme point is one of the recursive choices; not merely
an inclusion of a supplied finite family in the extreme-point set. -/
private theorem extreme_classification (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (x : Fin n → ℝ), x ∈ ({z | Feasible e z}).extremePoints ℝ →
      ∃ bits : Fin n → Bool, point e n bits=x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    refine ⟨fun i => Fin.elim0 i,?_⟩
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro x hx
    have htail := tail_feasible hx.1
    have hclosed := vertical_mem e he he2 (tail x) htail x hx.1 rfl
    have hchoice : ∃ bit : Bool, lift e bit (tail x)=x := by
      by_cases h0 : lift e false (tail x)=x
      · exact ⟨false,h0⟩
      by_cases h1 : lift e true (tail x)=x
      · exact ⟨true,h1⟩
      have hopen := mem_openSegment_of_ne_left_right h0 h1 hclosed
      have hbad := hx.2 (lift_feasible e he he2 false htail)
        (lift_feasible e he he2 true htail) hopen
      exact (h0 hbad).elim
    obtain ⟨bit,hbit⟩ := hchoice
    have htext : tail x ∈ ({z | Feasible e z}).extremePoints ℝ := by
      refine ⟨htail,?_⟩
      intro y hy z hz hseg
      obtain ⟨a,b,ha,hb,hab,hcomb⟩ := hseg
      have hopen : x ∈ openSegment ℝ (lift e bit y) (lift e bit z) := by
        refine ⟨a,b,ha,hb,hab,?_⟩
        rw [← lift_combo e bit y z a b hab,hcomb]
        exact hbit
      have h := hx.2 (lift_feasible e he he2 bit hy) (lift_feasible e he he2 bit hz) hopen
      exact congrArg tail h
    obtain ⟨bits,hbits⟩ := ih (tail x) htext
    refine ⟨Fin.cons bit bits,?_⟩
    rw [← lift_point,hbits]
    exact hbit

private structure Route (e : ℝ) (n : ℕ) (a b : Fin n → Bool) where
  length : ℕ
  bits : ℕ → Fin n → Bool
  first : bits 0=a
  last : bits length=b
  bound : length ≤ n
  steps : ∀ j, j < length → point e n (bits j) ≠ point e n (bits (j+1)) ∧
    IsExtreme ℝ {z | Feasible e z} (segment ℝ (point e n (bits j)) (point e n (bits (j+1))))

private theorem route_exists (e : ℝ) (he : 0 < e) (he2 : e < 1/2) :
    ∀ n (a b : Fin n → Bool), Nonempty (Route e n a b) := by
  intro n
  induction n with
  | zero =>
    intro a b
    refine ⟨{length := 0, bits := fun _ => a, first := rfl,
      last := ?_, bound := le_rfl, steps := ?_}⟩
    · funext i; exact Fin.elim0 i
    · intro j hj; omega
  | succ n ih =>
    intro a b
    obtain ⟨c⟩ := ih (tail a) (tail b)
    have liftstep : ∀ j, j<c.length →
        point e (n+1) (Fin.cons (b 0) (c.bits j)) ≠
          point e (n+1) (Fin.cons (b 0) (c.bits (j+1))) ∧
        IsExtreme ℝ {z | Feasible e z}
          (segment ℝ (point e (n+1) (Fin.cons (b 0) (c.bits j)))
            (point e (n+1) (Fin.cons (b 0) (c.bits (j+1))))) := by
      intro j hj
      rw [← lift_point,← lift_point]
      exact lift_edge e he he2 (b 0) _ _ (c.steps j hj)
    by_cases hab : a 0=b 0
    · refine ⟨{length := c.length, bits := fun j => Fin.cons (b 0) (c.bits j),
        first := ?_, last := ?_, bound := c.bound.trans (Nat.le_succ n), steps := liftstep}⟩
      · rw [c.first,← hab]; exact cons_tail a
      · rw [c.last]; exact cons_tail b
    · refine ⟨{length := c.length+1,
        bits := fun j => Nat.casesOn j a (fun k => Fin.cons (b 0) (c.bits k)),
        first := rfl, last := ?_, bound := Nat.succ_le_succ c.bound, steps := ?_}⟩
      · change Fin.cons (b 0) (c.bits c.length)=b
        rw [c.last]; exact cons_tail b
      · intro j hj
        cases j with
        | zero =>
          change point e (n+1) a ≠ point e (n+1) (Fin.cons (b 0) (c.bits 0)) ∧
            IsExtreme ℝ {z | Feasible e z}
              (segment ℝ (point e (n+1) a) (point e (n+1) (Fin.cons (b 0) (c.bits 0))))
          rw [c.first,← cons_tail a]
          exact vertical_edge e he he2 (tail a) (a 0) (b 0) hab
        | succ j => exact liftstep j (by omega)

end TriangularFamily

/-- Positive ordinary-edge counterpart to the affine-level obstruction:
ALL actual extreme points of the stated triangular polytope are connected
by at most d genuine extreme-segment edges. No vertex list or path is given. -/
theorem solution (e : ℝ) (he : 0 < e) (he2 : e < 1/2) (d : ℕ)
    (u v : Fin d → ℝ)
    (hu : u ∈ ({x : Fin d → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
      ∀ (i j : Fin d), i.val+1=j.val → e*x j ≤ x i ∧ x i ≤ 1-e*x j}).extremePoints ℝ)
    (hv : v ∈ ({x : Fin d → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
      ∀ (i j : Fin d), i.val+1=j.val → e*x j ≤ x i ∧ x i ≤ 1-e*x j}).extremePoints ℝ) :
    ∃ (N : ℕ) (p : ℕ → Fin d → ℝ), N ≤ d ∧ p 0=u ∧ p N=v ∧
      (∀ j, j ≤ N → p j ∈
        ({x : Fin d → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
          ∀ (i k : Fin d), i.val+1=k.val → e*x k ≤ x i ∧ x i ≤ 1-e*x k}).extremePoints ℝ) ∧
      ∀ j, j < N → p j ≠ p (j+1) ∧
        IsExtreme ℝ
          {x : Fin d → ℝ | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
            ∀ (i k : Fin d), i.val+1=k.val → e*x k ≤ x i ∧ x i ≤ 1-e*x k}
          (segment ℝ (p j) (p (j+1))) := by
  obtain ⟨a,ha⟩ := TriangularFamily.extreme_classification e he he2 d u hu
  obtain ⟨b,hb⟩ := TriangularFamily.extreme_classification e he he2 d v hv
  obtain ⟨c⟩ := TriangularFamily.route_exists e he he2 d a b
  refine ⟨c.length,(fun j => TriangularFamily.point e d (c.bits j)),c.bound,?_,?_,?_,?_⟩
  · rw [c.first]; exact ha
  · rw [c.last]; exact hb
  · intro j hj
    exact TriangularFamily.point_extreme e he he2 d (c.bits j)
  · exact c.steps

#print axioms TriangularFamily.lift_extreme
#print axioms TriangularFamily.vertical_extreme
#print axioms TriangularFamily.extreme_classification
#print axioms TriangularFamily.route_exists
#print axioms solution
