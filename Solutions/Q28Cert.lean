import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Solutions.Q28Tables

open scoped RealInnerProductSpace
open Set Classical Hirsch Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-! Finite Q28 certificate data and kernel-checked combinatorial facts.
This module is a local compile cache. The submitted solution concatenates it. -/

def q28AZ : Fin 28 → Fin 5 → ℤ
  | ⟨0, _⟩ => ![18, 0, 0, 0, 1]
  | ⟨1, _⟩ => ![-18, 0, 0, 0, 1]
  | ⟨2, _⟩ => ![0, 0, 30, 0, 1]
  | ⟨3, _⟩ => ![0, 0, -30, 0, 1]
  | ⟨4, _⟩ => ![0, 0, 0, 30, 1]
  | ⟨5, _⟩ => ![0, 0, 0, -30, 1]
  | ⟨6, _⟩ => ![0, 5, 0, 25, 1]
  | ⟨7, _⟩ => ![0, 5, 0, -25, 1]
  | ⟨8, _⟩ => ![0, -5, 0, 25, 1]
  | ⟨9, _⟩ => ![0, -5, 0, -25, 1]
  | ⟨10, _⟩ => ![0, 0, 18, 18, 1]
  | ⟨11, _⟩ => ![0, 0, 18, -18, 1]
  | ⟨12, _⟩ => ![0, 0, -18, 18, 1]
  | ⟨13, _⟩ => ![0, 0, -18, -18, 1]
  | ⟨14, _⟩ => ![0, 0, 18, 0, -1]
  | ⟨15, _⟩ => ![0, 0, -18, 0, -1]
  | ⟨16, _⟩ => ![0, 30, 0, 0, -1]
  | ⟨17, _⟩ => ![0, -30, 0, 0, -1]
  | ⟨18, _⟩ => ![30, 0, 0, 0, -1]
  | ⟨19, _⟩ => ![-30, 0, 0, 0, -1]
  | ⟨20, _⟩ => ![25, 0, 0, 5, -1]
  | ⟨21, _⟩ => ![25, 0, 0, -5, -1]
  | ⟨22, _⟩ => ![-25, 0, 0, 5, -1]
  | ⟨23, _⟩ => ![-25, 0, 0, -5, -1]
  | ⟨24, _⟩ => ![18, 18, 0, 0, -1]
  | ⟨25, _⟩ => ![18, -18, 0, 0, -1]
  | ⟨26, _⟩ => ![-18, 18, 0, 0, -1]
  | _ => ![-18, -18, 0, 0, -1]

def chamberAZ : Fin 14 → Fin 5 → ℤ
  | ⟨0, _⟩ => ![18, 0, 0, 0, 1]
  | ⟨1, _⟩ => ![0, 0, 30, 0, 1]
  | ⟨2, _⟩ => ![0, 0, 0, 30, 1]
  | ⟨3, _⟩ => ![0, 5, 0, 25, 1]
  | ⟨4, _⟩ => ![0, 0, 18, 18, 1]
  | ⟨5, _⟩ => ![0, 0, 18, 0, -1]
  | ⟨6, _⟩ => ![0, 30, 0, 0, -1]
  | ⟨7, _⟩ => ![30, 0, 0, 0, -1]
  | ⟨8, _⟩ => ![25, 0, 0, 5, -1]
  | ⟨9, _⟩ => ![18, 18, 0, 0, -1]
  | ⟨10, _⟩ => ![-1, 0, 0, 0, 0]
  | ⟨11, _⟩ => ![0, -1, 0, 0, 0]
  | ⟨12, _⟩ => ![0, 0, -1, 0, 0]
  | _ => ![0, 0, 0, -1, 0]

def chamberBZ : Fin 14 → ℤ
  | ⟨k, _⟩ => if k < 10 then 1 else 0

def orbitNum : Fin 20 → Fin 5 → ℤ
  | ⟨0, _⟩ => ![0, 0, 0, 0, -1]
  | ⟨1, _⟩ => ![0, 0, 0, 0, 1]
  | ⟨2, _⟩ => ![0, 3, 5, 18, -225]
  | ⟨3, _⟩ => ![2, 3, 2, 3, 0]
  | ⟨4, _⟩ => ![2, 3, 5, 8, -75]
  | ⟨5, _⟩ => ![3, 2, 2, 3, 0]
  | ⟨6, _⟩ => ![3, 2, 5, 3, -30]
  | ⟨7, _⟩ => ![4, 6, 10, 15, -135]
  | ⟨8, _⟩ => ![5, 3, 2, 3, 30]
  | ⟨9, _⟩ => ![5, 8, 3, 2, 75]
  | ⟨10, _⟩ => ![5, 18, 3, 0, 225]
  | ⟨11, _⟩ => ![6, 4, 9, 6, -45]
  | ⟨12, _⟩ => ![6, 9, 15, 10, -90]
  | ⟨13, _⟩ => ![9, 6, 4, 6, 45]
  | ⟨14, _⟩ => ![10, 15, 6, 4, 135]
  | ⟨15, _⟩ => ![15, 10, 9, 6, 90]
  | ⟨16, _⟩ => ![21, 29, 50, 75, -675]
  | ⟨17, _⟩ => ![44, 31, 75, 50, -450]
  | ⟨18, _⟩ => ![50, 75, 29, 21, 675]
  | _ => ![75, 50, 31, 44, 450]

def orbitDen : Fin 20 → ℤ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 315
  | ⟨3, _⟩ => 90
  | ⟨4, _⟩ => 165
  | ⟨5, _⟩ => 90
  | ⟨6, _⟩ => 120
  | ⟨7, _⟩ => 315
  | ⟨8, _⟩ => 120
  | ⟨9, _⟩ => 165
  | ⟨10, _⟩ => 315
  | ⟨11, _⟩ => 225
  | ⟨12, _⟩ => 360
  | ⟨13, _⟩ => 225
  | ⟨14, _⟩ => 315
  | ⟨15, _⟩ => 360
  | ⟨16, _⟩ => 1575
  | ⟨17, _⟩ => 1800
  | ⟨18, _⟩ => 1575
  | _ => 1800


def orbitLevel : Fin 20 → ℕ :=
  ![6, 0, 6, 3, 5, 3, 5, 4, 1, 1, 1, 4, 3, 2, 2, 3, 4, 4, 2, 2]

def quotientEdges : List (ℕ × ℕ) :=
  [(0,2),(0,4),(0,6),(1,8),(1,9),(1,10),(2,2),(2,4),
   (3,3),(3,7),(3,13),(3,18),(4,4),(4,7),(4,16),
   (5,5),(5,11),(5,13),(5,16),(6,6),(6,11),(6,17),
   (7,7),(7,12),(7,16),(8,8),(8,13),(8,19),
   (9,9),(9,10),(9,14),(9,18),(10,10),
   (11,11),(11,15),(11,17),(12,12),(12,14),(12,17),
   (13,13),(13,19),(14,14),(14,15),(14,18),
   (15,15),(15,19),(16,16),(16,17),(17,17),
   (18,18),(18,19),(19,19)]

def QuotientAdj (i j : Fin 20) : Prop :=
  (i.val, j.val) ∈ quotientEdges ∨ (j.val, i.val) ∈ quotientEdges

instance (i j : Fin 20) : Decidable (QuotientAdj i j) :=
  inferInstanceAs (Decidable
    ((i.val, j.val) ∈ quotientEdges ∨ (j.val, i.val) ∈ quotientEdges))

def det3 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : ℤ) : ℤ :=
  a00 * (a11 * a22 - a12 * a21)
  - a01 * (a10 * a22 - a12 * a20)
  + a02 * (a10 * a21 - a11 * a20)

def det5 (M : Fin 5 → Fin 5 → ℤ) : ℤ :=
  let a : Fin 5 → Fin 5 → ℤ := M
  let d4 (r0 r1 r2 r3 : Fin 5) (c0 c1 c2 c3 : Fin 5) : ℤ :=
    let b (i j : Fin 4) : ℤ :=
      a (![r0, r1, r2, r3] i) (![c0, c1, c2, c3] j)
    b 0 0 * det3 (b 1 1) (b 1 2) (b 1 3) (b 2 1) (b 2 2) (b 2 3) (b 3 1) (b 3 2) (b 3 3)
    - b 0 1 * det3 (b 1 0) (b 1 2) (b 1 3) (b 2 0) (b 2 2) (b 2 3) (b 3 0) (b 3 2) (b 3 3)
    + b 0 2 * det3 (b 1 0) (b 1 1) (b 1 3) (b 2 0) (b 2 1) (b 2 3) (b 3 0) (b 3 1) (b 3 3)
    - b 0 3 * det3 (b 1 0) (b 1 1) (b 1 2) (b 2 0) (b 2 1) (b 2 2) (b 3 0) (b 3 1) (b 3 2)
  a 0 0 * d4 1 2 3 4 1 2 3 4
  - a 0 1 * d4 1 2 3 4 0 2 3 4
  + a 0 2 * d4 1 2 3 4 0 1 3 4
  - a 0 3 * d4 1 2 3 4 0 1 2 4
  + a 0 4 * d4 1 2 3 4 0 1 2 3

def matOf (s0 s1 s2 s3 s4 : Fin 14) : Fin 5 → Fin 5 → ℤ :=
  fun i j => chamberAZ (![s0, s1, s2, s3, s4] i) j

def replaceCol (M : Fin 5 → Fin 5 → ℤ) (col : Fin 5) (rhs : Fin 5 → ℤ) :
    Fin 5 → Fin 5 → ℤ :=
  fun i j => if j = col then rhs i else M i j

def intDot5 (row : Fin 5 → ℤ) (x : Fin 5 → ℤ) : ℤ :=
  row 0 * x 0 + row 1 * x 1 + row 2 * x 2 + row 3 * x 3 + row 4 * x 4

def cramerNums (s0 s1 s2 s3 s4 : Fin 14) : Fin 5 → ℤ :=
  let M := matOf s0 s1 s2 s3 s4
  let rhs : Fin 5 → ℤ := fun i => chamberBZ (![s0, s1, s2, s3, s4] i)
  fun j => det5 (replaceCol M j rhs)

def feasibleNums (nums : Fin 5 → ℤ) (d : ℤ) : Bool :=
  decide (∀ i : Fin 14,
    let lhs := intDot5 (chamberAZ i) nums
    if 0 < d then lhs ≤ chamberBZ i * d else chamberBZ i * d ≤ lhs)

def origActiveCount (nums : Fin 5 → ℤ) (d : ℤ) : ℕ :=
  (Finset.univ.filter (fun i : Fin 28 => intDot5 (q28AZ i) nums = d)).card

def matchesOrbit (nums : Fin 5 → ℤ) (d : ℤ) (o : Fin 20) : Bool :=
  decide (∀ j : Fin 5, orbitNum o j * d = nums j * orbitDen o)

def verifyBasis (s0 s1 s2 s3 s4 : Fin 14) : Bool :=
  let d := det5 (matOf s0 s1 s2 s3 s4)
  if d = 0 then true
  else
    let nums := cramerNums s0 s1 s2 s3 s4
    if feasibleNums nums d then
      if origActiveCount nums d < 5 then true
      else decide (∃ o : Fin 20, matchesOrbit nums d o = true)
    else true

/-- Binomial coefficients C(n,k) for n < 14 and k ≤ 5, stored as numerals. -/
def ch (n k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => n
  | 2 =>
    match n with
    | 0 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 10 | 6 => 15
    | 7 => 21 | 8 => 28 | 9 => 36 | 10 => 45 | 11 => 55 | 12 => 66 | _ => 78
  | 3 =>
    match n with
    | 0 | 1 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 10 | 6 => 20 | 7 => 35
    | 8 => 56 | 9 => 84 | 10 => 120 | 11 => 165 | 12 => 220 | _ => 286
  | 4 =>
    match n with
    | 0 | 1 | 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 15 | 7 => 35 | 8 => 70
    | 9 => 126 | 10 => 210 | 11 => 330 | 12 => 495 | _ => 715
  | 5 =>
    match n with
    | 0 | 1 | 2 | 3 | 4 => 0 | 5 => 1 | 6 => 6 | 7 => 21 | 8 => 56
    | 9 => 126 | 10 => 252 | 11 => 462 | 12 => 792 | _ => 1287
  | _ => 0

def combRank (s0 s1 s2 s3 s4 : ℕ) : ℕ :=
  ch s0 1 + ch s1 2 + ch s2 3 + ch s3 4 + ch s4 5

def of14 (n : ℕ) : Fin 14 :=
  ⟨n % 14, Nat.mod_lt n (by decide : (0 : ℕ) < 14)⟩

def of20 (n : ℕ) : Fin 20 :=
  ⟨n % 20, Nat.mod_lt n (by decide : (0 : ℕ) < 20)⟩

def of16 (n : ℕ) : Fin 16 :=
  ⟨n % 16, Nat.mod_lt n (by decide : (0 : ℕ) < 16)⟩

def of28 (n : ℕ) : Fin 28 :=
  ⟨n % 28, Nat.mod_lt n (by decide : (0 : ℕ) < 28)⟩

def certVec (r : ℕ) : Fin 5 → ℤ :=
  fun j => vecAt (5 * r + j.val)

def rowDot (s : Fin 14) (v : Fin 5 → ℤ) : ℤ :=
  intDot5 (chamberAZ s) v

def origCount (v : Fin 5 → ℤ) (d : ℤ) : ℕ :=
  (if intDot5 (q28AZ 0) v = d then 1 else 0) +
  (if intDot5 (q28AZ 1) v = d then 1 else 0) +
  (if intDot5 (q28AZ 2) v = d then 1 else 0) +
  (if intDot5 (q28AZ 3) v = d then 1 else 0) +
  (if intDot5 (q28AZ 4) v = d then 1 else 0) +
  (if intDot5 (q28AZ 5) v = d then 1 else 0) +
  (if intDot5 (q28AZ 6) v = d then 1 else 0) +
  (if intDot5 (q28AZ 7) v = d then 1 else 0) +
  (if intDot5 (q28AZ 8) v = d then 1 else 0) +
  (if intDot5 (q28AZ 9) v = d then 1 else 0) +
  (if intDot5 (q28AZ 10) v = d then 1 else 0) +
  (if intDot5 (q28AZ 11) v = d then 1 else 0) +
  (if intDot5 (q28AZ 12) v = d then 1 else 0) +
  (if intDot5 (q28AZ 13) v = d then 1 else 0) +
  (if intDot5 (q28AZ 14) v = d then 1 else 0) +
  (if intDot5 (q28AZ 15) v = d then 1 else 0) +
  (if intDot5 (q28AZ 16) v = d then 1 else 0) +
  (if intDot5 (q28AZ 17) v = d then 1 else 0) +
  (if intDot5 (q28AZ 18) v = d then 1 else 0) +
  (if intDot5 (q28AZ 19) v = d then 1 else 0) +
  (if intDot5 (q28AZ 20) v = d then 1 else 0) +
  (if intDot5 (q28AZ 21) v = d then 1 else 0) +
  (if intDot5 (q28AZ 22) v = d then 1 else 0) +
  (if intDot5 (q28AZ 23) v = d then 1 else 0) +
  (if intDot5 (q28AZ 24) v = d then 1 else 0) +
  (if intDot5 (q28AZ 25) v = d then 1 else 0) +
  (if intDot5 (q28AZ 26) v = d then 1 else 0) +
  (if intDot5 (q28AZ 27) v = d then 1 else 0)

def violates (s : Fin 14) (v : Fin 5 → ℤ) (d : ℤ) : Bool :=
  let lhs := rowDot s v
  let rhs := chamberBZ s * d
  if 0 < d then decide (rhs < lhs) else decide (lhs < rhs)

def matchesO (v : Fin 5 → ℤ) (d : ℤ) (o : ℕ) : Bool :=
  decide (∀ j : Fin 5, orbitNum (of20 o) j * d = v j * orbitDen (of20 o))

def certOkAt (s0 s1 s2 s3 s4 : Fin 14) : Bool :=
  let r := combRank s0.val s1.val s2.val s3.val s4.val
  let tag := tagAt r
  let v := certVec r
  let d := dAt r
  (tag == 0 || tag == 1 || tag == 2) &&
    if tag == 0 then
      (rowDot s0 v == 0) && (rowDot s1 v == 0) && (rowDot s2 v == 0) &&
        (rowDot s3 v == 0) && (rowDot s4 v == 0) &&
          decide (v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 ∨ v 3 ≠ 0 ∨ v 4 ≠ 0)
    else
      (rowDot s0 v == d * chamberBZ s0) &&
        (rowDot s1 v == d * chamberBZ s1) &&
          (rowDot s2 v == d * chamberBZ s2) &&
            (rowDot s3 v == d * chamberBZ s3) &&
              (rowDot s4 v == d * chamberBZ s4) &&
                decide (d ≠ 0) &&
                  if tag == 2 then
                    matchesO v d (oAt r)
                  else
                    if failKindAt r == 0 then
                      violates (of14 (failRowAt r)) v d
                    else
                      decide (origCount v d < 5)

def pick (k r : ℕ) : ℕ :=
  if ch 13 k ≤ r then 13
  else if ch 12 k ≤ r then 12
  else if ch 11 k ≤ r then 11
  else if ch 10 k ≤ r then 10
  else if ch 9 k ≤ r then 9
  else if ch 8 k ≤ r then 8
  else if ch 7 k ≤ r then 7
  else if ch 6 k ≤ r then 6
  else if ch 5 k ≤ r then 5
  else if ch 4 k ≤ r then 4
  else if ch 3 k ≤ r then 3
  else if ch 2 k ≤ r then 2
  else if ch 1 k ≤ r then 1
  else 0

def unrank5 (r : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  let s4 := pick 5 r
  let r4 := r - ch s4 5
  let s3 := pick 4 r4
  let r3 := r4 - ch s3 4
  let s2 := pick 3 r3
  let r2 := r3 - ch s2 3
  let s1 := pick 2 r2
  let r1 := r2 - ch s1 2
  (pick 1 r1, s1, s2, s3, s4)

def rowDotN (s : ℕ) (v0 v1 v2 v3 v4 : ℤ) : ℤ :=
  match s with
  | 0 => 18 * v0 + v4
  | 1 => 30 * v2 + v4
  | 2 => 30 * v3 + v4
  | 3 => 5 * v1 + 25 * v3 + v4
  | 4 => 18 * v2 + 18 * v3 + v4
  | 5 => 18 * v2 - v4
  | 6 => 30 * v1 - v4
  | 7 => 30 * v0 - v4
  | 8 => 25 * v0 + 5 * v3 - v4
  | 9 => 18 * v0 + 18 * v1 - v4
  | 10 => -v0
  | 11 => -v1
  | 12 => -v2
  | _ => -v3

def bZ (s : ℕ) : ℤ := if s < 10 then 1 else 0

def certOkUnrank (r : ℕ) : Bool :=
  let t := unrank5 r
  let s0 := t.1
  let s1 := t.2.1
  let s2 := t.2.2.1
  let s3 := t.2.2.2.1
  let s4 := t.2.2.2.2
  let tag := tagAt r
  let v0 := vecAt (5 * r)
  let v1 := vecAt (5 * r + 1)
  let v2 := vecAt (5 * r + 2)
  let v3 := vecAt (5 * r + 3)
  let v4 := vecAt (5 * r + 4)
  let d := dAt r
  if tag == 0 then
    (rowDotN s0 v0 v1 v2 v3 v4 == 0) &&
      (rowDotN s1 v0 v1 v2 v3 v4 == 0) &&
        (rowDotN s2 v0 v1 v2 v3 v4 == 0) &&
          (rowDotN s3 v0 v1 v2 v3 v4 == 0) &&
            (rowDotN s4 v0 v1 v2 v3 v4 == 0) &&
              ((v0 != 0) || (v1 != 0) || (v2 != 0) || (v3 != 0) || (v4 != 0))
  else
    (rowDotN s0 v0 v1 v2 v3 v4 == d * bZ s0) &&
      (rowDotN s1 v0 v1 v2 v3 v4 == d * bZ s1) &&
        (rowDotN s2 v0 v1 v2 v3 v4 == d * bZ s2) &&
          (rowDotN s3 v0 v1 v2 v3 v4 == d * bZ s3) &&
            (rowDotN s4 v0 v1 v2 v3 v4 == d * bZ s4) &&
              (d != 0) &&
                if tag == 2 then
                  let o := oAt r
                  (orbitNum (of20 o) 0 * d == v0 * orbitDen (of20 o)) &&
                    (orbitNum (of20 o) 1 * d == v1 * orbitDen (of20 o)) &&
                      (orbitNum (of20 o) 2 * d == v2 * orbitDen (of20 o)) &&
                        (orbitNum (of20 o) 3 * d == v3 * orbitDen (of20 o)) &&
                          (orbitNum (of20 o) 4 * d == v4 * orbitDen (of20 o))
                else
                  if failKindAt r == 0 then
                    let i := failRowAt r
                    let lhs := rowDotN i v0 v1 v2 v3 v4
                    let rhs := bZ i * d
                    if 0 < d then decide (rhs < lhs) else decide (lhs < rhs)
                  else
                    decide (origCount (fun j => vecAt (5 * r + j.val)) d < 5)

def certsPrefix : ℕ → Bool
  | 0 => true
  | n + 1 => certsPrefix n && certOkUnrank n

def signCoord (s : Fin 16) (j : Fin 5) : ℤ :=
  if _ : j.val < 4 then
    if (s.val / Nat.pow 2 j.val) % 2 = 1 then -1 else 1
  else 1

def intDotFlip (o : Fin 20) (s : Fin 16) (i : Fin 28) : ℤ :=
  q28AZ i 0 * signCoord s 0 * orbitNum o 0 +
  q28AZ i 1 * signCoord s 1 * orbitNum o 1 +
  q28AZ i 2 * signCoord s 2 * orbitNum o 2 +
  q28AZ i 3 * signCoord s 3 * orbitNum o 3 +
  q28AZ i 4 * signCoord s 4 * orbitNum o 4

def tightMask (o : Fin 20) (s : Fin 16) : ℕ :=
  maskAt (o.val * 16 + s.val)

def popcount28 (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) + (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) + (if m.testBit 7 then 1 else 0) +
  (if m.testBit 8 then 1 else 0) + (if m.testBit 9 then 1 else 0) +
  (if m.testBit 10 then 1 else 0) + (if m.testBit 11 then 1 else 0) +
  (if m.testBit 12 then 1 else 0) + (if m.testBit 13 then 1 else 0) +
  (if m.testBit 14 then 1 else 0) + (if m.testBit 15 then 1 else 0) +
  (if m.testBit 16 then 1 else 0) + (if m.testBit 17 then 1 else 0) +
  (if m.testBit 18 then 1 else 0) + (if m.testBit 19 then 1 else 0) +
  (if m.testBit 20 then 1 else 0) + (if m.testBit 21 then 1 else 0) +
  (if m.testBit 22 then 1 else 0) + (if m.testBit 23 then 1 else 0) +
  (if m.testBit 24 then 1 else 0) + (if m.testBit 25 then 1 else 0) +
  (if m.testBit 26 then 1 else 0) + (if m.testBit 27 then 1 else 0)

def commonActiveCard (o1 o2 : Fin 20) (s : Fin 16) : ℕ :=
  cardAt (o1.val * 320 + o2.val * 16 + s.val)

def bitOf (o s i : ℕ) : Bool :=
  flipDotAt (o * 448 + s * 28 + i) == orbitDen (of20 o)

def computedMask (o s : ℕ) : ℕ :=
  (if bitOf o s 0 then 1 else 0) +
  (if bitOf o s 1 then 2 else 0) +
  (if bitOf o s 2 then 4 else 0) +
  (if bitOf o s 3 then 8 else 0) +
  (if bitOf o s 4 then 16 else 0) +
  (if bitOf o s 5 then 32 else 0) +
  (if bitOf o s 6 then 64 else 0) +
  (if bitOf o s 7 then 128 else 0) +
  (if bitOf o s 8 then 256 else 0) +
  (if bitOf o s 9 then 512 else 0) +
  (if bitOf o s 10 then 1024 else 0) +
  (if bitOf o s 11 then 2048 else 0) +
  (if bitOf o s 12 then 4096 else 0) +
  (if bitOf o s 13 then 8192 else 0) +
  (if bitOf o s 14 then 16384 else 0) +
  (if bitOf o s 15 then 32768 else 0) +
  (if bitOf o s 16 then 65536 else 0) +
  (if bitOf o s 17 then 131072 else 0) +
  (if bitOf o s 18 then 262144 else 0) +
  (if bitOf o s 19 then 524288 else 0) +
  (if bitOf o s 20 then 1048576 else 0) +
  (if bitOf o s 21 then 2097152 else 0) +
  (if bitOf o s 22 then 4194304 else 0) +
  (if bitOf o s 23 then 8388608 else 0) +
  (if bitOf o s 24 then 16777216 else 0) +
  (if bitOf o s 25 then 33554432 else 0) +
  (if bitOf o s 26 then 67108864 else 0) +
  (if bitOf o s 27 then 134217728 else 0)

theorem certOk_01234 : certOkAt 0 1 2 3 4 = true := rfl

def checkChunk (off n : ℕ) : Bool :=
  (List.range n).all fun i => certOkUnrank (off + i)

theorem checkChunk_00 : checkChunk 0 100 = true := rfl
theorem checkChunk_01 : checkChunk 100 100 = true := rfl
theorem checkChunk_02 : checkChunk 200 100 = true := rfl
theorem checkChunk_03 : checkChunk 300 100 = true := rfl
theorem checkChunk_04 : checkChunk 400 100 = true := rfl
theorem checkChunk_05 : checkChunk 500 100 = true := rfl
theorem checkChunk_06 : checkChunk 600 100 = true := rfl
theorem checkChunk_07 : checkChunk 700 100 = true := rfl
theorem checkChunk_08 : checkChunk 800 100 = true := rfl
theorem checkChunk_09 : checkChunk 900 100 = true := rfl
theorem checkChunk_10 : checkChunk 1000 100 = true := rfl
theorem checkChunk_11 : checkChunk 1100 100 = true := rfl
theorem checkChunk_12 : checkChunk 1200 100 = true := rfl
theorem checkChunk_13 : checkChunk 1300 100 = true := rfl
theorem checkChunk_14 : checkChunk 1400 100 = true := rfl
theorem checkChunk_15 : checkChunk 1500 100 = true := rfl
theorem checkChunk_16 : checkChunk 1600 100 = true := rfl
theorem checkChunk_17 : checkChunk 1700 100 = true := rfl
theorem checkChunk_18 : checkChunk 1800 100 = true := rfl
theorem checkChunk_19 : checkChunk 1900 100 = true := rfl
theorem checkChunk_20 : checkChunk 2000 2 = true := rfl

lemma checkChunk_spec (off n r : ℕ)
    (h : checkChunk off n = true) (h1 : off ≤ r) (h2 : r < off + n) :
    certOkUnrank r = true := by
  have hr : r - off < n := by omega
  have hall := (List.all_eq_true.mp h) (r - off) (List.mem_range.mpr hr)
  have : off + (r - off) = r := Nat.add_sub_of_le h1
  simpa [this] using hall

theorem certOkUnrank_all (r : ℕ) (hr : r < 2002) : certOkUnrank r = true := by
  rcases Nat.lt_or_ge r 100 with h | h
  · exact checkChunk_spec 0 100 r checkChunk_00 (Nat.zero_le _) h
  rcases Nat.lt_or_ge r 200 with h2 | h2
  · exact checkChunk_spec 100 100 r checkChunk_01 h h2
  rcases Nat.lt_or_ge r 300 with h3 | h3
  · exact checkChunk_spec 200 100 r checkChunk_02 h2 h3
  rcases Nat.lt_or_ge r 400 with h4 | h4
  · exact checkChunk_spec 300 100 r checkChunk_03 h3 h4
  rcases Nat.lt_or_ge r 500 with h5 | h5
  · exact checkChunk_spec 400 100 r checkChunk_04 h4 h5
  rcases Nat.lt_or_ge r 600 with h6 | h6
  · exact checkChunk_spec 500 100 r checkChunk_05 h5 h6
  rcases Nat.lt_or_ge r 700 with h7 | h7
  · exact checkChunk_spec 600 100 r checkChunk_06 h6 h7
  rcases Nat.lt_or_ge r 800 with h8 | h8
  · exact checkChunk_spec 700 100 r checkChunk_07 h7 h8
  rcases Nat.lt_or_ge r 900 with h9 | h9
  · exact checkChunk_spec 800 100 r checkChunk_08 h8 h9
  rcases Nat.lt_or_ge r 1000 with h10 | h10
  · exact checkChunk_spec 900 100 r checkChunk_09 h9 h10
  rcases Nat.lt_or_ge r 1100 with h11 | h11
  · exact checkChunk_spec 1000 100 r checkChunk_10 h10 h11
  rcases Nat.lt_or_ge r 1200 with h12 | h12
  · exact checkChunk_spec 1100 100 r checkChunk_11 h11 h12
  rcases Nat.lt_or_ge r 1300 with h13 | h13
  · exact checkChunk_spec 1200 100 r checkChunk_12 h12 h13
  rcases Nat.lt_or_ge r 1400 with h14 | h14
  · exact checkChunk_spec 1300 100 r checkChunk_13 h13 h14
  rcases Nat.lt_or_ge r 1500 with h15 | h15
  · exact checkChunk_spec 1400 100 r checkChunk_14 h14 h15
  rcases Nat.lt_or_ge r 1600 with h16 | h16
  · exact checkChunk_spec 1500 100 r checkChunk_15 h15 h16
  rcases Nat.lt_or_ge r 1700 with h17 | h17
  · exact checkChunk_spec 1600 100 r checkChunk_16 h16 h17
  rcases Nat.lt_or_ge r 1800 with h18 | h18
  · exact checkChunk_spec 1700 100 r checkChunk_17 h17 h18
  rcases Nat.lt_or_ge r 1900 with h19 | h19
  · exact checkChunk_spec 1800 100 r checkChunk_18 h18 h19
  rcases Nat.lt_or_ge r 2000 with h20 | h20
  · exact checkChunk_spec 1900 100 r checkChunk_19 h19 h20
  · exact checkChunk_spec 2000 2 r checkChunk_20 h20 hr

def unrankOk : Bool :=
  (List.range 14).all fun s4 =>
    (List.range s4).all fun s3 =>
      (List.range s3).all fun s2 =>
        (List.range s2).all fun s1 =>
          (List.range s1).all fun s0 =>
            let t := unrank5 (combRank s0 s1 s2 s3 s4)
            (t.1 == s0) && (t.2.1 == s1) && (t.2.2.1 == s2) &&
              (t.2.2.2.1 == s3) && (t.2.2.2.2 == s4)

theorem unrankOk_true : unrankOk = true := rfl

lemma unrank_rank (s0 s1 s2 s3 s4 : ℕ)
    (h01 : s0 < s1) (h12 : s1 < s2) (h23 : s2 < s3) (h34 : s3 < s4) (h4 : s4 < 14) :
    unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4) := by
  have h := unrankOk_true
  simp [unrankOk, List.all_eq_true, List.mem_range] at h
  have hok := h s4 (by omega) s3 (by omega) s2 (by omega) s1 (by omega) s0 (by omega)
  simp at hok
  rcases hok with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4'⟩
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4')))

lemma combRank_lt {s0 s1 s2 s3 s4 : ℕ}
    (h01 : s0 < s1) (h12 : s1 < s2) (h23 : s2 < s3) (h34 : s3 < s4) (h4 : s4 < 14) :
    combRank s0 s1 s2 s3 s4 < 2002 := by
  have hs4 : s4 ≤ 13 := Nat.lt_succ_iff.mp h4
  have hs3 : s3 ≤ 12 := by omega
  have hs2 : s2 ≤ 11 := by omega
  have hs1 : s1 ≤ 10 := by omega
  have hs0 : s0 ≤ 9 := by omega
  have c5 : ch s4 5 ≤ 1287 := by
    revert s4 hs4 h4; intro s4 hs4 h4
    interval_cases s4 <;> simp [ch]
  have c4 : ch s3 4 ≤ 495 := by
    interval_cases s3 <;> simp [ch]
  have c3 : ch s2 3 ≤ 165 := by
    interval_cases s2 <;> simp [ch]
  have c2 : ch s1 2 ≤ 45 := by
    interval_cases s1 <;> simp [ch]
  have c1 : ch s0 1 ≤ 9 := by
    simp [ch]; omega
  simp [combRank]
  omega

def fourOk (o1 o2 s : ℕ) : Bool :=
  let c := cardAt (o1 * 320 + o2 * 16 + s)
  decide (c < 4 ∨ o1 = o2 ∨
    (o1, o2) ∈ quotientEdges ∨ (o2, o1) ∈ quotientEdges)

def fourAll : Bool :=
  (List.range 20).all fun o1 =>
    (List.range 20).all fun o2 =>
      (List.range 16).all fun s =>
        fourOk o1 o2 s

theorem fourAll_true : fourAll = true := rfl

lemma of20_val (o : Fin 20) : of20 o.val = o :=
  Fin.ext (Nat.mod_eq_of_lt o.isLt)

lemma of16_val (s : Fin 16) : of16 s.val = s :=
  Fin.ext (Nat.mod_eq_of_lt s.isLt)

lemma of14_val (s : Fin 14) : of14 s.val = s :=
  Fin.ext (Nat.mod_eq_of_lt s.isLt)

theorem four_actives_in_quotient :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      4 ≤ commonActiveCard o1 o2 s →
      o1 = o2 ∨ QuotientAdj o1 o2 := by
  intro o1 o2 s hcard
  have h := fourAll_true
  simp [fourAll, List.all_eq_true, List.mem_range] at h
  have hok : fourOk o1.val o2.val s.val = true :=
    h o1.val o1.isLt o2.val o2.isLt s.val s.isLt
  have hprop := of_decide_eq_true (by simpa [fourOk] using hok)
  rcases hprop with hlt | heq | hadj | hadj
  · have : cardAt (o1.val * 320 + o2.val * 16 + s.val) < 4 := hlt
    simp [commonActiveCard] at hcard
    omega
  · exact Or.inl (Fin.ext heq)
  · exact Or.inr (Or.inl hadj)
  · exact Or.inr (Or.inr hadj)

def gapOk (o1 o2 s : ℕ) : Bool :=
  let lv := orbitLevel (of20 o1)
  let lw := orbitLevel (of20 o2)
  let gap := max lv lw - min lv lw
  decide (gap ≤ 1 ∨ cardAt (o1 * 320 + o2 * 16 + s) ≤ 3)

def gapAll : Bool :=
  (List.range 20).all fun o1 =>
    (List.range 20).all fun o2 =>
      (List.range 16).all fun s =>
        gapOk o1 o2 s

theorem gapAll_true : gapAll = true := rfl

theorem common_active_of_level_gap :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      1 < max (orbitLevel o1) (orbitLevel o2) - min (orbitLevel o1) (orbitLevel o2) →
      commonActiveCard o1 o2 s ≤ 3 := by
  intro o1 o2 s hgap
  have h := gapAll_true
  simp [gapAll, List.all_eq_true, List.mem_range] at h
  have hok : gapOk o1.val o2.val s.val = true :=
    h o1.val o1.isLt o2.val o2.isLt s.val s.isLt
  have hprop := of_decide_eq_true (by simpa [gapOk] using hok)
  rcases hprop with hle | hcard
  · have ho1 := of20_val o1
    have ho2 := of20_val o2
    simp [ho1, ho2] at hle
    omega
  · simpa [commonActiveCard] using hcard

theorem orbitLevel_step :
    ∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1 := by
  decide

theorem mask_bit :
    ∀ (o : Fin 20) (s : Fin 16) (i : Fin 28),
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o := by
  decide

