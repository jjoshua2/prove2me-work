import Mathlib.Data.Nat.Count
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Fin

open Finset Nat

set_option maxHeartbeats 2000000

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

lemma popcount28_eq_count (m : ℕ) :
    popcount28 m = Nat.count (fun i => m.testBit i = true) 28 := by
  simp [popcount28, Nat.count_succ, Nat.count_zero]

lemma popcount28_eq_filter_range (m : ℕ) :
    popcount28 m = #{x ∈ range 28 | m.testBit x = true} := by
  rw [popcount28_eq_count, Nat.count_eq_card_filter_range]

lemma range_eq_Iio_nat (n : ℕ) : range n = Iio n := by
  ext x
  simp [mem_range, mem_Iio]

lemma popcount28_eq_filter (m : ℕ) :
    popcount28 m =
      (univ.filter (fun i : Fin 28 => m.testBit i.val = true)).card := by
  rw [popcount28_eq_filter_range, range_eq_Iio_nat, ← Fin.map_valEmbedding_univ]
  rw [filter_map]
  simp [card_map]
