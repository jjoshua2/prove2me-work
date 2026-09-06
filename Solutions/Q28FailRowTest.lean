import Definitions.Def_Hirsch_q28_cert

open Hirsch

set_option maxHeartbeats 8000000

lemma list_getD_lt_of_all {l : List ℕ} {i d b : ℕ}
    (h : ∀ x ∈ l, x < b) (hd : d < b) : l.getD i d < b := by
  cases hopt : l[i]? with
  | none =>
      simp [List.getD, hopt]
      exact hd
  | some x =>
      simp [List.getD, hopt]
      exact h x (List.mem_of_getElem? hopt)

theorem failRowChunks_lt :
    (List.range 63).all
      (fun c => (failRowAtChunk c).all (fun x => decide (x < 14))) = true :=
  rfl

lemma failRowAtChunk_all_lt {c : ℕ} (hc : c < 63) :
    (failRowAtChunk c).all (fun x => decide (x < 14)) = true := by
  have h := failRowChunks_lt
  have : c ∈ List.range 63 := List.mem_range.mpr hc
  exact (List.all_eq_true.mp h) c this

lemma failRowAt_lt {n : ℕ} (hn : n < 2002) : failRowAt n < 14 := by
  have hc : n / 32 < 63 := by omega
  unfold failRowAt
  refine list_getD_lt_of_all ?_ (by decide)
  intro x hx
  exact of_decide_eq_true
    ((List.all_eq_true.mp (failRowAtChunk_all_lt hc)) x hx)

#check failRowAt_lt
