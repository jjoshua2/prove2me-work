import Solutions.PolynomialCircuitStepProgress
import Solutions.PolynomialCircuitCarrierRank
import Solutions.PolynomialCircuitCarrierEdge

/-!
# Whole-walk circuit rank accounting

CANDIDATE SOURCE: not compiled in the pinned Lean environment in this session.
The accompanying ordinary proof and exact regressions are separate evidence.
No platform theorem, Open child, axiom, or publication is introduced here.

For a pair x,y let p=dim F(x,x), q=dim F(y,y), h=dim F(x,y).
The loss and gain are h-p and h-q. These count ranks, not describing rows.
Padding has zero charge. A maximal circuit step gains at least one rank.
The final results concern whole walks, including nonvertex checkpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitWalkBudget

open HirschPolynomialAccess HirschCircuitLocalization

variable {d n : ℕ}

noncomputable def loss
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℕ :=
  commonFaceDim a b x y - commonFaceDim a b x x

noncomputable def gain
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℕ :=
  commonFaceDim a b x y - commonFaceDim a b y y

noncomputable def charge (x y : EuclideanSpace ℝ (Fin d)) : ℕ :=
  if x = y then 0 else 1

/-- Residual of the circuit-localization bound. For a certified circuit step,
this equals a sum of four nonnegative row-count/rank surpluses. The four-term
identification is proved in the accompanying note, not asserted by this def. -/
noncomputable def slack
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℕ :=
  if x = y then 0 else (n - d + 1) - (loss a b x y + gain a b x y)

noncomputable def totalLoss
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range L, loss a b (w k) (w (k + 1))

noncomputable def totalGain
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range L, gain a b (w k) (w (k + 1))

noncomputable def totalSlack
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range L, slack a b (w k) (w (k + 1))

noncomputable def nonstayCount
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) : ℕ :=
  ∑ k ∈ Finset.range L, charge (w k) (w (k + 1))

lemma commonFaceDim_symm
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    commonFaceDim a b x y = commonFaceDim a b y x := by
  have hC : commonSourceRows a b x y = commonSourceRows a b y x := by
    ext i
    simp [commonSourceRows, and_comm, and_left_comm, and_assoc]
  unfold commonFaceDim commonDirection
  rw [hC]

lemma source_self_direction_le_carrier
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    commonDirection a b x x ≤ commonDirection a b x y := by
  intro z hz
  have hself : rowEvalMap a (commonSourceRows a b x x) z = 0 :=
    LinearMap.mem_ker.1 hz
  change rowEvalMap a (commonSourceRows a b x y) z = 0
  funext ii
  have hi := (Finset.mem_filter.1 ii.2).2
  have hiXX : ii.1 ∈ commonSourceRows a b x x := by
    simp [commonSourceRows, hi.1, hi.2.1]
  exact congrFun hself ⟨ii.1, hiXX⟩

lemma endpoint_nullities_le_carrier
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    commonFaceDim a b x x ≤ commonFaceDim a b x y ∧
      commonFaceDim a b y y ≤ commonFaceDim a b x y := by
  constructor
  · exact Submodule.finrank_mono (source_self_direction_le_carrier a b x y)
  · rw [commonFaceDim_symm a b x y]
    exact Submodule.finrank_mono (source_self_direction_le_carrier a b y x)

lemma self_nullity_zero_of_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    commonFaceDim a b x x = 0 := by
  have h := commonFaceDim_le_sourceOnlyRows_card a b x x hx
  simpa [sourceOnlyRows] using h

/-- The converse is included to avoid silently treating a nonvertex
checkpoint as a vertex. Feasibility is essential here. -/
lemma extreme_of_self_nullity_zero
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b)
    (hdim : commonFaceDim a b x x = 0) :
    x ∈ extremePoints ℝ (Hpoly a b) := by
  refine ⟨hx, ?_⟩
  intro u hu v hv hxuv
  have hxF : x ∈ commonFace a b x x := commonFace_u_mem a b x x hx
  have huF : u ∈ commonFace a b x x :=
    (commonFace_isExtreme a b x x).2 hu hv hxF hxuv
  have hdir : u - x ∈ commonDirection a b x x :=
    ((mem_commonFace_iff_sub_mem_commonDirection a b x x u).1 huF).2
  by_contra hne
  have hdisp : u - x ≠ 0 := sub_ne_zero.mpr hne
  have hspan : Submodule.span ℝ ({u - x} : Set (EuclideanSpace ℝ (Fin d))) ≤
      commonDirection a b x x := by
    apply Submodule.span_le.2
    intro z hz
    have heq : z = u - x := by simpa only [Set.mem_singleton_iff] using hz
    rw [heq]
    exact hdir
  have hle := Submodule.finrank_mono hspan
  rw [finrank_span_singleton hdisp] at hle
  change 1 ≤ commonFaceDim a b x x at hle
  omega

/-- Exact local conservation, without feasibility or circuit hypotheses. -/
lemma local_rank_balance
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    loss a b x y + commonFaceDim a b x x =
      gain a b x y + commonFaceDim a b y y := by
  obtain ⟨hp, hq⟩ := endpoint_nullities_le_carrier a b x y
  unfold loss gain
  omega

lemma local_circuit_rank_budget
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b)) (hg : IsRowCircuit a (y - x)) :
    loss a b x y + gain a b x y ≤ n - d + 1 := by
  have hloc := rowCircuit_commonFaceDim_checkpoint_localization a b z x y hz hg
  obtain ⟨hp, hq⟩ := endpoint_nullities_le_carrier a b x y
  unfold loss gain
  omega

lemma maximal_step_gain_pos
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (hs : RowCircuitStep a b x y) :
    1 ≤ gain a b x y := by
  have h := rowCircuitStep_target_commonFaceDim_lt a b x y hs
  unfold gain
  omega

lemma local_padded_budget_exact
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hs : x = y ∨ RowCircuitStep a b x y) :
    loss a b x y + gain a b x y + slack a b x y =
      charge x y * (n - d + 1) := by
  by_cases heq : x = y
  · subst y
    simp [loss, gain, slack, charge]
  · have hstep : RowCircuitStep a b x y := hs.resolve_left heq
    have hb := local_circuit_rank_budget a b z x y hz hstep.2.2.1
    simp only [slack, charge, heq, if_false, one_mul]
    omega

/-- The endpoint-corrected whole-walk conservation law is purely linear
algebra. It applies to arbitrary sequences, even before feasibility. -/
theorem walk_rank_balance
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ) :
    totalLoss a b w L + commonFaceDim a b (w 0) (w 0) =
      totalGain a b w L + commonFaceDim a b (w L) (w L) := by
  unfold totalLoss totalGain
  induction L with
  | zero => simp
  | succ L ih =>
    simp only [Finset.sum_range_succ]
    have h := local_rank_balance a b (w L) (w (L + 1))
    omega

/-- Exact total localization budget, with zero cost for padding. -/
theorem walk_total_budget_exact
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hs : ∀ k < L, w k = w (k + 1) ∨ RowCircuitStep a b (w k) (w (k + 1))) :
    totalLoss a b w L + totalGain a b w L + totalSlack a b w L =
      nonstayCount w L * (n - d + 1) := by
  unfold totalLoss totalGain totalSlack nonstayCount
  calc
    _ = ∑ k ∈ Finset.range L,
        (loss a b (w k) (w (k + 1)) + gain a b (w k) (w (k + 1)) +
          slack a b (w k) (w (k + 1))) := by
      simp only [Finset.sum_add_distrib]
    _ = ∑ k ∈ Finset.range L, charge (w k) (w (k + 1)) * (n - d + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact local_padded_budget_exact a b z (w k) (w (k + 1)) hz
        (hs k (Finset.mem_range.1 hk))
    _ = _ := by rw [Finset.sum_mul]

/-- Each genuine maximal step contributes at least one gained rank. -/
theorem nonstayCount_le_totalGain
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hs : ∀ k < L, w k = w (k + 1) ∨ RowCircuitStep a b (w k) (w (k + 1))) :
    nonstayCount w L ≤ totalGain a b w L := by
  unfold nonstayCount totalGain
  apply Finset.sum_le_sum
  intro k hk
  by_cases heq : w k = w (k + 1)
  · simp [charge, heq]
  · have hstep := (hs k (Finset.mem_range.1 hk)).resolve_left heq
    simpa only [charge, heq, if_false] using
      maximal_step_gain_pos a b (w k) (w (k + 1)) hstep

/-- A global exact identity that retains both endpoint corrections. -/
theorem walk_endpoint_corrected_budget_exact
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hs : ∀ k < L, w k = w (k + 1) ∨ RowCircuitStep a b (w k) (w (k + 1))) :
    2 * totalGain a b w L + commonFaceDim a b (w L) (w L) + totalSlack a b w L =
      nonstayCount w L * (n - d + 1) + commonFaceDim a b (w 0) (w 0) := by
  have hb := walk_rank_balance a b w L
  have ht := walk_total_budget_exact a b z hz w L hs
  omega

/-- Main conservation/half-budget theorem. Endpoint vertexhood, not
vertexhood of the intervening checkpoints, makes total loss equal gain. -/
theorem vertex_circuit_walk_rank_half_budget
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ extremePoints ℝ (Hpoly a b))
    (hs : ∀ k < L, w k = w (k + 1) ∨ RowCircuitStep a b (w k) (w (k + 1))) :
    nonstayCount w L ≤ totalLoss a b w L ∧
      totalLoss a b w L = totalGain a b w L ∧
      totalLoss a b w L ≤ nonstayCount w L * (n - d + 1) / 2 := by
  have hb := walk_rank_balance a b w L
  have ht := walk_total_budget_exact a b (w 0) h0 w L hs
  have hm := nonstayCount_le_totalGain a b w L hs
  have hp := self_nullity_zero_of_extreme a b (w 0) h0
  have hq := self_nullity_zero_of_extreme a b (w L) hL
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Pointwise rank-loss at most one certifies the ORIGINAL witness as an
edge/stay walk. An average bound of one is deliberately not substituted. -/
theorem rank_one_walk_is_edge_walk
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hs : ∀ k < L, w k = w (k + 1) ∨ RowCircuitStep a b (w k) (w (k + 1)))
    (hloss : ∀ k < L, loss a b (w k) (w (k + 1)) ≤ 1) :
    (∀ k ≤ L, w k ∈ extremePoints ℝ (Hpoly a b)) ∧
      ∀ k < L, w k = w (k + 1) ∨ Adj (Hpoly a b) (w k) (w (k + 1)) := by
  have hzero : ∀ k : ℕ, k ≤ L → commonFaceDim a b (w k) (w k) = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact self_nullity_zero_of_extreme a b (w 0) h0
    | succ k ih =>
      intro hk
      have hklt : k < L := by omega
      have hzk := ih (by omega)
      rcases hs k hklt with heq | hstep
      · simpa only [heq] using hzk
      · have hb := local_rank_balance a b (w k) (w (k + 1))
        have hl := hloss k hklt
        have hg := maximal_step_gain_pos a b (w k) (w (k + 1)) hstep
        change commonFaceDim a b (w (k + 1)) (w (k + 1)) = 0
        omega
  have hver : ∀ k ≤ L, w k ∈ extremePoints ℝ (Hpoly a b) := by
    intro k hk
    exact extreme_of_self_nullity_zero a b (w k) (hfeas k hk) (hzero k hk)
  refine ⟨hver, ?_⟩
  intro k hk
  rcases hs k hk with heq | hstep
  · exact Or.inl heq
  · right
    have hp := hzero k (by omega)
    have hl := hloss k hk
    have hdim : commonFaceDim a b (w k) (w (k + 1)) ≤ 1 := by
      simpa only [loss, hp, Nat.sub_zero] using hl
    exact rowCircuitStep_adj_of_commonFaceDim_le_one a b (w k) (w (k + 1))
      (hver k (by omega)) hstep hdim

/-- With at most d+1 describing rows, maximality and circuit localization
supply the pointwise rank-one certificate automatically. No boundedness,
irredundancy, strict feasibility, or vertex target is required. -/
theorem small_row_excess_walk_is_edge_walk
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ extremePoints ℝ (Hpoly a b))
    (hs : ∀ k < L, w k = w (k + 1) ∨ RowCircuitStep a b (w k) (w (k + 1)))
    (hrows : n ≤ d + 1) :
    (∀ k ≤ L, w k ∈ extremePoints ℝ (Hpoly a b)) ∧
      ∀ k < L, w k = w (k + 1) ∨ Adj (Hpoly a b) (w k) (w (k + 1)) := by
  apply rank_one_walk_is_edge_walk a b w L hfeas h0 hs
  intro k hk
  rcases hs k hk with heq | hstep
  · simp [loss, heq]
  · have hb := rowCircuitStep_commonFaceDim_source_bound
      a b (w 0) (w k) (w (k + 1)) h0 hstep
    unfold loss
    omega

/-- A genuine no-overhead refinement theorem for the small-row-excess
class, rather than another Open restatement of global edge refinement. -/
theorem rowCircuitWalk_refines_no_overhead_of_rows_le_dim_add_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hw : RowCircuitWalk a b L u v) (hrows : n ≤ d + 1) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w L = v ∧
      ∀ k < L, w k = w (k + 1) ∨ Adj (Hpoly a b) (w k) (w (k + 1)) := by
  obtain ⟨w, hw0, hwL, hfeas, hs⟩ := hw
  have h0 : w 0 ∈ extremePoints ℝ (Hpoly a b) := by
    simpa only [hw0] using hu
  exact ⟨w, hw0, hwL,
    (small_row_excess_walk_is_edge_walk a b w L hfeas h0 hs hrows).2⟩

#print axioms walk_rank_balance
#print axioms walk_total_budget_exact
#print axioms walk_endpoint_corrected_budget_exact
#print axioms vertex_circuit_walk_rank_half_budget
#print axioms rank_one_walk_is_edge_walk
#print axioms small_row_excess_walk_is_edge_walk
#print axioms rowCircuitWalk_refines_no_overhead_of_rows_le_dim_add_one

end HirschCircuitWalkBudget
