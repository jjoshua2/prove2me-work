import Solutions.PolynomialVertexSpan
import Solutions.PolynomialClipEndpointLift
import Solutions.PolynomialAdjEndpoints

/-!
Compact single-cut vertex classification, without recession-ray enumeration.

Candidate source: NOT kernel-verified in the September 11 continuation runtime.
See research/COMPACT_CAP_VERTEX_CLASSIFICATION_2026-09-11.md for the ordinary
proof, exact regression evidence, and the precise verification boundary.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
namespace HirschCapVertices

variable {d n : ℕ}

lemma hpoly_convex (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy s t hs ht hst i
  simp only [inner_add_right, inner_smul_right]
  have hsum : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith [mul_le_mul_of_nonneg_left (hx i) hs,
    mul_le_mul_of_nonneg_left (hy i) ht]

lemma hpoly_isClosed (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    IsClosed (Hpoly a b) := by
  unfold Hpoly
  simp only [setOf_forall]
  exact isClosed_iInter (fun i => isClosed_le (by fun_prop) continuous_const)

lemma hpoly_cons_eq_inter
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (M : ℝ) :
    Hpoly (Fin.cons c a) (Fin.cons M b) = Hpoly a b ∩ {x | ⟪c, x⟫ ≤ M} := by
  ext x
  constructor
  · intro hx
    exact ⟨fun i => hx i.succ, hx 0⟩
  · rintro ⟨hx, hc⟩ i
    exact Fin.cases hc (fun k => hx k) i

/-- At a capped vertex, the cap functional is injective on the direction space
annihilating every old row active there. No rank or ray theorem is imported. -/
lemma cap_active_kernel_eq_zero
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (M : ℝ)
    (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ M}))
    (g : EuclideanSpace ℝ (Fin d))
    (hrows : ∀ i, ⟪a i, z⟫ = b i → ⟪a i, g⟫ = 0)
    (hcap : ⟪c, g⟫ = 0) : g = 0 := by
  have hz' : z ∈ extremePoints ℝ (Hpoly (Fin.cons c a) (Fin.cons M b)) := by
    rwa [hpoly_cons_eq_inter]
  apply HirschPolynomialAccess.vertex_tight_rows_span_checked d (n + 1)
    (Fin.cons c a) (Fin.cons M b) z hz' g
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · intro _
    exact hcap
  · intro hi
    exact hrows k hi

/-- A finite H-presentation has finitely many vertices, even if it is unbounded,
empty, lower-dimensional, or redundant. Equal complete tight-row sets force
equal vertices by the already-checked active-row kernel theorem. -/
theorem hpoly_extremePoints_finite
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    (extremePoints ℝ (Hpoly a b)).Finite := by
  classical
  let V := {x // x ∈ extremePoints ℝ (Hpoly a b)}
  let code : V → Finset (Fin n) := fun x => Finset.univ.filter (fun i => ⟪a i, x.1⟫ = b i)
  have hinj : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b x.1 x.2 (x.1 - y.1)
    intro i hi
    have himem : i ∈ code x := by simp [code, hi]
    have hymem : i ∈ code y := by simpa only [hxy] using himem
    have hyi : ⟪a i, y.1⟫ = b i := by simpa [code] using hymem
    rw [inner_sub_right, hi, hyi, sub_self]
  letI : Finite V := Finite.of_injective code hinj
  exact Set.toFinite _

/-- Every genuinely new vertex of a compact single-halfspace clip is adjacent
to an old outer vertex strictly below the clipping hyperplane.

The cap need not be beyond all old vertices. That stronger condition is needed
for preservation of ALL old graph routes, not for this local classification.
-/
theorem compact_hpoly_cap_vertex_classification
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (M : ℝ)
    (hcompact : IsCompact (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ M}))
    (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ M})) :
    z ∈ extremePoints ℝ (Hpoly a b) ∨
      (⟪c, z⟫ = M ∧ ∃ v ∈ extremePoints ℝ (Hpoly a b),
        ⟪c, v⟫ < M ∧ Adj (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ M}) v z) := by
  classical
  let Q := Hpoly a b
  let R := Q ∩ {x | ⟪c, x⟫ ≤ M}
  have hQ : Convex ℝ Q := hpoly_convex a b
  by_cases hold : z ∈ extremePoints ℝ Q
  · exact Or.inl hold
  have hzcap : ⟪c, z⟫ = M := by
    by_contra hne
    have hlt : ⟪c, z⟫ < M := lt_of_le_of_ne hz.1.2 hne
    exact hold (HirschCut.strict_cut_extreme_to_parent Q hQ c M hz hlt)
  have hker : ∀ g : EuclideanSpace ℝ (Fin d),
      (∀ i, ⟪a i, z⟫ = b i → ⟪a i, g⟫ = 0) → ⟪c, g⟫ = 0 → g = 0 :=
    cap_active_kernel_eq_zero a b c M z hz
  let F : Set (EuclideanSpace ℝ (Fin d)) :=
    R ∩ {x | ∀ i, ⟪a i, z⟫ = b i → ⟪a i, x⟫ = b i}
  have hzF : z ∈ F := ⟨hz.1, fun _ hi => hi⟩
  have hFc : IsCompact F := by
    apply hcompact.inter_right
    simp only [setOf_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _ =>
      isClosed_eq (by fun_prop) continuous_const))
  have hFe : IsExtreme ℝ R F := by
    refine ⟨inter_subset_left, ?_⟩
    intro x hx y hy q hq hseg
    refine ⟨hx, ?_⟩
    intro i hi
    have hf := HirschClipLift.supporting_equality_extreme R (a i) (b i)
      (fun w hw => hw.1 i)
    exact (hf.left_mem_of_mem_openSegment hx hy ⟨hq.1, hq.2 i hi⟩ hseg).2
  have hFconv : Convex ℝ F := by
    intro x hx y hy s t hs ht hst
    refine ⟨⟨hQ hx.1.1 hy.1.1 hs ht hst, ?_⟩, ?_⟩
    · change ⟪c, s • x + t • y⟫ ≤ M
      rw [inner_add_right, inner_smul_right, inner_smul_right]
      have hcx : ⟪c, x⟫ ≤ M := hx.1.2
      have hcy : ⟪c, y⟫ ≤ M := hy.1.2
      have hsum : s * M + t * M = M := by rw [← add_mul, hst, one_mul]
      linarith [mul_le_mul_of_nonneg_left hcx hs,
        mul_le_mul_of_nonneg_left hcy ht]
    · intro i hi
      rw [inner_add_right, inner_smul_right, inner_smul_right,
        hx.2 i hi, hy.2 i hi, ← add_mul, hst, one_mul]
  -- Non-extremeness in Q gives a two-sided old segment through z.
  have hwitness : ∃ u ∈ Q, ∃ w ∈ Q,
      z ∈ openSegment ℝ u w ∧ u ≠ z := by
    by_contra h
    apply hold
    refine ⟨hz.1.1, ?_⟩
    intro u hu w hw hseg
    by_contra hne
    exact h ⟨u, hu, w, hw, hseg, hne⟩
  obtain ⟨u, hu, w, hw, hseg, hune⟩ := hwitness
  have huA : ∀ i, ⟪a i, z⟫ = b i → ⟪a i, u⟫ = b i := by
    intro i hi
    have hf := HirschClipLift.supporting_equality_extreme Q (a i) (b i)
      (fun x hx => hx i)
    exact (hf.left_mem_of_mem_openSegment hu hw ⟨hz.1.1, hi⟩ hseg).2
  have hwA : ∀ i, ⟪a i, z⟫ = b i → ⟪a i, w⟫ = b i := by
    intro i hi
    have hf := HirschClipLift.supporting_equality_extreme Q (a i) (b i)
      (fun x hx => hx i)
    exact (hf.right_mem_of_mem_openSegment hu hw ⟨hz.1.1, hi⟩ hseg).2
  have hlower : ∃ y ∈ F, ⟪c, y⟫ < M := by
    by_cases huLt : ⟪c, u⟫ < M
    · exact ⟨u, ⟨⟨hu, huLt.le⟩, huA⟩, huLt⟩
    have huNe : ⟪c, u⟫ ≠ M := by
      intro he
      apply hune
      apply sub_eq_zero.mp
      apply hker (u - z)
      · intro i hi
        rw [inner_sub_right, huA i hi, hi, sub_self]
      · rw [inner_sub_right, he, hzcap, sub_self]
    have huGt : M < ⟪c, u⟫ := lt_of_le_of_ne (le_of_not_gt huLt) huNe.symm
    obtain ⟨s, t, hs, ht, hst, heq⟩ := hseg
    have hcEq := congrArg (fun x : EuclideanSpace ℝ (Fin d) => ⟪c, x⟫) heq
    simp only [inner_add_right, inner_smul_right, hzcap] at hcEq
    have htotal : s * M + t * M = M := by rw [← add_mul, hst, one_mul]
    have hwLt : ⟪c, w⟫ < M := by
      by_contra h
      have hwGe := le_of_not_gt h
      have hp := mul_pos hs (sub_pos.mpr huGt)
      have hn := mul_nonneg ht.le (sub_nonneg.mpr hwGe)
      nlinarith
    exact ⟨w, ⟨⟨hw, hwLt.le⟩, hwA⟩, hwLt⟩
  obtain ⟨y, hyF, hyLt⟩ := hlower
  obtain ⟨v, hvF, hmin⟩ := hFc.exists_isMinOn ⟨z, hzF⟩
    (show Continuous (fun x : EuclideanSpace ℝ (Fin d) => ⟪c, x⟫) by fun_prop).continuousOn
  have hvLt : ⟪c, v⟫ < M := lt_of_le_of_lt (hmin hyF) hyLt
  have hvne : v ≠ z := by intro he; rw [he, hzcap] at hvLt; exact (lt_irrefl M) hvLt
  -- Cap evaluation parametrizes the entire compact active face.
  have hsegment : segment ℝ v z = F := by
    apply Set.Subset.antisymm
    · exact hFconv.segment_subset hvF hzF
    · intro x hx
      let t : ℝ := (⟪c, x⟫ - ⟪c, v⟫) / (M - ⟪c, v⟫)
      have hden : 0 < M - ⟪c, v⟫ := sub_pos.mpr hvLt
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hmin hx)) hden.le
      have hcapx : ⟪c, x⟫ ≤ M := hx.1.2
      have ht1 : t ≤ 1 := (div_le_iff₀ hden).mpr (by linarith [hcapx])
      have hmul : t * (M - ⟪c, v⟫) = ⟪c, x⟫ - ⟪c, v⟫ :=
        div_mul_cancel₀ _ hden.ne'
      let p := (1 - t) • v + t • z
      have hpA : ∀ i, ⟪a i, z⟫ = b i → ⟪a i, p⟫ = b i := by
        intro i hi
        dsimp [p]
        rw [inner_add_right, inner_smul_right, inner_smul_right, hvF.2 i hi, hi]
        ring
      have hpC : ⟪c, p⟫ = ⟪c, x⟫ := by
        dsimp [p]
        rw [inner_add_right, inner_smul_right, inner_smul_right, hzcap]
        nlinarith [hmul]
      have hpx : p = x := by
        apply sub_eq_zero.mp
        apply hker (p - x)
        · intro i hi
          rw [inner_sub_right, hpA i hi, hx.2 i hi, sub_self]
        · rw [inner_sub_right, hpC, sub_self]
      exact ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, hpx⟩
  have hadj : Adj R v z := ⟨hvne, by rw [hsegment]; exact hFe⟩
  have hvR : v ∈ extremePoints ℝ R := HirschPolynomialAccess.adj_left_extreme R hadj
  have hvQ : v ∈ extremePoints ℝ Q :=
    HirschCut.strict_cut_extreme_to_parent Q hQ c M hvR hvLt
  exact Or.inr ⟨hzcap, v, hvQ, hvLt, hadj⟩

/-- The missing global far-level condition: dominate the compact final set AND
every outer vertex, not merely the final set. Finiteness is proved above. -/
theorem exists_level_above_compact_and_outer_vertices
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hne : K.Nonempty)
    (c : EuclideanSpace ℝ (Fin d)) :
    ∃ M : ℝ, (∀ x ∈ K, ⟪c, x⟫ < M) ∧
      (∀ x ∈ extremePoints ℝ (Hpoly a b), ⟪c, x⟫ < M) := by
  have hc : IsCompact (K ∪ extremePoints ℝ (Hpoly a b)) :=
    hK.union (hpoly_extremePoints_finite a b).isCompact
  have hne' : (K ∪ extremePoints ℝ (Hpoly a b)).Nonempty :=
    hne.mono subset_union_left
  obtain ⟨z, hz, hmax⟩ := hc.exists_isMaxOn hne'
    (show Continuous (fun x : EuclideanSpace ℝ (Fin d) => ⟪c, x⟫) by fun_prop).continuousOn
  refine ⟨⟪c, z⟫ + 1, ?_, ?_⟩
  · intro x hx
    have h : ⟪c, x⟫ ≤ ⟪c, z⟫ := hmax (Or.inl hx)
    linarith
  · intro x hx
    have h : ⟪c, x⟫ ≤ ⟪c, z⟫ := hmax (Or.inr hx)
    linarith

lemma old_vertex_survives_cap
    (Q : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (M : ℝ)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ extremePoints ℝ Q)
    (hcap : ⟪c, u⟫ ≤ M) :
    u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ M}) := by
  refine ⟨⟨hu.1, hcap⟩, ?_⟩
  intro x hx y hy hseg
  exact hu.2 hx.1 hy.1 hseg

lemma old_edge_survives_cap
    (Q : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (M : ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) (huv : Adj Q u v)
    (hu : ⟪c, u⟫ ≤ M) (hv : ⟪c, v⟫ ≤ M) :
    Adj (Q ∩ {x | ⟪c, x⟫ ≤ M}) u v := by
  refine ⟨huv.1, ⟨?_, ?_⟩⟩
  · intro x hx
    refine ⟨huv.2.subset hx, ?_⟩
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
    change ⟪c, s • u + t • v⟫ ≤ M
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have hsum : s * M + t * M = M := by rw [← add_mul, hst, one_mul]
    linarith [mul_le_mul_of_nonneg_left hu hs, mul_le_mul_of_nonneg_left hv ht]
  · intro x hx y hy z hz hseg
    exact huv.2.left_mem_of_mem_openSegment hx.1 hy.1 hz hseg

#print axioms cap_active_kernel_eq_zero
#print axioms hpoly_extremePoints_finite
#print axioms compact_hpoly_cap_vertex_classification
#print axioms exists_level_above_compact_and_outer_vertices
#print axioms old_vertex_survives_cap
#print axioms old_edge_survives_cap

end HirschCapVertices
