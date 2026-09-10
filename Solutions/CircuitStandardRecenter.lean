import Solutions.CircuitSourceBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace HirschCircuit

/-- Recenter the affine nonnegative slice at any feasible point. -/
theorem standardSlice_recenter {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c) :
    StandardSlice K c = StandardSlice K v := by
  ext s
  constructor
  · intro hs
    refine ⟨?_, hs.2⟩
    have hdecomp : s - v = (s - c) - (v - c) := by
      funext i
      simp only [Pi.sub_apply]
      ring
    rw [hdecomp]
    exact K.sub_mem hs.1 hv.1
  · intro hs
    refine ⟨?_, hs.2⟩
    have hdecomp : s - c = (s - v) + (v - c) := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [hdecomp]
    exact K.add_mem hs.1 hv.1

/-- `StandardCircuitStep` depends on the affine center only through the
underlying slice, so recentering at a feasible target preserves it exactly. -/
theorem standardCircuitStep_recenter_iff {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v x y : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c) :
    StandardCircuitStep K c x y ↔ StandardCircuitStep K v x y := by
  have hset := standardSlice_recenter K c v hv
  simp only [StandardCircuitStep]
  rw [hset]

/-- Padded standard-form circuit walks are unchanged by recentering the affine
slice at a feasible point. -/
theorem standardCircuitWalk_recenter_iff {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c)
    (L : ℕ) (u w : Fin n → ℝ) :
    StandardCircuitWalk K c L u w ↔ StandardCircuitWalk K v L u w := by
  have hset := standardSlice_recenter K c v hv
  simp only [StandardCircuitWalk, StandardCircuitStep]
  rw [hset]

/-- Extreme points transfer verbatim under recentering because the feasible
sets are literally equal. -/
theorem extremePoint_recenter {n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (c v x : Fin n → ℝ)
    (hv : v ∈ StandardSlice K c)
    (hx : x ∈ Set.extremePoints ℝ (StandardSlice K c)) :
    x ∈ Set.extremePoints ℝ (StandardSlice K v) := by
  rwa [← standardSlice_recenter K c v hv]

#print axioms standardSlice_recenter
#print axioms standardCircuitStep_recenter_iff
#print axioms standardCircuitWalk_recenter_iff
#print axioms extremePoint_recenter

end HirschCircuit
