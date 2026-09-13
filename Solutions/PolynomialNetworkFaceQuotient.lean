import Solutions.PolynomialNetworkForestEdges

/-! Exact affine quotient and directed-path implication primitives.
New proof candidates; no local Lean or platform verification is asserted. -/
open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschNetwork
variable {V W A : Type*} [DecidableEq V] [DecidableEq A]

def componentLift (group : V → W) (offset : V → ℝ) (z : W → ℝ) : V → ℝ :=
  fun i => z (group i)+offset i

theorem quotient_slack_identity
    (group : V → W) (offset : V → ℝ) (z : W → ℝ)
    (tail head : A → V) (bound : A → ℝ) (e : A) :
    bound e-(componentLift group offset z (head e)-componentLift group offset z (tail e)) =
      (bound e-offset (head e)+offset (tail e))-(z (group (head e))-z (group (tail e))) := by
  simp only [componentLift]
  ring

/-- Every original row, including a loop after contraction, is represented. -/
theorem componentLift_mem_iff
    (root : V) (tail head : A → V) (bound : A → ℝ)
    (group : V → W) (offset : V → ℝ) (ho : offset root=0) (z : W → ℝ) :
    componentLift group offset z∈potentials root tail head bound ↔
      z∈potentials (group root) (group ∘ tail) (group ∘ head)
        (fun e => bound e-offset (head e)+offset (tail e)) := by
  simp only [potentials,Set.mem_setOf_eq,componentLift,Function.comp_apply,ho,add_zero]
  constructor
  · rintro ⟨hz,h⟩
    refine ⟨hz,?_⟩
    intro e
    have he := h e
    linarith
  · rintro ⟨hz,h⟩
    refine ⟨hz,?_⟩
    intro e
    have he := h e
    linarith

/-- Connectivity supplies the inverse affine coordinates of the actual
common-equality face, rather than merely an inclusion into a convenient model. -/
theorem reconstruct_from_component_equalities
    (tail head : A → V) (S : Finset A)
    (group : V → W) (representative : W → V) (offset x : V → ℝ)
    (hoff : ∀ c,offset (representative c)=0)
    (hconn : ∀ i,Nonempty ((rowGraph tail head S).Walk (representative (group i)) i))
    (heq : ∀ e∈S,x (head e)-x (tail e)=offset (head e)-offset (tail e)) :
    componentLift group offset (fun c => x (representative c))=x := by
  have hker : ∀ e∈S,(x-offset) (head e)-(x-offset) (tail e)=0 := by
    intro e he
    have h := heq e he
    simp only [Pi.sub_apply]
    linarith
  funext i
  obtain ⟨w⟩ := hconn i
  have h := value_eq_of_row_walk tail head S (x-offset) hker w
  change x (representative (group i))-offset (representative (group i))=x i-offset i at h
  rw [hoff] at h
  simp only [componentLift]
  linarith

theorem componentLift_injective
    (group : V → W) (representative : W → V) (offset : V → ℝ)
    (hrep : ∀ c,group (representative c)=c) :
    Function.Injective (componentLift group offset) := by
  intro x y he
  funext c
  have h := congrFun he (representative c)
  simpa [componentLift,hrep c] using h

/-- A directed path is a nonnegative multiplier certificate for the direct
inequality. This works with negative original bounds and parallel rows. -/
theorem inequality_of_directed_path
    (n : ℕ) (x : ℕ → ℝ) (cost : Fin n → ℝ) (C : ℝ)
    (h : ∀ i : Fin n,x (i.val+1)-x i.val≤cost i)
    (hsum : (∑ i,cost i)≤C) : x n-x 0≤C := by
  have ht : ∀ m : ℕ,(∑ i : Fin m,x (i.val+1)-x i.val)=x m-x 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [ih]
      ring
  have hh := Finset.sum_le_sum (fun i _ => h i)
  rw [ht] at hh
  exact hh.trans hsum

/-- The midpoint is strictly feasible in every noncommon endpoint row.
That supplies positive reduced lengths to the exact redundancy detector. -/
theorem midpoint_strict_of_not_common {u v b : ℝ}
    (hu : u≤b) (hv : v≤b) (hn : ¬(u=b ∧ v=b)) : (u+v)/2<b := by
  by_contra h
  have he : (u+v)/2=b := by linarith
  exact hn ⟨by linarith,by linarith⟩

#print axioms quotient_slack_identity
#print axioms componentLift_mem_iff
#print axioms reconstruct_from_component_equalities
#print axioms componentLift_injective
#print axioms inequality_of_directed_path
#print axioms midpoint_strict_of_not_common
end HirschNetwork
