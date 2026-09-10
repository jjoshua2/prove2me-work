import Mathlib
set_option autoImplicit false
namespace HirschBoxSlice

/-- Strict descent supplies a padded walk of any budget above the potential. -/
theorem walk_of_strict_potential
    {E : Type*} (R : E → E → Prop) (S : E → Prop)
    (v : E) (Φ : E → ℕ)
    (hnext : ∀ x, S x → x ≠ v → ∃ y, S y ∧ R x y ∧ Φ y < Φ x) :
    ∀ n : ℕ, ∀ x, S x → Φ x ≤ n → ∃ w : ℕ → E,
      w 0 = x ∧ w n = v ∧
      ∀ k < n, w k = w (k + 1) ∨ R (w k) (w (k + 1)) := by
  classical
  intro n
  induction n with
  | zero =>
      intro x hx hbound
      have heq : x = v := by
        by_contra h
        obtain ⟨y, hy, hedge, hdrop⟩ := hnext x hx h
        omega
      exact ⟨fun _ => v, heq.symm, rfl, by omega⟩
  | succ n ih =>
      intro x hx hbound
      by_cases heq : x = v
      · exact ⟨fun _ => v, heq.symm, rfl, fun _ _ => Or.inl rfl⟩
      · obtain ⟨y, hy, hedge, hdrop⟩ := hnext x hx heq
        obtain ⟨w, hw0, hwn, hws⟩ := ih y hy (by omega)
        let w' : ℕ → E := fun k => match k with
          | 0 => x
          | k + 1 => w k
        refine ⟨w', rfl, hwn, ?_⟩
        intro k hk
        cases k with
        | zero => exact Or.inr (by simpa only [w', hw0] using hedge)
        | succ k => exact hws k (by omega)
end HirschBoxSlice
#print axioms HirschBoxSlice.walk_of_strict_potential
