import Mathlib

/-!
# Exact dimension mass from a non-reentering portal signature chain

For a simple polytope, the number of newly active facets between vertices is
the dimension of their smallest common face. A geodesic through ALL intrinsic
facets makes every facet's portal appearances contiguous. Entry counts then
telescope to the union of signatures, giving

    sum(child dimensions) = parent dimension + visited neutral facets.

This file proves the finite-set core, not the entire simple-polytope interface.
New proof candidate; separate Lean compilation/axiom audit required.
-/
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschPortalDebt
variable {α : Type*} [DecidableEq α]

/-- Facets entered in one transition. Uniform vertex rank identifies this
with common-carrier dimension; it is a directed set metric in general. -/
def entries (a b : Finset α) : ℕ := (b \ a).card

lemma union_card_entries (a b : Finset α) : (a ∪ b).card = a.card + entries a b := by
  have hd : Disjoint a (b \ a) := by
    apply Finset.disjoint_left.mpr
    intro x hxa hxb
    exact (Finset.mem_sdiff.mp hxb).2 hxa
  have he : a ∪ b = a ∪ (b \ a) := by ext x; simp <;> tauto
  rw [he, Finset.card_union_of_disjoint hd]
  rfl

lemma entries_triangle (a b c : Finset α) : entries a c ≤ entries a b + entries b c := by
  have hsub : c \ a ⊆ (b \ a) ∪ (c \ b) := by
    intro x hx
    obtain ⟨hxc,hxa⟩ := Finset.mem_sdiff.mp hx
    by_cases hxb : x ∈ b
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxb,hxa⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxc,hxb⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Any facet seen in the next signature and already in history must still
be active in the current signature. This is a directly checkable non-reentry
condition, not a route-length hypothesis. -/
def FreshChain (seen current : Finset α) : List (Finset α) → Prop
  | [] => True
  | b :: bs => (b ∩ seen ⊆ current) ∧ FreshChain (seen ∪ b) b bs

def visited (seen : Finset α) : List (Finset α) → Finset α
  | [] => seen
  | b :: bs => visited (seen ∪ b) bs

def entryCost (current : Finset α) : List (Finset α) → ℕ
  | [] => 0
  | b :: bs => entries current b + entryCost b bs

lemma entries_eq_fresh (seen current next : Finset α)
    (hcur : current ⊆ seen) (hfresh : next ∩ seen ⊆ current) :
    entries current next = entries seen next := by
  unfold entries
  congr 1
  ext x
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨hx,hn⟩
    exact ⟨hx,fun hs => hn (hfresh (Finset.mem_inter.mpr ⟨hx,hs⟩))⟩
  · rintro ⟨hx,hn⟩
    exact ⟨hx,fun hc => hn (hcur hc)⟩

/-- No reentry means each new label is charged once even in a long chain. -/
theorem fresh_chain_cost (seen current : Finset α) (tail : List (Finset α))
    (hcur : current ⊆ seen) (hfresh : FreshChain seen current tail) :
    entryCost current tail + seen.card = (visited seen tail).card := by
  induction tail generalizing seen current with
  | nil => simp [entryCost,visited]
  | cons b bs ih =>
    obtain ⟨hf,hrest⟩ := hfresh
    have hentry := entries_eq_fresh seen current b hcur hf
    have hcard := union_card_entries seen b
    have ht := ih (seen ∪ b) b Finset.subset_union_right hrest
    simp only [entryCost,visited]
    omega

/-- Separate unavoidable endpoint entries from the genuinely neutral labels. -/
theorem signature_mass_eq_endpoint_plus_neutral
    (a b all : Finset α) (cost : ℕ) (ha : a ⊆ all) (hb : b ⊆ all)
    (hcost : cost + a.card = all.card) :
    cost = entries a b + (all \ (a ∪ b)).card := by
  have hu : a ∪ b ⊆ all := Finset.union_subset ha hb
  have hc := Finset.card_sdiff_add_card_eq_card hu
  have he := union_card_entries a b
  omega

/-- At separated simple endpoints of intrinsic rank d, at most m-2d
neutral facets are available. The resulting child dimension mass is <=m-d. -/
theorem separated_signature_mass_le_excess
    (a b all universe : Finset α) (d cost : ℕ)
    (ha : a ⊆ all) (hb : b ⊆ all) (hAll : all ⊆ universe)
    (hda : a.card = d) (_hdb : b.card = d)
    (_hsep : Disjoint a b) (hcost : cost + a.card = all.card) :
    cost ≤ universe.card - d := by
  have hcard := Finset.card_le_card hAll
  omega

#print axioms entries_triangle
#print axioms fresh_chain_cost
#print axioms signature_mass_eq_endpoint_plus_neutral
#print axioms separated_signature_mass_le_excess
end HirschPortalDebt
