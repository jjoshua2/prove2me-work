#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "public_geodesic_packet"
OUT.mkdir(exist_ok=True)

HEADER = """import Mathlib
import Definitions.Def_Hirsch_model

set_option maxHeartbeats 8000000
noncomputable section

"""

def body(path: str) -> str:
    lines = (ROOT / path).read_text().splitlines()
    out = []
    for ln in lines:
        if ln.startswith("import "):
            continue
        if ln.startswith("#print axioms "):
            continue
        out.append(ln)
    return "\n".join(out).strip() + "\n"

product = body("Solutions/PolynomialProductWalk.lean")
adj = body("Solutions/PolynomialAdjEndpoints.lean")
splice = body("Solutions/PolynomialFaceReentrySplice.lean")
cover = body("Solutions/PolynomialGeodesicFaceCover.lean")
tail = body("Solutions/PolynomialGeodesicFaceTail.lean")

reentry_wrapper = r'''
open scoped RealInnerProductSpace
open Set Hirsch

theorem solution
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F)
    (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P)
    (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' (s + B + (L - t)) = v ∧
      ∀ j < s + B + (L - t),
        w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by
  exact HirschFaceSplice.splice_reentry_through_extreme_face
    d L B s t P F hF hFD u v w hw0 hwL hwstep
    hst htL hsP htP hsF htF

#print axioms solution
'''

# Expand the connectivity hypothesis in the public theorem statement so the
# platform theorem does not depend on our local Walk abbreviation.
tail_wrapper = r'''
open scoped RealInnerProductSpace
open Set Hirsch

theorem solution
    {ι : Type*} (d B K : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) B)
    (htails : ∀ u ∈ extremePoints ℝ P,
      ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card ≤ K ∧
        ∀ x ∈ extremePoints ℝ P, (∀ i, u ∈ F i → x ∉ F i) → x ∈ T)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P (B + K) := by
  apply HirschFaceSplice.diamLE_of_disjoint_face_tail_bound
    d B K P F hF hFD htails
  intro u hu v hv
  obtain ⟨L, w, h0, hL, hs⟩ := hconnect u hu v hv
  exact ⟨L, w, h0, hL, hs⟩

#print axioms solution
'''

(OUT / "reentry_solution.lean").write_text(HEADER + product + "\n" + splice + "\n" + reentry_wrapper)
(OUT / "tail_solution.lean").write_text(
    HEADER + product + "\n" + adj + "\n" + splice + "\n" + cover + "\n" + tail + "\n" + tail_wrapper
)
print(OUT)
