#!/usr/bin/env python3
from __future__ import annotations
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "public_geodesic_face_cover_packet"
OUT.mkdir(exist_ok=True)

HEADER = """import Mathlib
import Definitions.Def_Hirsch_model

set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] Classical.propDecidable

"""

def body(path: str) -> str:
    lines = (ROOT / path).read_text().splitlines()
    out = []
    for ln in lines:
        if ln.startswith("import ") or ln.startswith("#print axioms "):
            continue
        out.append(ln)
    return "\n".join(out).strip() + "\n"

wrapper = r'''
open scoped RealInnerProductSpace BigOperators
open Set Hirsch

theorem solution
    {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ (Finset.univ.filter (fun i => x ∈ F i)).card)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P ((∑ i, (B i + 1)) / q - 1) := by
  apply HirschFaceSplice.diamLE_of_face_cover d q hq P F B hF hFD hcover
  intro u hu v hv
  obtain ⟨L, w, hw0, hwL, hs⟩ := hconnect u hu v hv
  exact ⟨L, w, hw0, hwL, hs⟩

#print axioms solution
'''

pieces = [
    body("Solutions/PolynomialProductWalk.lean"),
    body("Solutions/PolynomialAdjEndpoints.lean"),
    body("Solutions/PolynomialFaceReentrySplice.lean"),
    body("Solutions/PolynomialGeodesicFaceCover.lean"),
]
text = HEADER + "\n".join(pieces) + "\n" + wrapper
path = OUT / "solution.lean"
path.write_text(text)
manifest = {
    "mathlib_rev":"c5ea00351c28e24afc9f0f84379aa41082b1188f",
    "solution_sha256":hashlib.sha256(text.encode()).hexdigest(),
    "bytes":len(text.encode()),
}
(OUT/"manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
print(json.dumps(manifest))
