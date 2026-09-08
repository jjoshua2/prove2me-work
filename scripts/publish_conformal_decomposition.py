#!/usr/bin/env python3
"""Compile/audit a standalone closed proof before publishing one reusable lemma.

The public statement uses the existing slack model and explicit conformality,
so no additional definition or unproved child is introduced. Credentials remain
in environment/memory, and the imported HTTP client rejects redirects.
"""
from __future__ import annotations

import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import sys

import publish_natura_more as publish
from publish_natura_helpers import API

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "conformal_publication"
NAME = "HirschCircuit.elementary_conformal_decomposition_ambient_bound"
BINDERS = """{n : ℕ}
    (K : Submodule ℝ (Fin n → ℝ)) (z : Fin n → ℝ) (hz : z ∈ K) :
    ∃ gs : List (Fin n → ℝ), gs.length ≤ n ∧
      (∀ g ∈ gs, HirschCircuit.IsElementaryIn K g ∧
        ∀ i, 0 ≤ g i * z i ∧ |g i| ≤ |z i|) ∧ gs.sum = z"""
FORMAL = "theorem " + NAME + " " + BINDERS + " := by sorry"
PREAMBLE = "import Definitions.Def_Hirsch_circuit_slack_model\nset_option autoImplicit false\n"
EXPLANATION = (
    "Choose a nonzero conformal vector with minimal support cardinality. "
    "A proper-support subspace direction would allow a half-scaled perturbation "
    "that cancels one coordinate without changing the orthant, contradicting "
    "minimality. Thus the vector is elementary in the original subspace. "
    "Rescale it until some coordinate of the residual vanishes; the residual "
    "remains conformal. Strong induction on support cardinality yields an exact "
    "sum of at most the support size, hence at most n, elementary pieces. "
    "This proves only a decomposition, not a maximal circuit-walk or graph-diameter bound."
)


def main() -> int:
    OUT.mkdir(exist_ok=True)
    chunks = [PREAMBLE]
    sources = ["CircuitConformalBasics", "CircuitConformalPiece", "CircuitConformalDecomposition"]
    for module in sources:
        text = (ROOT / "Solutions" / (module + ".lean")).read_text()
        # Only dependency imports and audit commands are removed. The checked
        # definitions and proofs themselves are preserved byte-for-byte.
        text = "\n".join(line for line in text.splitlines()
                         if not line.startswith("import ") and not line.startswith("#print axioms"))
        chunks.append(text)
    chunks.append("theorem solution " + BINDERS + " := by\n"
                  "  exact HirschCircuit.exists_elementary_conformal_decomposition_le_n K z hz\n"
                  "#print axioms solution\n")
    proof = "\n\n".join(chunks)
    if re.search(r"\b(sorry|admit|axiom)\b", proof):
        raise RuntimeError("unexpected admission token in proof")
    proof_path = ROOT / "Solutions" / "ConformalDecompositionPublication.lean"
    proof_path.write_text(proof)
    # Build just the existing published definitions, then audit the flattened
    # standalone solution so server-side verification has no local imports.
    lake = str(Path.home() / ".elan/bin/lake")
    subprocess.run([lake, "build", "Definitions.Def_Hirsch_circuit_slack_model"], cwd=ROOT, check=True)
    checked = subprocess.run([lake, "env", "lean", str(proof_path)], cwd=ROOT,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (OUT / "build.log").write_text(checked.stdout)
    print(checked.stdout)
    if checked.returncode or "sorryAx" in checked.stdout:
        raise RuntimeError("standalone proof did not pass its compile/axiom gate")
    if "'solution' depends on axioms:" not in checked.stdout:
        raise RuntimeError("missing solution axiom audit")
    (OUT / "solution.lean").write_text(proof)
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)
    publish.OUT = OUT
    publish.EXPLANATIONS[NAME] = EXPLANATION
    spec = {
        "name": NAME,
        "title": "Conformal elementary decomposition with an ambient-coordinate bound",
        "formal": FORMAL,
        "preamble": PREAMBLE,
        "natural": "Every vector $z$ in a real linear subspace $K\\subseteq\\mathbb R^n$ can be written as a sum of at most $n$ nonzero support-minimal vectors of $K$. Each summand has the same closed-orthant signs as $z$ and is coordinatewise no larger in absolute value. The zero vector is represented by the empty sum. This ambient-coordinate bound does not assert a maximal circuit-walk bound or the sharper dimension bound.",
        "source": "Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Definition 2.1 and Lemma 2.2. Matrix-free ambient-coordinate relaxation, proved by support-cardinality induction; no novelty claim.",
        "tags": ["polyhedra", "circuits", "linear-algebra", "conformal-decomposition"],
        "proof": proof_path,
    }
    result = publish.publish_one(api, spec)
    state = {"checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
             "name": NAME, "env": publish.PIN, "result": result}
    (OUT / "status.json").write_text(json.dumps(state, indent=2) + "\n")
    print(json.dumps(state))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        OUT.mkdir(exist_ok=True)
        failure = {"type": type(exc).__name__,
                   "message": str(exc)[:700] if isinstance(exc, RuntimeError) else "compile or publication failed"}
        (OUT / "failure.json").write_text(json.dumps(failure, indent=2) + "\n")
        print(json.dumps(failure))
        sys.exit(2)
