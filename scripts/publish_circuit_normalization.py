#!/usr/bin/env python3
"""Publish and prove the admission-free circuit-presentation normalization lemma.

The theorem and solution are generated from the already-compiled PR #9 source.
No credential or bearer token is printed.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.parse
import uuid

from circuit_leaf_api import API, PIN, normal, rows, wait

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "circuit_normalization_packet"
NAME = "HirschCircuit.exists_irredundant_strict_model"
PREAMBLE = (
    "import Definitions.Def_Hirsch_circuit_model\n"
    "set_option autoImplicit false\n"
    "set_option maxHeartbeats 2000000\n"
    "open scoped RealInnerProductSpace\n"
    "open Hirsch\n"
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def build_exact_sources() -> tuple[str, str]:
    source = (ROOT / "Solutions/CircuitIrredundantModel.lean").read_text(encoding="utf-8")
    marker = "theorem exists_irredundant_strict_model"
    if marker not in source:
        raise RuntimeError("normalization theorem not found in reviewed source")
    tail = source.split(marker, 1)[1]
    if ":= by" not in tail:
        raise RuntimeError("normalization theorem has unexpected syntax")
    signature, proof_tail = tail.split(":= by", 1)
    proof = proof_tail.split("#print axioms", 1)[0].rstrip()
    if re.search(r"\b(sorry|admit|native_decide)\b", proof):
        raise RuntimeError("admission detected in normalization proof")

    formal_statement = f"theorem {NAME}" + signature.rstrip() + " := by sorry"
    solution = PREAMBLE + "\ntheorem solution" + signature.rstrip() + " := by" + proof + "\n\n#print axioms solution\n"
    return formal_statement, solution


def compile_and_audit(solution: str) -> None:
    OUT.mkdir(exist_ok=True)
    path = OUT / "solution.lean"
    path.write_text(solution, encoding="utf-8")
    run = subprocess.run(
        [str(Path.home() / ".elan/bin/lake"), "env", "lean", str(path)],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=295,
    )
    (OUT / "compile.log").write_text(run.stdout, encoding="utf-8")
    print(run.stdout)
    if run.returncode:
        raise RuntimeError("generated exact solution failed local Lean compilation")
    match = re.search(r"'solution' depends on axioms:\s*\[([^]]*)\]", run.stdout)
    if not match:
        raise RuntimeError("generated solution did not emit an axiom report")
    axioms = {part.strip() for part in match.group(1).split(",") if part.strip()}
    unexpected = axioms - ALLOWED_AXIOMS
    if unexpected:
        raise RuntimeError("unexpected axioms in generated solution: " + repr(sorted(unexpected)))
    print(
        "NORMALIZATION_LOCAL_AUDIT",
        json.dumps(
            {
                "compiled": True,
                "sha256": hashlib.sha256(solution.encode()).hexdigest(),
                "axioms": sorted(axioms),
            }
        ),
    )


def verify(api: API, theorem_id: str, proof: str, explanation: str) -> dict:
    boundary = "----Prove2Me" + uuid.uuid4().hex
    parts: list[str] = []
    for name, value in [
        ("theorem_id", theorem_id),
        ("proof_type", "prove"),
        ("explanation", explanation),
    ]:
        parts.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n'
        )
    parts.append(
        f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
        f"Content-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n"
    )
    return api.request(
        "/verify",
        "".join(parts).encode(),
        "POST",
        "multipart/form-data; boundary=" + boundary,
    )


def main() -> int:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY is unavailable")

    formal_statement, solution = build_exact_sources()
    compile_and_audit(solution)

    api = API(key)
    api.refresh()
    print("AUTH ok version=" + str(api.version))

    existing = rows(api, theorem_name=NAME)
    theorem_id: str
    if existing:
        if len(existing) != 1:
            raise RuntimeError("normalization theorem name collision")
        item = existing[0]
        if normal(item.get("formal_statement", "")) != normal(formal_statement):
            raise RuntimeError("existing normalization theorem has a different formal statement")
        theorem_id = item["theorem_id"]
        print("NORMALIZATION_TARGET existing status=" + str(item.get("status")) + " id=" + theorem_id)
    else:
        problem = {
            "theorem_name": NAME,
            "theorem_title": "Irredundant strict presentation from separated feasible endpoints",
            "formal_statement": formal_statement,
            "preamble": PREAMBLE.rstrip(),
            "natural_language_statement": (
                "Let an $n$-row H-polyhedron contain feasible points $u$ and $v$. Assume that every nonzero "
                "describing row is not tight at both endpoints. Then some subfamily of $m\\le n$ original rows "
                "defines exactly the same feasible set, is irredundant, and admits a point strictly satisfying "
                "every retained inequality.\n\nThe retained family is chosen with minimum cardinality. Row-deletion "
                "witnesses give irredundancy, and the midpoint of $u$ and $v$ is strictly feasible for every "
                "retained nonzero row. This normalization is useful before translating an H-polytope into slack "
                "coordinates for circuit-walk arguments."
            ),
            "source": (
                "Elementary normalization lemma used in the circuit-routing reduction for the Polynomial Hirsch mission; "
                "the downstream slack-coordinate motivation is Bento Natura, Circuit Diameter of Polyhedra is Strongly "
                "Polynomial, arXiv:2602.06958v2, Section 1.1 and Theorem 3.1."
            ),
            "tags": ["convex-geometry", "polytopes"],
        }
        queued = api.request(
            "/submit-problem",
            {"env": PIN, "private": False, "problems": [problem]},
            "POST",
        )
        if queued.get("errors") or len(queued.get("jobs", [])) != 1:
            raise RuntimeError("normalization publication did not return exactly one job")
        status = wait(
            api,
            "/publish-jobs/" + queued["jobs"][0]["job_id"],
            {"PUBLISHED", "FAILED", "ERROR"},
            seconds=280,
        )
        print("NORMALIZATION_PUBLISH", json.dumps({k: status.get(k) for k in ("status", "theorem_id", "error_message")}))
        if status.get("status") != "PUBLISHED":
            raise RuntimeError("normalization theorem publication failed")
        theorem_id = status["theorem_id"]

    live = api.request("/theorems/" + theorem_id)
    if live.get("status") == "Proved":
        print("NORMALIZATION_DONE already_proved=true id=" + theorem_id)
        return 0

    explanation = (
        "Choose, among all subfamilies of the original inequalities defining the same feasible set, one of minimum "
        "cardinality. Every retained row is essential: otherwise removing it would yield a smaller defining family. "
        "The corresponding row-deletion witness violates that row while satisfying all other retained rows, which is "
        "exactly irredundancy.\n\nA retained row cannot have zero normal, because its deletion witness would "
        "strictly violate the row while the feasible endpoint $u$ satisfies it. Finally, endpoint separation says each "
        "retained nonzero row is strict at $u$ or at $v$. Since both endpoints are feasible, their midpoint is therefore "
        "strict for every retained row. Reindexing the minimum family by `Fin m` gives $m\\le n$ and preserves the "
        "original H-polyhedron exactly."
    )
    queued = verify(api, theorem_id, solution, explanation)
    submission_id = queued["submission_id"]
    verdict = wait(
        api,
        "/verify?" + urllib.parse.urlencode({"submission_id": submission_id}),
        {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"},
        seconds=300,
    )
    print(
        "NORMALIZATION_VERDICT",
        json.dumps(
            {
                "theorem_id": theorem_id,
                "submission_id": submission_id,
                "status": verdict.get("status"),
                "error_message": verdict.get("error_message", ""),
            }
        ),
    )
    if verdict.get("status") != "ACCEPTED":
        raise RuntimeError("normalization proof was not ACCEPTED")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print("NORMALIZATION_ERROR " + type(exc).__name__ + ": " + str(exc), file=sys.stderr)
        raise
