#!/usr/bin/env python3
"""Submit a fully compiled standalone proof of the existing, unchanged Child A.

No theorem or definition is created by this script. It only reads the target,
checks the pinned local proof and its axiom dependency list, and invokes the
normal proof-verification endpoint for that target. No credentials are saved.
"""
from __future__ import annotations

import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

from publish_natura_helpers import API, wait_verdict

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "child_a_submission"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TARGET = "9b9a6f06-d05d-41ba-980f-04b905e67562"
NAME = "Hirsch.cubic_circuit_walk_bound"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPLANATION = r"""We prove a matrix-free standard-form bound first, then apply the exact existing slack-coordinate and irredundant-presentation bridge.

For Q=(v+K) intersected with the nonnegative orthant and M=max(2,n), track a coordinate as completed when either its target value is zero and its current value is zero, or its positive target value v_i traps the current value below M v_i. Reset the phase reference r whenever this combined progress set grows. Thus target-zero support loss is an event, not an invariant silently discarded.

While the progress set is unchanged, use W=sum_{v_i=0,r_i!=0} x_i/r_i. Extremality of v implies W>0 unless x=v. A conformal decomposition of v-x into at most n elementary vectors supplies a piece with score at least W/M. Its genuine maximal augmentation has 1<=alpha<=M, preserves all progress and contracts W by at least 1-1/M. After at most 4 M^2 such steps, either a phase event already occurred or W<=1/(2M^2).

In the latter case choose any still-positive target-zero coordinate q and rho=x_q/r_q. Put lambda=1/(2M) and eta=(1-lambda)rho/(1-rho). The displacement delta=lambda(v-x)+eta(x-r) belongs to K, has delta_q=-x_q and is nonpositive on every target-zero coordinate. A conformal elementary piece selected by averaging at q has a positive maximal augmentation alpha<=M. Existing trapped coordinates stay between half their current value and M times their target, so the blocking coordinate must yield strict new progress. This argument does not assume a source theorem or a progress-step existence oracle.

Every phase therefore reaches v or strictly increases a finite set of n coordinates within 4M^2+1 steps. Induction on the remaining coordinate budget yields n(4M^2+1)<=17n^3 steps. The n=0 case is stationary. Recentring preserves the exact feasible slice and circuit-step relation. Finally the proved slack identification transfers this to the original H-presentation, redundant rows are removed with the already-proved exact preprocessing theorem, and padding gives the requested C(m+d)^3 budget. All directions remain elementary in the original row/slack subspace and all nonstationary steps are truly maximal.

This is Child A only: it does not assert that circuit steps are edges, does not prove the separate edge-refinement child, and does not prove the Polynomial Hirsch Conjecture. The bound is a source-backed formalization with a support-safe adaptation, not a claim of a new circuit-diameter theorem."""


def save(name: str, value) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def standalone() -> tuple[str, list[str]]:
    seen: set[str] = set()
    external: set[str] = set()
    chunks: list[str] = []
    order: list[str] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        if not module.startswith("Solutions."):
            raise RuntimeError("only local solution modules may be inlined")
        seen.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        text = path.read_text()
        for line in text.splitlines():
            if line.startswith("import "):
                for dep in line[len("import "):].split():
                    if dep.startswith("Solutions."):
                        visit(dep)
                    elif dep.startswith("Theorems."):
                        raise RuntimeError("theorem import forbidden in direct Child A proof: " + dep)
                    elif dep == "Mathlib" or dep.startswith("Mathlib.") or dep.startswith("Definitions."):
                        external.add(dep)
                    else:
                        raise RuntimeError("unexpected import " + dep)
        body = "\n".join(line for line in text.splitlines()
                         if not line.startswith("import ") and not line.startswith("#print axioms"))
        chunks.append(body)
        order.append(module)

    visit("Solutions.CircuitPhaseRoute")
    target_text = (ROOT / "Theorems/Thm_Hirsch_cubic_circuit_walk_bound.lean").read_text()
    match = re.search(r"theorem\s+Hirsch\.cubic_circuit_walk_bound\s*:\s*(.*?)\s*:=\s*by\s+sorry", target_text, re.S)
    if not match:
        raise RuntimeError("expected local Child A target signature not found")
    target_type = match.group(1)
    proof = "\n".join("import " + dep for dep in sorted(external)) + "\n\n"
    proof += "\n\n".join(chunks)
    proof += "\n\nopen scoped RealInnerProductSpace\n"
    proof += "theorem solution :\n" + target_type + " := by\n"
    proof += "  exact HirschCircuit.cubic_circuit_walk_bound_of_standard HirschCircuit.standard_cubic_circuit_bound\n"
    proof += "#print axioms solution\n"
    return proof, order


def main() -> int:
    OUT.mkdir(exist_ok=True)
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)
    before = api.request("/theorems/" + TARGET)
    if before.get("theorem_name") != NAME or before.get("mathlib_rev") != PIN:
        raise RuntimeError("target name or pinned environment changed")
    save("target-before.json", {k: before.get(k) for k in ["theorem_id", "theorem_name", "mathlib_rev", "status", "formal_statement"]})
    state = {"started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
             "target": TARGET, "name": NAME, "env": PIN, "status_before": before.get("status"),
             "submitted": False}
    save("status.json", state)
    if before.get("status") == "Proved":
        state["status_after"] = "Proved"
        state["verification_skipped"] = "already proved"
        save("status.json", state)
        print(json.dumps(state))
        return 0
    if before.get("status") != "Open":
        raise RuntimeError("target is not Open or Proved")
    proof, order = standalone()
    proof_path = ROOT / "Solutions/ChildAStandalone.lean"
    proof_path.write_text(proof)
    (OUT / "solution.lean").write_text(proof)
    save("source-manifest.json", {"inline_order": order,
                                  "sha256": hashlib.sha256(proof.encode()).hexdigest(),
                                  "source_commit": os.environ.get("GITHUB_SHA")})
    lake = str(Path.home() / ".elan/bin/lake")
    checked = subprocess.run([lake, "env", "lean", str(proof_path)], cwd=ROOT,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=600)
    (OUT / "standalone-build.log").write_text(checked.stdout)
    print(checked.stdout)
    if checked.returncode or "sorryAx" in checked.stdout:
        raise RuntimeError("standalone proof did not pass compile/no-admission gate")
    matches = re.findall(r"'solution' depends on axioms:\s*\[([^\]]*)\]", checked.stdout, re.S)
    if len(matches) != 1:
        raise RuntimeError("missing or ambiguous final theorem axiom audit")
    axioms = {a.strip() for a in matches[0].split(",") if a.strip()}
    if not axioms.issubset(ALLOWED):
        raise RuntimeError("nonstandard axiom dependency")
    state["axioms"] = sorted(axioms)
    state["standalone_compiled"] = True
    save("status.json", state)
    queued = api.verify(TARGET, proof, EXPLANATION)
    save("proof-queued.json", queued)
    state["submission_id"] = queued["submission_id"]
    state["submitted"] = True
    save("status.json", state)
    verdict = wait_verdict(api, queued["submission_id"], timeout=900)
    save("proof-verdict.json", verdict)
    after = api.request("/theorems/" + TARGET)
    state["verdict"] = verdict.get("status")
    state["status_after"] = after.get("status")
    state["finished_at"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save("status.json", state)
    print(json.dumps(state))
    return 0 if state["verdict"] == "ACCEPTED" and state["status_after"] == "Proved" else 3


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        failure = {"type": type(exc).__name__, "message": str(exc)[:700] if isinstance(exc, RuntimeError) else "proof validation or submission failed"}
        save("failure.json", failure)
        print(json.dumps(failure))
        sys.exit(2)
