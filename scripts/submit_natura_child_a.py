#!/usr/bin/env python3
"""Bundle, locally re-check, and submit the exact Polynomial-Hirsch Child A proof.

Nothing is sent unless the flattened proof compiles in the pinned environment,
prints a clean axiom audit for `solution`, and the live target has the expected
name/environment. Credentials remain in the environment and are never logged.
"""
from __future__ import annotations

import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.parse

from bundle_natura_child_a import build_flat
from publish_natura_helpers import API

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "child_a_submission"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TARGET_ID = "9b9a6f06-d05d-41ba-980f-04b905e67562"
TARGET_NAME = "Hirsch.cubic_circuit_walk_bound"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

EXPLANATION = r"""We prove the cubic circuit-walk bound with the explicit constant $C=17$.

First pass to an irredundant strictly feasible row presentation of the same bounded polytope. Boundedness makes the row-evaluation map injective, so slack coordinates identify the row-circuit walk with a circuit walk in a nonnegative affine slice. Recenter this slice at the target vertex $v$.

For any displacement in the slice direction space, a support-minimality argument gives an exact conformal decomposition into at most the ambient number $n$ of elementary directions. During a phase we track the finite set of coordinates that have made permanent progress: target-zero coordinates already equal to zero and target-positive coordinates already below the threshold $M v_i$, where $M=\max(2,n)$.

A weighted potential on the target-zero coordinates is
$$
\Phi_r(x)=\sum_{v_i=0}\frac{x_i}{r_i},
$$
with zero weight when $r_i=0$. As long as no progress event occurs, equality of the phase-progress sets guarantees that every live denominator is positive. From a conformal decomposition of $v-x$, averaging selects an elementary direction carrying at least a $1/M$ fraction of the potential decrease. Its positive maximal feasible augmentation has multiplier between $1$ and $M$, preserves all already-achieved progress, and contracts the potential by at least
$$
\Phi_r(x^+)\le \left(1-\frac1M\right)\Phi_r(x).
$$

After at most $4M^2$ such norm steps without a progress event, a rational contraction estimate gives
$$
\Phi_r(x)\le \frac{1}{2M^2}.
$$
At that threshold we use a support-safe elimination displacement. Choose the largest live ratio $\rho=x_q/r_q$ and set
$$
\lambda=\frac1{2M},\qquad
\eta=\frac{(1-\lambda)\rho}{1-\rho},\qquad
\delta=\lambda(v-x)+\eta(x-r).
$$
The small-potential bound implies $M\eta\le\lambda$. A conformal elementary piece of $\delta$, chosen by averaging at coordinate $q$, has a strictly negative $q$-component. Its positive maximal feasible augmentation is bounded by $M$. The checked scalar inequalities show that already-trapped target-positive coordinates remain trapped and cannot fall below half their previous value, while target-zero coordinates never increase. The coordinate that blocks the maximal step therefore creates a new permanent progress event.

Thus every phase uses at most $4M^2+1$ circuit steps and either reaches $v$ or strictly enlarges a subset of the $n$ coordinates. There are at most $n$ phases. Hence the standard-slice walk has length at most
$$
n(4M^2+1)\le 17n^3.
$$
The zero-dimensional case is handled separately. Finally, the slack/walk equivalence transfers this walk back to the irredundant H-presentation, and stationary padding raises the budget from $17m^3$ to the required $17(m+d)^3$."""


def write(name: str, obj) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n")


def wait_verdict(api: API, submission_id: str, timeout: int = 900):
    end = time.monotonic() + timeout
    terminal = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
    while True:
        state = api.request("/verify?" + urllib.parse.urlencode({"submission_id": submission_id}))
        write("verify-status.json", state)
        if state.get("status") in terminal:
            return state
        if time.monotonic() >= end:
            return state
        time.sleep(8)


def run_checked(cmd: list[str], log_name: str, error: str) -> str:
    run = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (OUT / log_name).write_text(run.stdout)
    print(run.stdout)
    if run.returncode:
        raise RuntimeError(error)
    return run.stdout


def main() -> int:
    OUT.mkdir(exist_ok=True)
    proof, order = build_flat("NaturaChildACandidate")
    proof_path = OUT / "solution.lean"
    proof_path.write_text(proof)
    write("bundle.json", {"modules": order, "bytes": len(proof.encode())})

    lake = Path.home() / ".elan/bin/lake"

    # A raw `lake env lean path/to/solution.lean` resolves imports from built
    # `.olean`s, not directly from this repository's source tree.  Build the
    # public local Definition modules imported by the flattened proof first;
    # this mirrors the dependency modules Prove2Me supplies server-side.
    definition_imports = sorted(set(re.findall(
        r"^\s*import\s+(Definitions\.[A-Za-z0-9_.]+)\s*$", proof, flags=re.M
    )))
    if definition_imports:
        run_checked(
            [str(lake), "build", *definition_imports],
            "definition-build.log",
            "failed to build flattened proof's public Definition imports",
        )
    write("definition-imports.json", definition_imports)

    checked_stdout = run_checked(
        [str(lake), "env", "lean", "-DautoImplicit=false", str(proof_path)],
        "local-check.log",
        "flattened Child-A proof failed local Lean compilation",
    )
    if "sorryAx" in checked_stdout:
        raise RuntimeError("flattened Child-A proof depends on sorryAx")
    m = re.search(r"'solution' depends on axioms:\s*\[([^]]*)\]", checked_stdout)
    if not m:
        raise RuntimeError("missing solution axiom audit")
    axioms = {x.strip() for x in m.group(1).split(",") if x.strip()}
    if not axioms <= ALLOWED_AXIOMS:
        raise RuntimeError("unexpected solution axioms: " + repr(sorted(axioms)))

    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)
    target = api.request("/theorems/" + TARGET_ID)
    write("target.json", {k: target.get(k) for k in
                          ("theorem_id", "theorem_name", "status", "mathlib_rev", "formal_statement")})
    if target.get("theorem_name") != TARGET_NAME:
        raise RuntimeError("target theorem name changed")
    if target.get("mathlib_rev") != PIN:
        raise RuntimeError("target environment changed")
    if target.get("status") == "Proved":
        print(json.dumps({"already_proved": TARGET_ID}, indent=2))
        return 0
    if target.get("status") != "Open":
        raise RuntimeError("unexpected target status: " + repr(target.get("status")))

    submitted = api.verify(TARGET_ID, proof, EXPLANATION)
    write("submitted.json", submitted)
    submission_id = submitted["submission_id"]
    verdict = wait_verdict(api, submission_id)
    final = api.request("/theorems/" + TARGET_ID)
    result = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "theorem_id": TARGET_ID,
        "submission_id": submission_id,
        "verdict": verdict.get("status"),
        "theorem_status": final.get("status"),
        "platform_version": getattr(api, "version", None),
    }
    write("result.json", result)
    print(json.dumps(result, indent=2))
    return 0 if verdict.get("status") == "ACCEPTED" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        OUT.mkdir(exist_ok=True)
        write("failure.json", {"type": type(exc).__name__, "message": str(exc)[:1200]})
        print(f"ERROR: {exc}", file=sys.stderr)
        raise
