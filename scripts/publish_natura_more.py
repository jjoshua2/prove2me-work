#!/usr/bin/env python3
"""Publish and prove additional already-audited Natura/Hirsch helper lemmas."""
from __future__ import annotations

import datetime
import json
import os
from pathlib import Path
import re
import time
import urllib.parse

from publish_natura_helpers import API, wait_job, wait_verdict

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "natura_more_publish_packet"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"

SPECS = [
    {
        "name": "HirschCircuit.rowCircuitWalk_mono",
        "title": "Padded row-circuit walks are monotone in the budget",
        "formal": """namespace HirschCircuit

theorem rowCircuitWalk_mono {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {L M : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (h : RowCircuitWalk a b L u v) (hLM : L ≤ M) :
    RowCircuitWalk a b M u v := by sorry

end HirschCircuit""",
        "preamble": """import Definitions.Def_Hirsch_circuit_model

set_option autoImplicit false
open Hirsch
""",
        "natural": "A padded maximal row-circuit walk of length at most $L$ can be represented with any larger budget $M\\ge L$ by retaining the original walk through time $L$ and then remaining at its final endpoint. This establishes monotonicity of the padded circuit-walk predicate in its step budget.",
        "source": "Formalization helper for the Polynomial Hirsch circuit reduction; follows directly from the padded-walk definition in Hirsch_circuit_model.",
        "tags": ["hirsch-conjecture", "polyhedra", "circuits", "walks"],
        "proof": ROOT / "Solutions/Sol_HirschCircuit_rowCircuitWalk_mono.lean",
    },
    {
        "name": "HirschCircuit.exists_positive_maximal_nonnegative_step",
        "title": "Existence of a positive maximal nonnegative augmentation",
        "formal": """namespace HirschCircuit

theorem exists_positive_maximal_nonnegative_step {n : ℕ}
    (x g : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hzero : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ α : ℝ, 0 < α ∧ (∀ i, 0 ≤ x i + α * g i) ∧
      (∃ q, g q < 0 ∧ x q + α * g q = 0) ∧
      ∀ β : ℝ, α < β → ∃ i, x i + β * g i < 0 := by sorry

end HirschCircuit""",
        "preamble": """import Mathlib

set_option autoImplicit false
""",
        "natural": "Let $x\\in\\mathbb R^n_{\\ge0}$ and let $g$ be a direction that is nonnegative at every coordinate where $x$ is zero, but is negative in at least one coordinate. Then there is a strictly positive maximal step length $\\alpha$: $x+\\alpha g$ remains nonnegative, at least one decreasing coordinate becomes zero, and every larger step violates nonnegativity. The step is the minimum blocking ratio over the finitely many negative coordinates of $g$.",
        "source": "Elementary finite-minimum maximal-augmentation lemma used in the support-safe adaptation of Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Section 1.1 and Algorithm 1.",
        "tags": ["polyhedra", "circuits", "augmentation", "nonnegative-orthant"],
        "proof": ROOT / "Solutions/Sol_HirschCircuit_exists_positive_maximal_nonnegative_step.lean",
    },
]

EXPLANATIONS = {
    "HirschCircuit.rowCircuitWalk_mono": "Given a padded row-circuit walk of length $L$ and $L\\le M$, define the new walk at time $j$ to be the old walk at $\\min(j,L)$. Before time $L$ every original circuit step is unchanged; from time $L$ onward both consecutive points equal the old endpoint. Feasibility is inherited from the original walk, and the endpoint at time $M$ is therefore the same $v$.",
    "HirschCircuit.exists_positive_maximal_nonnegative_step": "Consider the finite nonempty set of coordinates with $g_i<0$. For each such coordinate the blocking ratio is $x_i/(-g_i)$. The zero-coordinate hypothesis makes every numerator on this set strictly positive, so the minimum blocking ratio $\\alpha$ is positive. Coordinates with $g_i<0$ remain nonnegative up to this minimum, while coordinates with $g_i\\ge0$ can only increase. A minimizing coordinate is exactly zero at $\\alpha$, and any larger step makes that same coordinate negative.",
}


def normalize(text: str) -> str:
    return re.sub(r"\s+", "", text or "")


def write(name: str, value) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def rows(api: API, theorem_name: str):
    query = urllib.parse.urlencode({"env": PIN, "theorem_name": theorem_name, "limit": 20, "offset": 0})
    result = api.request("/theorems?" + query)
    return result.get("theorems", [])


def safe_name(name: str) -> str:
    return name.replace(".", "_")


def publish_one(api: API, spec: dict):
    existing = rows(api, spec["name"])
    if existing:
        if len(existing) != 1:
            raise RuntimeError("theorem-name collision for " + spec["name"])
        theorem = api.request("/theorems/" + existing[0]["theorem_id"])
        if normalize(theorem.get("formal_statement", "")) != normalize(spec["formal"]):
            raise RuntimeError("existing theorem differs for " + spec["name"])
        theorem_id = theorem["theorem_id"]
    else:
        queued = api.request(
            "/submit-problem",
            {
                "env": PIN,
                "private": False,
                "problems": [{
                    "theorem_name": spec["name"],
                    "theorem_title": spec["title"],
                    "formal_statement": spec["formal"],
                    "natural_language_statement": spec["natural"],
                    "preamble": spec["preamble"],
                    "source": spec["source"],
                    "tags": spec["tags"],
                }],
            },
            "POST",
        )
        write(safe_name(spec["name"]) + "-problem-queued.json", queued)
        if queued.get("errors") or len(queued.get("jobs", [])) != 1:
            raise RuntimeError("failed to queue " + spec["name"])
        job = wait_job(api, queued["jobs"][0]["job_id"])
        write(safe_name(spec["name"]) + "-problem-job.json", job)
        if job.get("status") != "PUBLISHED":
            raise RuntimeError("publication failed for " + spec["name"] + ": " + str(job.get("error_message", ""))[:400])
        theorem_id = job["theorem_id"]
        theorem = api.request("/theorems/" + theorem_id)

    before = theorem.get("status")
    result = {"theorem_id": theorem_id, "status_before": before}
    if before == "Proved":
        result["status_after"] = "Proved"
        result["verify_skipped"] = True
        return result
    if before != "Open":
        raise RuntimeError("unexpected status for " + spec["name"] + ": " + str(before))

    proof = spec["proof"].read_text()
    queued = api.verify(theorem_id, proof, EXPLANATIONS[spec["name"]])
    write(safe_name(spec["name"]) + "-proof-queued.json", queued)
    verdict = wait_verdict(api, queued["submission_id"])
    write(safe_name(spec["name"]) + "-proof-verdict.json", verdict)
    after = api.request("/theorems/" + theorem_id).get("status")
    result.update({"submission_id": queued["submission_id"], "verdict": verdict.get("status"), "status_after": after})
    if result["verdict"] != "ACCEPTED" or after != "Proved":
        raise RuntimeError("proof was not accepted for " + spec["name"])
    return result


def main() -> int:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)
    state = {
        "started_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "env": PIN,
        "results": {},
    }
    for spec in SPECS:
        state["results"][spec["name"]] = publish_one(api, spec)
        write("status.json", state)
    print(json.dumps(state))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        OUT.mkdir(exist_ok=True)
        write("failure.json", {
            "failed_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "error_type": type(exc).__name__,
            "error": str(exc)[:700] if isinstance(exc, RuntimeError) else "publication failed",
        })
        raise SystemExit(2)
