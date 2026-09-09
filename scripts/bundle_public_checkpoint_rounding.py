#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TARGETS = {
    "vertex_selection": "Solutions.Sol_Hirsch_face_preserving_vertex_selection",
    "feasible_start_containment": "Solutions.Sol_Hirsch_feasible_start_containment_route_bound",
}


def bundle(label: str, target: str) -> None:
    seen: set[str] = set()
    visiting: set[str] = set()
    imports: set[str] = set()
    pieces: list[str] = []
    sources: list[dict[str, str]] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        if module in visiting:
            raise ValueError(f"cycle {module}")
        visiting.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        text = path.read_text(encoding="utf-8")
        body: list[str] = []
        for line in text.splitlines():
            if line.startswith("import "):
                for dep in line[7:].split():
                    if dep.startswith("Solutions."):
                        visit(dep)
                    elif dep.startswith("Mathlib") or dep == "Definitions.Def_Hirsch_model":
                        imports.add(dep)
                    else:
                        raise ValueError(f"unexpected import {dep} in {module}")
            elif not line.startswith("#print axioms "):
                body.append(line)
        joined = "\n".join(body)
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s", joined, re.M):
            raise ValueError(f"forbidden proof construct in {module}")
        # Close anonymous `noncomputable section`s after each flattened source.
        joined += "\nend\n" * len(re.findall(r"^noncomputable section\s*$", joined, re.M))
        pieces.append(f"-- BEGIN {path.relative_to(ROOT)}\n{joined}\n")
        sources.append({
            "path": str(path.relative_to(ROOT)),
            "sha256": hashlib.sha256(text.encode()).hexdigest(),
        })
        visiting.remove(module)
        seen.add(module)

    visit(target)
    if "Definitions.Def_Hirsch_model" not in imports:
        raise ValueError("flattened proof unexpectedly lost Hirsch model import")
    proof = "\n".join(f"import {x}" for x in sorted(imports)) + "\n\n" + "\n".join(pieces)
    proof += "\n#print axioms solution\n"
    out = ROOT / f"public_checkpoint_{label}_packet"
    out.mkdir(exist_ok=True)
    (out / "solution.lean").write_text(proof, encoding="utf-8")
    manifest = {
        "mathlib_rev": PIN,
        "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "solution_sha256": hashlib.sha256(proof.encode()).hexdigest(),
        "bytes": len(proof.encode()),
        "sources": sources,
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(label)
    print(json.dumps(manifest, indent=2))


def main() -> None:
    for label, target in TARGETS.items():
        bundle(label, target)


if __name__ == "__main__":
    main()
