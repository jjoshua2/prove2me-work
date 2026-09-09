#!/usr/bin/env python3
"""Prepare an offline proof packet. This script has no network or API action."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "public_interval_repair_packet"
TARGET = "Solutions.Sol_Hirsch_face_interval_cover_route_bound"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
ALLOWED_IMPORTS = {"Mathlib", "Definitions.Def_Hirsch_model"}


def main() -> None:
    seen: set[str] = set()
    visiting: set[str] = set()
    imports: set[str] = set()
    pieces: list[str] = []
    sources: list[dict[str, str]] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        if module in visiting:
            raise ValueError("Cyclic local import: " + module)
        visiting.add(module)
        path = ROOT / (module.replace(".", "/") + ".lean")
        text = path.read_text(encoding="utf-8")
        body: list[str] = []
        for line in text.splitlines():
            if line.startswith("import "):
                for dep in line[7:].split():
                    if dep.startswith("Solutions."):
                        visit(dep)
                    elif dep in ALLOWED_IMPORTS:
                        imports.add(dep)
                    else:
                        raise ValueError("Unexpected external import: " + dep)
            elif not line.startswith("#print axioms "):
                body.append(line)
        joined = "\n".join(body)
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s", joined, re.M):
            raise ValueError("Admission or unchecked declaration: " + module)
        anonymous = len(re.findall(r"^noncomputable section\s*$", joined, re.M))
        if anonymous and re.search(r"^end\s*$", joined, re.M):
            raise ValueError("Anonymous-section closure requires manual review: " + module)
        joined += "\nend\n" * anonymous
        pieces.append("-- BEGIN " + str(path.relative_to(ROOT)) + "\n" + joined + "\n")
        sources.append({"path": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(text.encode()).hexdigest()})
        visiting.remove(module)
        seen.add(module)

    visit(TARGET)
    header = "\n".join("import " + dep for dep in sorted(imports)) + "\n\n"
    proof = header + "\n".join(pieces) + "\n#print axioms solution\n"
    OUT.mkdir(exist_ok=True)
    (OUT / "solution.lean").write_text(proof, encoding="utf-8")
    original = (ROOT / (TARGET.replace(".", "/") + ".lean")).read_text()
    theorem_type = original[original.index("theorem solution"):original.index(" := by")]
    manifest = {
        "mathlib_rev": PIN,
        "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "proposed_theorem_name": "Hirsch.face_interval_cover_route_bound",
        "publication_status": "NOT_SUBMITTED",
        "imports": sorted(imports),
        "sources": sources,
        "theorem_type": theorem_type,
        "solution_sha256": hashlib.sha256(proof.encode()).hexdigest(),
        "bytes": len(proof.encode()),
    }
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({k: manifest[k] for k in ("source_commit", "solution_sha256", "bytes", "publication_status")}, indent=2))


if __name__ == "__main__":
    main()
