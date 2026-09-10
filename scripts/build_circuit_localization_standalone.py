#!/usr/bin/env python3
"""Flatten a circuit-localization public adapter into a standalone Prove2Me proof.

Only private `Solutions.*` dependencies are inlined. Public definition modules
stay as imports, so the generated proof is checked against the same public
vocabulary used in the theorem statement. Importing theorem stubs is forbidden.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PUBLIC_IMPORTS = [
    "Mathlib",
    "Definitions.Def_Hirsch_common_face_geometry",
    "Definitions.Def_Hirsch_circuit_slack_model",
]
IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)\s*$")
PRINT_AXIOMS_RE = re.compile(r"^\s*#print\s+axioms\b")


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def module_path(name: str) -> Path:
    return ROOT / (name.replace(".", "/") + ".lean")


def build(root_module: str) -> tuple[str, list[dict[str, str]]]:
    seen: set[str] = set()
    visiting: set[str] = set()
    pieces: list[str] = []
    sources: list[dict[str, str]] = []

    def visit(name: str) -> None:
        if name in seen:
            return
        if name in visiting:
            raise RuntimeError("cyclic Solutions import: " + name)
        visiting.add(name)
        path = module_path(name)
        if not path.is_file():
            raise RuntimeError("missing source module: " + name)
        text = path.read_text(encoding="utf-8")
        body: list[str] = []
        for line in text.splitlines():
            m = IMPORT_RE.match(line)
            if m:
                dep = m.group(1)
                if dep.startswith("Solutions."):
                    visit(dep)
                elif dep.startswith("Theorems."):
                    raise RuntimeError("theorem-stub import forbidden: " + dep)
                else:
                    # Public definitions/Mathlib are supplied by PUBLIC_IMPORTS.
                    continue
            elif PRINT_AXIOMS_RE.match(line):
                continue
            else:
                body.append(line)
        visiting.remove(name)
        seen.add(name)
        rel = path.relative_to(ROOT).as_posix()
        sources.append({"module": name, "path": rel, "sha256": digest(text)})
        pieces.append("\n".join(body).rstrip() + "\n")

    visit(root_module)
    out = "".join(f"import {m}\n" for m in PUBLIC_IMPORTS) + "\n"
    out += "\n".join(pieces)
    out += "\n#print axioms solution\n"
    if len(re.findall(r"(?m)^\s*theorem\s+solution\b", out)) != 1:
        raise RuntimeError("generated proof must contain exactly one theorem solution")
    if re.search(r"(?m)^\s*(axiom|opaque)\b", out):
        raise RuntimeError("generated proof contains an unchecked declaration")
    return out, sources


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("module")
    p.add_argument("output", type=Path)
    p.add_argument("manifest", type=Path)
    args = p.parse_args()
    text, sources = build(args.module)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text, encoding="utf-8")
    manifest = {
        "root_module": args.module,
        "output_sha256": digest(text),
        "sources": sources,
        "public_imports": PUBLIC_IMPORTS,
    }
    args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
