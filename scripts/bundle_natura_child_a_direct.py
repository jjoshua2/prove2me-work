#!/usr/bin/env python3
"""Flatten the verified Child-A dependency graph into one Prove2Me-ready Lean file."""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SOL = ROOT / "Solutions"
ENTRY = "NaturaChildADirect"
LOCAL_IMPORT = re.compile(r"^\s*import\s+Solutions\.([A-Za-z0-9_]+)\s*$")
ANY_IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$")
AUDIT = re.compile(r"^\s*#print\s+axioms\b")
ADMISSION = re.compile(r"\b(sorry|admit|axiom)\b")


def module_path(name: str) -> Path:
    p = SOL / f"{name}.lean"
    if not p.exists():
        raise FileNotFoundError(f"missing local module {p}")
    return p


def dependencies(name: str) -> list[str]:
    out: list[str] = []
    for line in module_path(name).read_text().splitlines():
        m = LOCAL_IMPORT.match(line)
        if m:
            out.append(m.group(1))
    return out


def topo(entry: str) -> list[str]:
    seen: set[str] = set()
    active: set[str] = set()
    order: list[str] = []

    def visit(name: str) -> None:
        if name in seen:
            return
        if name in active:
            raise RuntimeError(f"cycle in local imports at {name}")
        active.add(name)
        for dep in dependencies(name):
            visit(dep)
        active.remove(name)
        seen.add(name)
        order.append(name)

    visit(entry)
    return order


def build_flat(entry: str = ENTRY) -> tuple[str, list[str]]:
    order = topo(entry)
    external: list[str] = []
    bodies: list[str] = []
    for name in order:
        lines: list[str] = []
        for line in module_path(name).read_text().splitlines():
            if LOCAL_IMPORT.match(line):
                continue
            im = ANY_IMPORT.match(line)
            if im:
                stmt = f"import {im.group(1)}"
                if stmt not in external:
                    external.append(stmt)
                continue
            if AUDIT.match(line):
                continue
            lines.append(line)
        bodies.append(
            f"/- BEGIN inlined Solutions.{name} -/\n"
            + "\n".join(lines)
            + f"\n/- END inlined Solutions.{name} -/"
        )
    text = "\n".join(external) + "\n\n" + "\n\n".join(bodies) + "\n\n#print axioms solution\n"
    code = re.sub(r"/-.*?-/", "", text, flags=re.S)
    code = re.sub(r"--.*", "", code)
    if ADMISSION.search(code):
        raise RuntimeError("flattened executable code contains an admission/axiom token")
    if "theorem solution" not in text:
        raise RuntimeError("flattened file does not contain theorem solution")
    return text, order


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=ROOT / "child_a_direct_evidence/solution.lean")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    text, order = build_flat()
    output = args.output if args.output.is_absolute() else ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(text)
    print("inlined modules:")
    for name in order:
        print("  " + name)
    print(f"wrote {output} ({len(text.encode())} bytes)")
    if args.check:
        lake = Path.home() / ".elan/bin/lake"
        run = subprocess.run(
            [str(lake), "env", "lean", "-DautoImplicit=false", str(output)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        print(run.stdout)
        if run.returncode:
            return run.returncode
        if "sorryAx" in run.stdout:
            print("sorryAx detected", file=sys.stderr)
            return 3
        if "'solution' depends on axioms:" not in run.stdout:
            print("missing solution axiom audit", file=sys.stderr)
            return 4
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
