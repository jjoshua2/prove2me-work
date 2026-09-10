#!/usr/bin/env bash
# Local/manual gate only. Never authenticates, publishes, or changes Git refs.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
mode="${1:-all}"
if [[ $# -gt 1 || ( "$mode" != all && "$mode" != --checks-only ) ]]; then
  echo 'usage: bash scripts/verify_circuit_checkpoint_continuation.sh [--checks-only]' >&2
  exit 2
fi
python3 - <<'PY'
import json, sys
from pathlib import Path
if not __debug__:
    sys.exit('Refusing optimized Python: the exact regression suites use assertions.')
if Path('lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.30.0':
    sys.exit('Unexpected Lean pin; nothing was compiled.')
pkgs = json.loads(Path('lake-manifest.json').read_text())['packages']
revs = [p.get('rev') for p in pkgs if p.get('name') == 'mathlib']
if revs != ['c5ea00351c28e24afc9f0f84379aa41082b1188f']:
    sys.exit('Unexpected Mathlib pin; nothing was compiled.')
PY
out="$(mktemp -d "${TMPDIR:-/tmp}/circuit-checkpoint-gate.XXXXXX")"
echo "Evidence directory: $out"
python3 scripts/check_actions_policy.py
python3 scripts/test_circuit_carrier_defect.py --output "$out/carrier-regression.json" > "$out/carrier.stdout"
python3 scripts/test_circuit_ordering_obstruction.py --output "$out/ordering-regression.json" > "$out/ordering.stdout"
python3 scripts/test_circuit_checkpoint_localization.py --output "$out/checkpoint-regression.json" > "$out/checkpoint.stdout"
(cd "$out" && sha256sum -c "$root/research/circuit_carrier_regressions.sha256" &&
  sha256sum -c "$root/research/checkpoint_localization_regression.sha256")
if [[ "$mode" == --checks-only ]]; then
  echo 'Exact/structural checks passed. Lean was NOT run; no platform verdict.'
  exit 0
fi
if ! command -v lake >/dev/null 2>&1; then
  if [[ -x "$HOME/.elan/bin/lake" ]]; then
    export PATH="$HOME/.elan/bin:$PATH"
  else
    echo 'Pinned Lean/Lake unavailable; no Lean verification was performed.' >&2
    exit 2
  fi
fi
modules=(Solutions.PolynomialCircuitCarrierDefect Solutions.PolynomialCircuitStepCommutation
  Solutions.PolynomialCircuitCheckpointLocalization Solutions.PolynomialCircuitCarrierRouting)
lake build "${modules[@]}" 2>&1 | tee "$out/build.log"
# Force fresh axiom reports: lake build can reuse cached modules without
# re-emitting #print output. Never audit only whatever a build happened to print.
mapfile -t required < research/circuit_checkpoint_required_axioms.txt
if [[ ${#required[@]} -ne 28 ]]; then
  echo 'Expected exactly 28 reviewed declarations.' >&2; exit 2
fi
{
  for m in "${modules[@]}"; do printf 'import %s\n' "$m"; done
  for d in "${required[@]}"; do
    if [[ ! "$d" =~ ^[A-Za-z_][A-Za-z0-9_.]*$ ]]; then
      echo 'Malformed axiom declaration name.' >&2; exit 2
    fi
    printf '#print axioms %s\n' "$d"
  done
} > "$out/CheckpointAudit.lean"
lake env lean "$out/CheckpointAudit.lean" 2>&1 | tee "$out/axioms.log"
python3 scripts/check_lean_axiom_log.py "$out/axioms.log" "${required[@]}"
# A receipt is written ONLY after all preceding commands pass. It describes
# source/kernel evidence, never a Prove2Me status or a standalone server proof.
python3 - "$out" <<'PY'
import hashlib, json, subprocess, sys
from pathlib import Path
out = Path(sys.argv[1])
paths = [Path('lean-toolchain'), Path('lake-manifest.json'), Path('lakefile.lean')]
for folder in ('Definitions', 'Solutions', 'Theorems'):
    paths += sorted(Path(folder).rglob('*.lean'))
source = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
logs = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in out.iterdir() if p.is_file()}
head = subprocess.run(['git', 'rev-parse', 'HEAD'], text=True, capture_output=True)
receipt = {'evidence': 'source_build_and_fresh_axiom_audit_passed',
           'required_declarations': 28, 'standalone_server_proof_compiled': False,
           'Prove2Me_actions': 0, 'git_head': head.stdout.strip() if head.returncode == 0 else None,
           'source_sha256': source, 'evidence_sha256': logs}
(out / 'receipt.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
PY
echo 'Source/kernel gate passed. No standalone/publication/platform verdict is implied.'
