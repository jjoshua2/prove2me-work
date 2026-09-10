#!/usr/bin/env python3
"""Control-flow tests with synthetic regression fixtures; NEVER a Lean check.
The fake lake executable only exits with failure, so no simulated proof can
produce a successful kernel receipt. Mathematical suites are tested separately.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tempfile

PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
ROOT = Path(__file__).resolve().parents[1]

def main():
    results = []
    with tempfile.TemporaryDirectory(prefix='checkpoint-gate-controls.') as tmp:
        root = Path(tmp)
        for d in ('scripts', 'research', 'tmp', 'home', 'bin'):
            (root / d).mkdir()
        shutil.copyfile(ROOT / 'scripts/verify_circuit_checkpoint_continuation.sh',
                        root / 'scripts/verify_circuit_checkpoint_continuation.sh')
        (root / 'lean-toolchain').write_text('leanprover/lean4:v4.30.0\n')
        (root / 'lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'mathlib', 'rev': PIN}]}))
        (root / 'scripts/check_actions_policy.py').write_text('print("fixture policy check")\n')
        fixture = ('import argparse\nfrom pathlib import Path\n'
                   'p=argparse.ArgumentParser();p.add_argument("--output",type=Path)\n'
                   'p.parse_args().output.write_text("synthetic gate fixture\\n")\n')
        for name in ('carrier_defect', 'ordering_obstruction', 'checkpoint_localization'):
            (root / f'scripts/test_circuit_{name}.py').write_text(fixture)
        digest = hashlib.sha256(b'synthetic gate fixture\n').hexdigest()
        carrier_hashes = ''.join(f'{digest}  {name}-regression.json\n' for name in ('carrier', 'ordering'))
        (root / 'research/circuit_carrier_regressions.sha256').write_text(carrier_hashes)
        checkpoint_hash = root / 'research/checkpoint_localization_regression.sha256'
        checkpoint_hash.write_text(f'{digest}  checkpoint-regression.json\n')
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        env.update(HOME=str(root/'home'), TMPDIR=str(root/'tmp'),
                   PATH=f'{root / "bin"}:/usr/local/bin:/usr/bin:/bin')
        def check(name, args, ok, extra=None):
            result = subprocess.run(['bash', 'scripts/verify_circuit_checkpoint_continuation.sh', *args],
                                    cwd=root, env={**env, **(extra or {})}, text=True,
                                    capture_output=True, timeout=20)
            assert (result.returncode == 0) == ok, (name, result.stdout, result.stderr)
            assert not list((root/'tmp').rglob('receipt.json')), 'Unexpected kernel receipt'
            results.append({'case': name, 'returncode': result.returncode, 'passed': True})
        check('unknown argument', ['--invalid'], False)
        (root/'lean-toolchain').write_text('leanprover/lean4:v0.0.0\n')
        check('wrong Lean pin', ['--checks-only'], False)
        (root/'lean-toolchain').write_text('leanprover/lean4:v4.30.0\n')
        (root/'lake-manifest.json').write_text(json.dumps({'packages': []}))
        check('wrong Mathlib pin', ['--checks-only'], False)
        (root/'lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'mathlib', 'rev': PIN}]}))
        check('disabled Python assertions', ['--checks-only'], False, {'PYTHONOPTIMIZE': '1'})
        checkpoint_hash.write_text(f'{"0"*64}  checkpoint-regression.json\n')
        check('corrupted regression hash', ['--checks-only'], False)
        checkpoint_hash.write_text(f'{digest}  checkpoint-regression.json\n')
        check('checks-only does not imply Lean', ['--checks-only'], True)
        # Test the gate's behavior on a compiler failure without simulating success.
        fake = root/'bin/lake'
        fake.write_text('#!/usr/bin/env bash\necho "INTENTIONAL failing compiler fixture" >&2\nexit 79\n')
        fake.chmod(0o755)
        check('failed compiler cannot create receipt', [], False)
    print(json.dumps({'evidence': 'synthetic_control_flow_tests_not_mathematical_or_Lean_verification',
                      'cases': results}, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
