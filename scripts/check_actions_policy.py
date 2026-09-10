#!/usr/bin/env python3
"""Reject accidental push-triggered experimental GitHub Actions workflows.

The repository intentionally permits automatic push triggers only for a tiny set
of durable main-branch maintenance workflows. Proof experiments and publication
workflows must remain manual/reusable so cloud agents cannot use hosted Actions
as a trial-and-error Lean compiler.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

WORKFLOWS = Path('.github/workflows')
ALLOWED_PUSH = {
    'actions-policy.yml',
    'lean-cache-warm.yml',
    'prove2me-auth-smoke.yml',
}

# YAML allows either `push:` or a quoted key. We only need a conservative
# repository policy check, not a full YAML parser.
PUSH_KEY = re.compile(r"(?m)^\s*(?:push|'push'|\"push\")\s*:\s*(?:$|[^#])")


def main() -> int:
    failures: list[str] = []
    if not WORKFLOWS.is_dir():
        print(f'missing workflow directory: {WORKFLOWS}', file=sys.stderr)
        return 2

    for path in sorted(WORKFLOWS.glob('*.y*ml')):
        text = path.read_text(encoding='utf-8')
        if PUSH_KEY.search(text) and path.name not in ALLOWED_PUSH:
            failures.append(str(path))

    if failures:
        print('Push-triggered experimental workflows are not allowed.', file=sys.stderr)
        print('Use workflow_dispatch/workflow_call and the shared Lean setup instead:', file=sys.stderr)
        for path in failures:
            print(f'  - {path}', file=sys.stderr)
        return 1

    print('GitHub Actions cost policy: OK')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
