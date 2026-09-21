#!/usr/bin/env python3
"""Exercise the actual refresh method offline; synthetic data is not a receipt.

Version-specific regression: run on the 0.10.7 compatibility commit. Older
version-specific tests are historical and must be run on their own pinned heads.
"""
import ast
import contextlib
import hashlib
import io
import json
from pathlib import Path
from types import SimpleNamespace
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'scripts/publish_projective_small_blocks.py'
EXPECTED = '0.10.7'
PREVIOUS_BLOB = 'e20f826cdd582ad9ed5ec775c45d0f63b1069ae6'


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def run_tests():
    source = SOURCE.read_text(encoding='utf-8')
    old_literal = "data.get('version') != '0.10.6'"
    new_literal = "data.get('version') != '0.10.7'"
    assert source.count(new_literal) == 1
    assert git_blob(source.replace(new_literal, old_literal).encode()) == PREVIOUS_BLOB
    tree = ast.parse(source)
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'VersionCheckedAPI')
    method = next(n for n in cls.body if isinstance(n, ast.FunctionDef) and n.name == 'refresh')
    scope = {'json': json, 'urllib': urllib, 'time': SimpleNamespace(time=lambda: 1000.0)}
    exec(compile(ast.Module(body=[method], type_ignores=[]), str(SOURCE), 'exec'), scope)
    refresh = scope['refresh']

    class OfflineOpener:
        def __init__(self, payload):
            self.payload, self.calls = payload, 0

        def open(self, req, timeout):
            self.calls += 1
            assert req.full_url == 'https://prove2.me/api/v1/agent/refresh'
            assert req.get_method() == 'POST' and timeout == 45
            assert json.loads(req.data) == {'api_key': 'synthetic-offline-key'}
            assert req.get_header('Content-type') == 'application/json'
            assert req.get_header('Authorization') is None
            return io.StringIO(json.dumps(self.payload))

    cases = [
        ('supported-explicit-expiry', {'version': EXPECTED, 'access_token': 'synthetic-token', 'expires_at': 9876}, None),
        ('supported-default-expiry', {'version': EXPECTED, 'access_token': 'synthetic-token'}, None),
        ('previous-version', {'version': '0.10.6', 'access_token': 'synthetic-token'}, RuntimeError),
        ('older-version', {'version': '0.10.5', 'access_token': 'synthetic-token'}, RuntimeError),
        ('future-version', {'version': '0.10.8', 'access_token': 'synthetic-token'}, RuntimeError),
        ('missing-version', {'access_token': 'synthetic-token'}, RuntimeError),
        ('null-version', {'version': None, 'access_token': 'synthetic-token'}, RuntimeError),
        ('numeric-version', {'version': 107, 'access_token': 'synthetic-token'}, RuntimeError),
        ('version-suffix', {'version': '0.10.7-dev', 'access_token': 'synthetic-token'}, RuntimeError),
        ('version-whitespace', {'version': '0.10.7 ', 'access_token': 'synthetic-token'}, RuntimeError),
        ('version-prefix', {'version': 'v0.10.7', 'access_token': 'synthetic-token'}, RuntimeError),
        ('missing-token', {'version': EXPECTED}, KeyError),
    ]
    results = []
    for name, payload, error in cases:
        opener = OfflineOpener(payload)
        obj = SimpleNamespace(key='synthetic-offline-key', token='before', expires=0, opener=opener)
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            try:
                refresh(obj)
            except Exception as caught:
                assert error is not None and isinstance(caught, error), (name, type(caught))
                if error is RuntimeError:
                    assert str(caught) == 'Platform skill version changed; refresh the skill before publishing.'
                assert obj.token == 'before' and obj.expires == 0
            else:
                assert error is None, name
                assert obj.token == 'synthetic-token'
                assert obj.expires == (9876 if 'expires_at' in payload else 4500)
        assert opener.calls == 1 and not output.getvalue()
        results.append({'case': name, 'status': 'PASS'})
    return {'status': 'PASS', 'expected_version': EXPECTED,
            'method_executed_from_source': True, 'network_calls': 0,
            'real_credentials_read': False, 'only_runtime_change_is_version_literal': True,
            'source_blob': git_blob(source.encode()),
            'source_sha256': hashlib.sha256(source.encode()).hexdigest(), 'cases': results}


if __name__ == '__main__':
    print(json.dumps(run_tests(), indent=2))
