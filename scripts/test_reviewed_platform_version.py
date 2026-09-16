#!/usr/bin/env python3
"""Offline checks of the real refresh method; never reads credentials or calls a server."""
from __future__ import annotations
import ast
import hashlib
import io
import json
from pathlib import Path
import time
import unittest
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
PUBLISHER = ROOT / 'scripts/publish_projective_small_blocks.py'


def load_refresh_class():
    tree = ast.parse(PUBLISHER.read_text(encoding='utf-8'))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'VersionCheckedAPI')
    ns = {'API': object, 'json': json, 'time': time, 'urllib': urllib}
    # Execute the actual class, not a rewritten simulation. The imported parent
    # constructor is unnecessary: refresh needs only key/opener/token/expires.
    module = ast.Module(body=[cls], type_ignores=[])
    exec(compile(ast.fix_missing_locations(module), str(PUBLISHER), 'exec'), ns)
    return ns['VersionCheckedAPI']


class FakeOpener:
    def __init__(self, payload):
        self.payload = payload
        self.calls = []

    def open(self, request, timeout):
        self.calls.append((request.full_url, request.get_method(), timeout, json.loads(request.data)))
        return io.BytesIO(json.dumps(self.payload).encode())


class ReviewedVersionTests(unittest.TestCase):
    def client(self, payload):
        obj = load_refresh_class()()
        obj.key = 'offline-fixture-not-a-credential'
        obj.opener = FakeOpener(payload)
        return obj

    def test_reviewed_version_and_original_endpoint(self):
        c = self.client({'version': '0.10.4', 'access_token': 'offline-fixture-token', 'expires_at': 12345})
        c.refresh()
        self.assertEqual(c.token, 'offline-fixture-token')
        self.assertEqual(c.expires, 12345.0)
        self.assertEqual(c.opener.calls, [('https://prove2.me/api/v1/agent/refresh', 'POST', 45,
                                         {'api_key': 'offline-fixture-not-a-credential'})])

    def test_old_version_fails_before_token_assignment(self):
        c = self.client({'version': '0.10.3', 'access_token': 'must-not-be-used'})
        with self.assertRaisesRegex(RuntimeError, 'refresh the skill'):
            c.refresh()
        self.assertFalse(hasattr(c, 'token'))

    def test_future_version_still_fails_closed(self):
        c = self.client({'version': '0.10.5', 'access_token': 'must-not-be-used'})
        with self.assertRaisesRegex(RuntimeError, 'refresh the skill'):
            c.refresh()
        self.assertFalse(hasattr(c, 'token'))

    def test_missing_version_fails_closed(self):
        c = self.client({'access_token': 'must-not-be-used'})
        with self.assertRaises(RuntimeError): c.refresh()
        self.assertFalse(hasattr(c, 'token'))

    def test_nonstring_version_fails_closed(self):
        for version in (None, 104, True, ['0.10.4']):
            c = self.client({'version': version, 'access_token': 'must-not-be-used'})
            with self.assertRaises(RuntimeError): c.refresh()
            self.assertFalse(hasattr(c, 'token'))

    def test_missing_token_rejected(self):
        c = self.client({'version': '0.10.4'})
        with self.assertRaises(KeyError): c.refresh()
        self.assertFalse(hasattr(c, 'token'))

    def test_default_expiry_retained(self):
        c = self.client({'version': '0.10.4', 'access_token': 'offline-fixture-token'})
        before = time.time(); c.refresh(); after = time.time()
        self.assertLessEqual(before + 3500, c.expires)
        self.assertLessEqual(c.expires, after + 3500)

    def test_reviewed_official_skill_bytes(self):
        for path, expected in [('SKILL.md', '39798b14c10fbc6843fffa5f968cf48e68e73593'),
                               ('references/communicate.md', 'a5128681757cb431927b69ab2e879c4840867a8f')]:
            content = (ROOT / path).read_bytes()
            digest = hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\0' + content).hexdigest()
            self.assertEqual(digest, expected)

    def test_only_reviewed_runtime_literal_changed(self):
        content = PUBLISHER.read_text(encoding='utf-8')
        self.assertEqual(content.count("data.get('version') != '0.10.4'"), 1)
        before = content.replace("data.get('version') != '0.10.4'", "data.get('version') != '0.10.3'").encode()
        digest = hashlib.sha1(b'blob ' + str(len(before)).encode() + b'\0' + before).hexdigest()
        self.assertEqual(digest, 'c574e0dc5aeaa2164dc3c7498b7707a44677dd3e')


if __name__ == '__main__':
    unittest.main(verbosity=2)
