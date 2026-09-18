#!/usr/bin/env python3
"""Offline unit tests of the actual trusted refresh method; no credentials/network.

The class AST is executed with an inert base because these tests concern refresh,
not the inherited HTTP transport. The production method body is not rewritten.
"""
from __future__ import annotations

import ast
import contextlib
import hashlib
import io
import json
from pathlib import Path
import time
import types
import unittest
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'scripts/publish_projective_small_blocks.py'
EXPECTED_VERSION = '0.10.5'
OLD_SOURCE_BLOB = '91aaddfbe4c65c043ab3646412217a04521417c2'
UPSTREAM_SKILL_BLOB = '3b64e0d72acd92c8e052b65624c059978ca66748'


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def load_refresh_class():
    tree = ast.parse(SOURCE.read_text(encoding='utf-8'), filename=str(SOURCE))
    cls = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'VersionCheckedAPI')
    namespace = {'API': object, 'urllib': urllib, 'json': json, 'time': time}
    exec(compile(ast.Module(body=[cls], type_ignores=[]), str(SOURCE), 'exec'), namespace)
    return namespace['VersionCheckedAPI']


class FakeOpener:
    def __init__(self, payload=None, error=None):
        self.payload = payload
        self.error = error
        self.requests = []

    def open(self, request, timeout):
        self.requests.append((request, timeout))
        if self.error is not None:
            raise self.error
        return io.BytesIO(json.dumps(self.payload).encode())


class VersionRefreshTests(unittest.TestCase):
    def make_client(self, payload=None, error=None):
        client = load_refresh_class()()
        client.key = 'offline-test-key-not-a-credential'
        client.token = ''
        client.expires = 0.0
        client.opener = FakeOpener(payload, error)
        return client

    def test_runtime_change_is_only_reviewed_version_literal(self):
        data = SOURCE.read_bytes()
        self.assertEqual(data.count(b"data.get('version') != '0.10.5'"), 1)
        restored = data.replace(b"data.get('version') != '0.10.5'", b"data.get('version') != '0.10.4'", 1)
        self.assertEqual(git_blob(restored), OLD_SOURCE_BLOB)

    def test_skill_matches_official_release_exactly(self):
        self.assertEqual(git_blob((ROOT / 'SKILL.md').read_bytes()), UPSTREAM_SKILL_BLOB)

    def test_matching_version_updates_state_and_uses_only_original_refresh_url(self):
        client = self.make_client({'version': EXPECTED_VERSION, 'access_token': 'offline-dummy-token', 'expires_at': 12345})
        client.refresh()
        self.assertEqual(client.token, 'offline-dummy-token')
        self.assertEqual(client.expires, 12345.0)
        self.assertEqual(len(client.opener.requests), 1)
        request, timeout = client.opener.requests[0]
        self.assertEqual(request.full_url, 'https://prove2.me/api/v1/agent/refresh')
        self.assertEqual(request.get_method(), 'POST')
        self.assertEqual(json.loads(request.data), {'api_key': client.key})
        self.assertEqual(timeout, 45)
        self.assertIsNone(request.get_header('Authorization'))

    def test_mismatched_malformed_and_missing_versions_fail_closed(self):
        for version in ['0.10.4', '0.10.6', '0.11.0', '0.10.5-rc1', 'v0.10.5', '0.10.5 ', '', None, 0.105, ['0.10.5'], {'version': '0.10.5'}]:
            with self.subTest(version=version):
                client = self.make_client({'version': version, 'access_token': 'must-not-be-retained'})
                with self.assertRaisesRegex(RuntimeError, 'Platform skill version changed'):
                    client.refresh()
                self.assertEqual((client.token, client.expires), ('', 0.0))
                self.assertEqual(len(client.opener.requests), 1)
        client = self.make_client({'access_token': 'must-not-be-retained'})
        with self.assertRaises(RuntimeError):
            client.refresh()
        self.assertEqual(client.token, '')

    def test_matching_version_without_token_does_not_succeed(self):
        client = self.make_client({'version': EXPECTED_VERSION})
        with self.assertRaises(KeyError):
            client.refresh()
        self.assertEqual((client.token, client.expires), ('', 0.0))

    def test_default_expiry_remains_bounded(self):
        client = self.make_client({'version': EXPECTED_VERSION, 'access_token': 'offline-dummy-token'})
        before = time.time()
        client.refresh()
        after = time.time()
        self.assertLessEqual(before + 3500, client.expires)
        self.assertLessEqual(client.expires, after + 3500)

    def test_transport_errors_are_not_swallowed(self):
        client = self.make_client(error=RuntimeError('authenticated redirects disabled'))
        with self.assertRaisesRegex(RuntimeError, 'authenticated redirects disabled'):
            client.refresh()
        self.assertEqual(client.token, '')

    def test_refresh_does_not_log_key_or_token(self):
        for version in [EXPECTED_VERSION, '0.10.4']:
            client = self.make_client({'version': version, 'access_token': 'offline-dummy-token'})
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                try:
                    client.refresh()
                except RuntimeError as exc:
                    self.assertNotIn(client.key, str(exc))
                    self.assertNotIn('offline-dummy-token', str(exc))
            self.assertEqual(out.getvalue() + err.getvalue(), '')


if __name__ == '__main__':
    unittest.main(verbosity=2)
