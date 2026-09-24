#!/usr/bin/env python3
"""Offline tests for the reviewed 0.11.0 refresh guard, with no live credentials.
Extract the actual production class; no publisher module side effects are run.
Historical exact-revision tests are retained unchanged, not retargeted silently.
"""
from __future__ import annotations
import ast
import hashlib
import io
import json
from pathlib import Path
import time
import unittest
import urllib.request
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'scripts/publish_projective_small_blocks.py'
OLD_BLOB = 'b233d800b8cfd148ca37b0c4a7e4928b82158239'
NEW_BLOB = '9826983817f3bc159068b0e9ae4960a39459d1d7'


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def load_class():
    tree = ast.parse(SOURCE.read_text())
    classes = [n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == 'VersionCheckedAPI']
    if len(classes) != 1:
        raise AssertionError('Expected exactly one production refresh class')
    namespace = {'API': object, 'urllib': __import__('urllib'), 'json': json, 'time': time}
    exec(compile(ast.Module(body=classes, type_ignores=[]), str(SOURCE), 'exec'), namespace)
    return namespace['VersionCheckedAPI']


class FakeOpener:
    def __init__(self, payload):
        self.payload = payload
        self.calls = []

    def open(self, request, timeout):
        self.calls.append((request, timeout))
        return io.StringIO(json.dumps(self.payload))


def client(payload):
    instance = load_class()()
    instance.key = 'dummy-offline-key'
    instance.token = ''
    instance.expires = 0
    instance.opener = FakeOpener(payload)
    return instance


class ProtocolTests(unittest.TestCase):
    def test_exact_single_literal_change(self):
        data = SOURCE.read_bytes()
        self.assertEqual(git_blob(data), NEW_BLOB)
        self.assertEqual(data.count(b"'0.11.0'"), 1)
        self.assertEqual(git_blob(data.replace(b"'0.11.0'", b"'0.10.9'")), OLD_BLOB)
        self.assertNotIn(b'/licensing', data)

    def test_accepts_reviewed_version_and_preserves_request(self):
        instance = client({'version': '0.11.0', 'access_token': 'dummy-offline-token', 'expires_at': 1234})
        instance.refresh()
        self.assertEqual(instance.token, 'dummy-offline-token')
        self.assertEqual(instance.expires, 1234.0)
        self.assertEqual(len(instance.opener.calls), 1)
        request, timeout = instance.opener.calls[0]
        self.assertEqual(request.full_url, 'https://prove2.me/api/v1/agent/refresh')
        self.assertEqual(request.get_method(), 'POST')
        self.assertEqual(request.get_header('Content-type'), 'application/json')
        self.assertEqual(json.loads(request.data), {'api_key': 'dummy-offline-key'})
        self.assertEqual(timeout, 45)

    def test_rejects_unreviewed_versions_before_token_install(self):
        for version in ['0.10.9', '0.10.8', '0.11.1', '1.0.0', '', None, 110, ['0.11.0'], '0.11.0 ', True]:
            with self.subTest(version=version):
                instance = client({'version': version, 'access_token': 'must-not-install', 'expires_at': 999})
                with self.assertRaisesRegex(RuntimeError, '^Platform skill version changed;'):
                    instance.refresh()
                self.assertEqual(instance.token, '')
                self.assertEqual(instance.expires, 0)
                self.assertEqual(len(instance.opener.calls), 1)

    def test_missing_version_fails_closed(self):
        instance = client({'access_token': 'must-not-install'})
        with self.assertRaises(RuntimeError):
            instance.refresh()
        self.assertEqual(instance.token, '')
        self.assertEqual(instance.expires, 0)

    def test_nonmapping_response_does_not_install_token(self):
        for value in [None, [], '0.11.0', 110]:
            with self.subTest(value=value):
                instance = client(value)
                with self.assertRaises(AttributeError):
                    instance.refresh()
                self.assertEqual(instance.token, '')
                self.assertEqual(instance.expires, 0)

    def test_missing_token_does_not_succeed(self):
        instance = client({'version': '0.11.0'})
        with self.assertRaises(KeyError):
            instance.refresh()
        self.assertEqual(instance.token, '')
        self.assertEqual(instance.expires, 0)

    def test_existing_default_expiry_behavior(self):
        instance = client({'version': '0.11.0', 'access_token': 'dummy-offline-token'})
        with patch.object(time, 'time', return_value=1000):
            instance.refresh()
        self.assertEqual(instance.expires, 4500.0)

    def test_no_licensing_side_effect_or_prerequisite(self):
        for status in ['pending', 'accepted', 'not_required', 'inactive', 'unavailable']:
            with self.subTest(status=status):
                payload = {'version': '0.11.0', 'access_token': 'dummy-offline-token',
                           'licensing': {'status': status, 'terms_version': 'test-only'}}
                instance = client(payload)
                instance.refresh()
                self.assertEqual(instance.token, 'dummy-offline-token')
                self.assertEqual(len(instance.opener.calls), 1)
                request, _ = instance.opener.calls[0]
                self.assertEqual(request.full_url, 'https://prove2.me/api/v1/agent/refresh')
                self.assertEqual(json.loads(request.data), {'api_key': 'dummy-offline-key'})


if __name__ == '__main__':
    unittest.main(verbosity=2)
