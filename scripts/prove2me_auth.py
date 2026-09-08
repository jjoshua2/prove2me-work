#!/usr/bin/env python3
"""Safe Prove2Me credential bootstrap and connectivity diagnostics.

This helper never prints an API key or bearer token. It uses only the Python
standard library so it can run in a fresh Codex/GitHub Actions environment.
"""

from __future__ import annotations

import argparse
import json
import os
import socket
import sys
import tempfile
import time
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

API_BASE = "https://prove2.me/api/v1"
API_HOST = "prove2.me"
WORKSPACE = Path(__file__).resolve().parents[1]
CREDENTIALS_PATH = WORKSPACE / "credentials.json"


class CheckFailure(RuntimeError):
    pass


def _load_credentials() -> dict[str, Any]:
    if not CREDENTIALS_PATH.exists():
        return {}
    try:
        value = json.loads(CREDENTIALS_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CheckFailure(f"cannot read {CREDENTIALS_PATH.name}: {exc}") from exc
    if not isinstance(value, dict):
        raise CheckFailure(f"{CREDENTIALS_PATH.name} must contain a JSON object")
    return value


def _write_credentials(value: dict[str, Any]) -> None:
    CREDENTIALS_PATH.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(
        prefix=".credentials.", suffix=".tmp", dir=CREDENTIALS_PATH.parent, text=True
    )
    try:
        os.fchmod(fd, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            json.dump(value, handle, indent=2, sort_keys=True)
            handle.write("\n")
        os.replace(temporary, CREDENTIALS_PATH)
        os.chmod(CREDENTIALS_PATH, 0o600)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def _validate_api_key(value: str) -> str:
    value = value.strip()
    if not value.startswith("p2m_") or len(value) < 24:
        raise CheckFailure("PROVE2ME_API_KEY is present but does not look like a p2m_ API key")
    return value


def _api_key(credentials: dict[str, Any]) -> tuple[str | None, str | None]:
    environment_key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if environment_key:
        return _validate_api_key(environment_key), "environment"
    file_key = credentials.get("api_key")
    if isinstance(file_key, str) and file_key.strip():
        return _validate_api_key(file_key), "credentials.json"
    return None, None


def _json_request(
    method: str,
    url: str,
    *,
    payload: dict[str, Any] | None = None,
    bearer: str | None = None,
    timeout: float = 15.0,
) -> dict[str, Any]:
    body = None
    headers = {"Accept": "application/json", "User-Agent": "prove2me-work-auth-check/1"}
    if payload is not None:
        body = json.dumps(payload).encode("utf-8")
        headers["Content-Type"] = "application/json"
    if bearer:
        headers["Authorization"] = f"Bearer {bearer}"

    request = urllib.request.Request(url, data=body, headers=headers, method=method)
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            raw = response.read()
    except urllib.error.HTTPError as exc:
        # Deliberately do not print the response body: auth endpoints can return
        # credential-shaped data and diagnostics should remain safely redacted.
        raise CheckFailure(f"HTTP {exc.code} from {url}") from exc
    except urllib.error.URLError as exc:
        reason = exc.reason
        if isinstance(reason, socket.gaierror):
            raise CheckFailure(f"DNS resolution failed for {API_HOST}: {reason}") from exc
        raise CheckFailure(f"network request failed for {url}: {reason}") from exc
    except TimeoutError as exc:
        raise CheckFailure(f"request timed out for {url}") from exc

    if not raw:
        return {}
    try:
        value = json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CheckFailure(f"non-JSON response from {url}") from exc
    if not isinstance(value, dict):
        raise CheckFailure(f"unexpected JSON response shape from {url}")
    return value


def _dns_check() -> None:
    try:
        socket.getaddrinfo(API_HOST, 443, type=socket.SOCK_STREAM)
    except socket.gaierror as exc:
        raise CheckFailure(f"DNS resolution failed for {API_HOST}: {exc}") from exc


def _refresh(api_key: str) -> tuple[str, int, str | None]:
    response = _json_request(
        "POST", f"{API_BASE}/agent/refresh", payload={"api_key": api_key}
    )
    token = response.get("access_token")
    expires_at = response.get("expires_at")
    version = response.get("version")
    if not isinstance(token, str) or not token:
        raise CheckFailure("/agent/refresh succeeded but returned no access_token")
    if not isinstance(expires_at, int):
        raise CheckFailure("/agent/refresh succeeded but returned no integer expires_at")
    if version is not None and not isinstance(version, str):
        version = None
    return token, expires_at, version


def command_bootstrap(args: argparse.Namespace) -> int:
    credentials = _load_credentials()
    api_key, source = _api_key(credentials)
    if not api_key:
        raise CheckFailure(
            "no API key found; set PROVE2ME_API_KEY for the agent phase or create gitignored credentials.json"
        )
    if source == "environment" and not args.persist_api_key:
        raise CheckFailure(
            "refusing to copy PROVE2ME_API_KEY into credentials.json without --persist-api-key; "
            "only do this when the variable is intentionally available during the agent phase"
        )

    output = {
        "api_key": api_key,
        "access_token": credentials.get("access_token", ""),
        "expires_at": credentials.get("expires_at", 0),
        "version": credentials.get("version", ""),
    }
    _write_credentials(output)
    print(f"credentials=ready source={source} path={CREDENTIALS_PATH.name} mode=0600")
    return 0


def command_check(args: argparse.Namespace) -> int:
    credentials = _load_credentials()

    _dns_check()
    print("dns=ok host=prove2.me")

    _json_request("GET", f"{API_BASE}/health")
    print("health=ok")

    api_key, source = _api_key(credentials)
    token: str | None = None
    expires_at = 0
    version: str | None = None

    if api_key:
        token, expires_at, version = _refresh(api_key)
        print(f"refresh=ok key_source={source} expires_at={expires_at}")
        if not args.no_write:
            # Never persist an environment-supplied long-lived key implicitly.
            # Preserve an API key only if it was already in credentials.json.
            saved_key = credentials.get("api_key")
            output: dict[str, Any] = {
                "api_key": saved_key if isinstance(saved_key, str) else "",
                "access_token": token,
                "expires_at": expires_at,
                "version": version or credentials.get("version", ""),
            }
            _write_credentials(output)
    else:
        saved_token = credentials.get("access_token")
        saved_expiry = credentials.get("expires_at")
        if isinstance(saved_token, str) and saved_token and isinstance(saved_expiry, int):
            if saved_expiry > int(time.time()) + 30:
                token = saved_token
                expires_at = saved_expiry
                saved_version = credentials.get("version")
                version = saved_version if isinstance(saved_version, str) else None
                print(f"refresh=skipped using_saved_access_token expires_at={expires_at}")
        if token is None:
            raise CheckFailure(
                "DNS and health work, but no usable API key or unexpired access token is available"
            )

    environments = _json_request("GET", f"{API_BASE}/environments", bearer=token)
    count = environments.get("environments")
    count_text = len(count) if isinstance(count, list) else "unknown"
    version_text = version or "unknown"
    print(f"authenticated_get=ok endpoint=/environments count={count_text} platform_version={version_text}")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Bootstrap and diagnose Prove2Me authentication without printing credentials."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    bootstrap = subparsers.add_parser(
        "bootstrap", help="create/normalize gitignored credentials.json"
    )
    bootstrap.add_argument(
        "--persist-api-key",
        action="store_true",
        help="allow copying PROVE2ME_API_KEY from the environment into credentials.json",
    )
    bootstrap.set_defaults(func=command_bootstrap)

    check = subparsers.add_parser(
        "check", help="check DNS, public health, token refresh, and one authenticated GET"
    )
    check.add_argument(
        "--no-write", action="store_true", help="do not cache a refreshed access token"
    )
    check.set_defaults(func=command_check)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        return int(args.func(args))
    except CheckFailure as exc:
        print(f"prove2me-auth-check: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
