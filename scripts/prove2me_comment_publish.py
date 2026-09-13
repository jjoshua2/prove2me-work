#!/usr/bin/env python3
"""Comment-triggered Prove2Me packet verification and trusted publication.

The GitHub Actions workflow that calls this script is split on purpose:

* the verify job compiles/audits candidate packets from a pull-request SHA and
  never receives ``PROVE2ME_API_KEY``;
* the publish job checks out trusted code from ``main``, consumes only the
  frozen artifact, and is the only step that may see the API key.

This module is the trusted publisher. Candidate pull-request Python is never
imported. Credentials are read from the environment inside API calls and are
never printed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Callable
from urllib.parse import urlencode

ALLOWED_ACTORS = frozenset({"jjoshua2"})
ALLOWED_ACTIONS = frozenset({"publish", "verify"})
PACKET_ROOT = Path("research/publication_packets")
REQUIRED_SOLUTION = "solution.lean"
AUDIT_FILES = ("driver.lean", "solution.lean", "statement.lean")
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s", re.M)
COMMAND = re.compile(r"^/prove2me\s+(publish|verify)(?:\s+(.*))?$")
TARGET_NAME = re.compile(r"^[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z][A-Za-z0-9_]*)*$")
PREAMBLE_DECL = re.compile(
    r"(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:def|structure|class|inductive|abbrev|theorem|lemma|instance|opaque|axiom|alias)\b"
)
SECRETISH = re.compile(r"p2m_[A-Za-z0-9]+|Bearer\s+\S+", re.I)
TERMINAL_VERIFY = frozenset(
    {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
)
ACTIVE_PUBLISH = frozenset({"PENDING", "COMPILING"})
TERMINAL_PUBLISH = frozenset({"PUBLISHED", "FAILED", "ERROR"})


class RequestError(ValueError):
    """User-facing command or packet selection error."""


def redact(text: str) -> str:
    return SECRETISH.sub("[redacted]", text)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def dump_json(path: Path, value: Any) -> Any:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    return value


def first_command_line(body: str) -> str:
    for raw in body.splitlines():
        line = raw.strip()
        if line:
            return line
    return ""


def parse_comment(body: str, actor: str) -> dict[str, Any]:
    if actor not in ALLOWED_ACTORS:
        raise RequestError(f"actor {actor!r} is not allowed to trigger Prove2Me publication")
    line = first_command_line(body)
    match = COMMAND.match(line)
    if match is None:
        raise RequestError("first non-empty line must be `/prove2me publish` or `/prove2me verify`")
    action = match.group(1)
    if action not in ALLOWED_ACTIONS:
        raise RequestError(f"unsupported action {action!r}")
    tokens = (match.group(2) or "").split()
    targets: list[str] = []
    packets: list[str] = []
    taking_targets = False
    for token in tokens:
        if token == "--targets":
            taking_targets = True
            continue
        if token.startswith("--targets="):
            taking_targets = False
            value = token.split("=", 1)[1]
            targets.extend(normalize_target(part) for part in value.split(",") if part)
            continue
        if token.startswith("--"):
            raise RequestError(f"unknown flag {token!r}")
        if taking_targets:
            targets.extend(normalize_target(part) for part in token.split(",") if part)
            taking_targets = False
            continue
        if TARGET_NAME.match(token) and "." in token:
            raise RequestError(
                f"{token} looks like a Lake module. --targets consumes one token; "
                "write --targets Mod.A,Mod.B or --targets=Mod.A,Mod.B"
            )
        packets.append(token)
    if taking_targets:
        raise RequestError("--targets requires a Lake module name")
    return {
        "actor": actor,
        "action": action,
        "packets": packets,
        "targets": targets,
    }


def normalize_target(raw: str) -> str:
    name = raw.strip()
    if not name or not TARGET_NAME.match(name):
        raise RequestError(f"invalid Lake target {raw!r}; expected a module name such as Solutions.Foo")
    return name


def normalize_packet_path(raw: str) -> str:
    text = raw.strip()
    if not text:
        raise RequestError("empty packet path")
    path = Path(text)
    if path.is_absolute() or any(part == ".." for part in path.parts):
        raise RequestError(f"packet path must be relative and stay under {PACKET_ROOT}: {raw}")
    text = text.strip("/")
    path = Path(text)
    if path == PACKET_ROOT or PACKET_ROOT in path.parents:
        relative = path
    else:
        relative = PACKET_ROOT / path
    try:
        relative.relative_to(PACKET_ROOT)
    except ValueError as exc:
        raise RequestError(f"packet path must stay under {PACKET_ROOT}: {raw}") from exc
    if relative == PACKET_ROOT:
        raise RequestError("name a packet directory, not the packet root")
    return relative.as_posix()


def packet_dir_from_file(filename: str) -> str | None:
    path = Path(filename)
    if path.name != REQUIRED_SOLUTION:
        return None
    parent = path.parent
    try:
        parent.relative_to(PACKET_ROOT)
    except ValueError:
        return None
    if parent == PACKET_ROOT:
        return None
    return parent.as_posix()


def already_accepted(packet: Path) -> bool:
    verification = packet / "verification.json"
    if verification.is_file():
        try:
            data = load_json(verification)
        except (OSError, json.JSONDecodeError):
            data = {}
        if data.get("status") == "ACCEPTED":
            return True
    return (packet / "accepted-source-hash.json").is_file()


def discover_packets(changed_files: list[str], workspace: Path) -> list[str]:
    found: list[str] = []
    seen: set[str] = set()
    for filename in changed_files:
        directory = packet_dir_from_file(filename)
        if directory is None or directory in seen:
            continue
        seen.add(directory)
        path = workspace / directory
        # Existence is checked on the pull-request SHA in the verify job. The
        # gate job only has main, so skip only packets already accepted there.
        if path.exists() and already_accepted(path):
            continue
        found.append(directory)
    return found


def select_packets(request: dict[str, Any], changed_files: list[str], workspace: Path) -> list[str]:
    specified = [normalize_packet_path(item) for item in request.get("packets") or []]
    if specified:
        return specified
    action = request.get("action") or "publish"
    targets = [normalize_target(item) for item in request.get("targets") or []]
    if action == "verify" and targets:
        return []
    discovered = discover_packets(changed_files, workspace)
    if discovered:
        return discovered
    if action == "publish":
        raise RequestError(
            "publication requires a packet directory under research/publication_packets; "
            "--targets only adds a Lake build"
        )
    raise RequestError(
        "no unpublished packets found and no --targets given; "
        "pass packet paths or `/prove2me verify --targets Module.Name`"
    )


def lean_runner(workspace: Path) -> Callable[[Path], tuple[int, str]]:
    def run(source: Path) -> tuple[int, str]:
        completed = subprocess.run(
            ["lake", "env", "lean", str(source)],
            cwd=workspace,
            text=True,
            capture_output=True,
            check=False,
        )
        output = (completed.stdout or "") + (completed.stderr or "")
        return completed.returncode, output

    return run


def build_targets(workspace: Path, targets: list[str]) -> None:
    if not targets:
        return
    completed = subprocess.run(
        ["lake", "build", *targets],
        cwd=workspace,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        output = redact((completed.stdout or "") + (completed.stderr or ""))
        raise RuntimeError(f"lake build failed for {' '.join(targets)}:\n{output}")


def strip_lean_comments(text: str) -> str:
    text = re.sub(r"/--.*?-/", " ", text, flags=re.S)
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", " ", text)


def assert_preamble_platform_safe(problem: dict[str, Any], source: Path | None = None) -> None:
    """Reject custom declarations in the registered preamble.

    Prove2Me elaborates ``preamble + formal_statement`` as the target type, then
    checks that a self-contained ``theorem solution`` has that same type.
    Local compilation of statement.lean and solution.lean separately cannot see
    that composition. A preamble ``structure``/``def`` that solution.lean also
    redeclares is a classic WA: two isomorphic but distinct types.
    """
    preamble = str(problem.get("preamble") or "")
    match = PREAMBLE_DECL.search(strip_lean_comments(preamble))
    if match is None:
        return
    where = source.as_posix() if source is not None else "problem.json"
    raise RequestError(
        f"{where} preamble contains a local {match.group(0).strip()} declaration. "
        "Prove2Me preambles may only hold imports, opens, variables, and options. "
        "Publish reusable symbols with submit-definition, or inline the type using "
        "Mathlib / Definitions.Def_* names so the registered target and theorem "
        "solution have the same type."
    )


def generate_driver(solution: str) -> str:
    if "#print axioms solution" in solution:
        return solution if solution.endswith("\n") else solution + "\n"
    return solution.rstrip() + "\n\n#print axioms solution\n"


def generate_statement(problem: dict[str, Any]) -> str:
    preamble = str(problem.get("preamble") or "import Mathlib").rstrip()
    statement = str(problem.get("formal_statement") or "").strip()
    if not statement:
        raise RequestError("problem.json is missing formal_statement")
    return preamble + "\n\n" + statement + ("\n" if statement.endswith("\n") else "\n")


def copy_packet(source: Path, destination: Path) -> dict[str, str]:
    destination.mkdir(parents=True, exist_ok=True)
    written: dict[str, str] = {}
    solution = (source / REQUIRED_SOLUTION).read_text(encoding="utf-8")
    (destination / REQUIRED_SOLUTION).write_text(
        solution if solution.endswith("\n") else solution + "\n", encoding="utf-8"
    )
    written[REQUIRED_SOLUTION] = (destination / REQUIRED_SOLUTION).read_text(encoding="utf-8")
    if FORBIDDEN.search(written[REQUIRED_SOLUTION]):
        raise RequestError(f"{source.as_posix()} solution.lean contains a forbidden admission")

    problem_path = source / "problem.json"
    problem = None
    if problem_path.is_file():
        problem = load_json(problem_path)
        assert_preamble_platform_safe(problem, source / "problem.json")
        (destination / "problem.json").write_text(
            problem_path.read_text(encoding="utf-8"), encoding="utf-8"
        )
        written["problem.json"] = (destination / "problem.json").read_text(encoding="utf-8")

    explanation_path = source / "explanation.md"
    if explanation_path.is_file():
        text = explanation_path.read_text(encoding="utf-8")
        (destination / "explanation.md").write_text(
            text if text.endswith("\n") else text + "\n", encoding="utf-8"
        )
        written["explanation.md"] = text if text.endswith("\n") else text + "\n"
    elif problem and problem.get("natural_language_statement"):
        text = str(problem["natural_language_statement"]).rstrip() + "\n"
        (destination / "explanation.md").write_text(text, encoding="utf-8")
        written["explanation.md"] = text

    driver_path = source / "driver.lean"
    driver = driver_path.read_text(encoding="utf-8") if driver_path.is_file() else generate_driver(solution)
    (destination / "driver.lean").write_text(driver if driver.endswith("\n") else driver + "\n", encoding="utf-8")
    written["driver.lean"] = (destination / "driver.lean").read_text(encoding="utf-8")

    statement_path = source / "statement.lean"
    if statement_path.is_file():
        statement = statement_path.read_text(encoding="utf-8")
        (destination / "statement.lean").write_text(
            statement if statement.endswith("\n") else statement + "\n", encoding="utf-8"
        )
        written["statement.lean"] = (destination / "statement.lean").read_text(encoding="utf-8")
    elif problem is not None:
        statement = generate_statement(problem)
        (destination / "statement.lean").write_text(statement, encoding="utf-8")
        written["statement.lean"] = statement

    if (source / "manifest.json").is_file():
        (destination / "manifest.json").write_text(
            (source / "manifest.json").read_text(encoding="utf-8"), encoding="utf-8"
        )
    return written


def compile_packet(
    packet: Path,
    runner: Callable[[Path], tuple[int, str]],
    auditor: Callable[[str, list[str]], dict[str, set[str]]],
) -> dict[str, Any]:
    from check_lean_axiom_log import audit as default_audit

    auditor = auditor or default_audit
    exit_codes: dict[str, int] = {}
    logs: dict[str, str] = {}
    for name in AUDIT_FILES:
        path = packet / name
        if not path.is_file():
            continue
        code, output = runner(path)
        logs[name] = output
        exit_codes[name] = code
        (packet / f"{Path(name).stem}-compile.log").write_text(redact(output), encoding="utf-8")
        if code != 0:
            raise RuntimeError(f"{packet.name}/{name} failed to compile:\n{redact(output)}")
    reports = auditor(logs.get("driver.lean") or logs.get("solution.lean") or "", ["solution"])
    axioms = sorted({axiom for values in reports.values() for axiom in values})
    hashes = {name: sha256_file(packet / name) for name in AUDIT_FILES if (packet / name).is_file()}
    evidence = {
        "status": "PASS",
        "exit_codes": exit_codes,
        "sha256": hashes,
        "axioms": axioms,
    }
    dump_json(packet / "packet-audit.json", evidence)
    return evidence


def freeze_manifest(source: Path, destination: Path, head_sha: str, evidence: dict[str, Any]) -> dict[str, Any]:
    existing: dict[str, Any] = {}
    if (destination / "manifest.json").is_file():
        try:
            existing = load_json(destination / "manifest.json")
        except (OSError, json.JSONDecodeError):
            existing = {}
    if existing.get("public_dependencies") not in (None, {}):
        raise RequestError(f"{source.as_posix()} is not a self-contained packet")
    files = {
        name: (destination / name).read_text(encoding="utf-8")
        for name in ("solution.lean", "driver.lean", "statement.lean", "problem.json", "explanation.md")
        if (destination / name).is_file()
    }
    manifest = {
        "source_commit": head_sha,
        "mathlib_rev": existing.get("mathlib_rev") or "c5ea00351c28e24afc9f0f84379aa41082b1188f",
        "public_dependencies": {},
        "source_blobs": existing.get("source_blobs") or {},
        "sha256": {name: sha256_text(text) for name, text in files.items()},
        "publishable": (destination / "problem.json").is_file() and (destination / "explanation.md").is_file(),
    }
    for name, digest in evidence["sha256"].items():
        if name in manifest["sha256"] and manifest["sha256"][name] != digest:
            raise RuntimeError(f"hash mismatch while freezing {name}")
    dump_json(destination / "manifest.json", manifest)
    return manifest


def verify_packets(
    workspace: Path,
    packets: list[str],
    head_sha: str,
    out: Path,
    targets: list[str] | None = None,
    runner: Callable[[Path], tuple[int, str]] | None = None,
    builder: Callable[[Path, list[str]], None] | None = None,
) -> dict[str, Any]:
    from check_lean_axiom_log import audit

    selected_targets = [normalize_target(item) for item in targets or []]
    if not packets and not selected_targets:
        raise RequestError("verification requires a packet directory or --targets Module.Name")
    (builder or build_targets)(workspace, selected_targets)
    compile = runner or lean_runner(workspace)
    out.mkdir(parents=True, exist_ok=True)
    results = []
    for relative in packets:
        source = workspace / relative
        stored = Path(relative).relative_to(PACKET_ROOT).as_posix()
        destination = out / "packets" / stored
        copy_packet(source, destination)
        evidence = compile_packet(destination, compile, audit)
        manifest = freeze_manifest(source, destination, head_sha, evidence)
        results.append(
            {
                "path": relative,
                "name": stored,
                "publishable": bool(manifest["publishable"]),
                "sha256": manifest["sha256"],
                "axioms": evidence["axioms"],
            }
        )
    summary = {
        "head_sha": head_sha,
        "packets": results,
        "targets": selected_targets,
        "target_results": [{"name": name, "status": "built"} for name in selected_targets],
        "module_only": not bool(results),
    }
    dump_json(out / "artifact.json", summary)
    return summary


def validate_artifact_packet(packet: Path) -> dict[str, Any]:
    manifest = load_json(packet / "manifest.json")
    evidence = load_json(packet / "packet-audit.json")
    if evidence.get("status") != "PASS":
        raise RuntimeError(f"{packet.name} packet-audit.json is not PASS")
    if manifest.get("public_dependencies") != {}:
        raise RuntimeError(f"{packet.name} is not self-contained")
    for name, digest in manifest["sha256"].items():
        path = packet / name
        if not path.is_file():
            raise RuntimeError(f"{packet.name} is missing {name}")
        if sha256_file(path) != digest:
            raise RuntimeError(f"{packet.name} {name} does not match the frozen hash")
    for name in ("driver.lean", "solution.lean"):
        if evidence["sha256"].get(name) != manifest["sha256"].get(name):
            raise RuntimeError(f"{packet.name} audit hash for {name} does not match the manifest")
        if evidence.get("exit_codes", {}).get(name) != 0:
            raise RuntimeError(f"{packet.name} {name} did not compile")
    if FORBIDDEN.search((packet / "solution.lean").read_text(encoding="utf-8")):
        raise RuntimeError(f"{packet.name} solution.lean contains a forbidden admission")
    return manifest


def whitespace_norm(text: str) -> str:
    return " ".join(text.split())


def wait_until(load: Callable[[], dict[str, Any]], done: Callable[[dict[str, Any]], bool], timeout: int, pause: float = 4.0) -> dict[str, Any]:
    deadline = time.monotonic() + timeout
    while True:
        result = load()
        if done(result):
            return result
        if time.monotonic() >= deadline:
            raise TimeoutError("Prove2Me job did not finish in time")
        time.sleep(pause)


def api_client():
    from publish_projective_small_blocks import VersionCheckedAPI

    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY is unavailable to the trusted publisher")
    return VersionCheckedAPI(key)


def existing_theorem(api, theorem_name: str, mathlib_rev: str) -> dict[str, Any] | None:
    query = urlencode({"q": theorem_name, "env": mathlib_rev})
    payload = api.request("/theorems?" + query)
    rows = [
        row
        for row in payload.get("theorems") or payload.get("items") or []
        if row.get("theorem_name") == theorem_name
    ]
    if not rows and payload.get("total"):
        rows = payload.get("theorems") or []
    if not rows:
        return None
    if len(rows) != 1:
        raise RuntimeError(f"theorem-name collision for {theorem_name}: {len(rows)} rows")
    return api.request("/theorems/" + rows[0]["theorem_id"])


def publish_job_rows(payload: dict[str, Any]) -> list[dict[str, Any]]:
    for key in ("jobs", "items", "publish_jobs"):
        rows = payload.get(key)
        if isinstance(rows, list):
            return [row for row in rows if isinstance(row, dict)]
    return []


def matching_publish_jobs(api, problem: dict[str, Any], mathlib_rev: str) -> list[dict[str, Any]]:
    """Return exact matching active/published problem-registration jobs.

    This is the durable retry guard for an asynchronous submit-problem call. A
    timed-out GitHub job must resume the already queued Prove2Me job rather than
    enqueueing the same theorem again. Jobs are accepted only when the theorem
    name matches and every available disambiguator (statement/environment)
    agrees with the frozen packet.
    """
    payload = api.request("/publish-jobs?" + urlencode({"kind": "problem", "limit": 100, "offset": 0}))
    wanted_statement = whitespace_norm(problem.get("formal_statement") or "")
    matches: list[dict[str, Any]] = []
    for row in publish_job_rows(payload):
        if row.get("theorem_name") != problem.get("theorem_name"):
            continue
        statement = row.get("formal_statement")
        if statement is not None and whitespace_norm(str(statement)) != wanted_statement:
            continue
        row_env = row.get("mathlib_rev") or row.get("env")
        if row_env is not None and str(row_env) != mathlib_rev:
            continue
        # If neither statement nor environment is echoed, theorem_name alone is
        # insufficient because names are unique only within an environment.
        if statement is None and row_env is None:
            continue
        if row.get("status") in ACTIVE_PUBLISH | {"PUBLISHED"}:
            matches.append(row)
    return matches


def recover_publish_job(api, problem: dict[str, Any], mathlib_rev: str) -> dict[str, Any] | None:
    matches = matching_publish_jobs(api, problem, mathlib_rev)
    published = [row for row in matches if row.get("status") == "PUBLISHED" and row.get("theorem_id")]
    if published:
        # A completed exact job is unambiguous even if an obsolete duplicate is
        # still visible in the history; prefer the newest list entry.
        return published[0]
    active = [row for row in matches if row.get("status") in ACTIVE_PUBLISH]
    if len(active) > 1:
        ids = [str(row.get("id") or row.get("job_id") or "?") for row in active]
        raise RuntimeError(
            f"multiple active publish jobs match {problem.get('theorem_name')}: {', '.join(ids)}"
        )
    return active[0] if active else None


def publish_packet(api, packet: Path, timeout: int = 480) -> dict[str, Any]:
    manifest = validate_artifact_packet(packet)
    if not manifest.get("publishable"):
        return {
            "packet": packet.name,
            "status": "SKIPPED_NOT_PUBLISHABLE",
            "reason": "packet compiled but lacks problem.json/explanation.md",
        }
    problem = load_json(packet / "problem.json")
    live = existing_theorem(api, problem["theorem_name"], manifest["mathlib_rev"])
    dump_json(packet / "duplicate-check.json", {"existing": live})
    if live is None:
        prior = recover_publish_job(api, problem, manifest["mathlib_rev"])
        if prior is None:
            queued = api.request("/submit-problem", problem, "POST")
            dump_json(packet / "publish-response.json", queued)
            job_id = queued.get("job_id") or (queued.get("jobs") or [{}])[0].get("job_id")
            registration = "QUEUED"
        else:
            dump_json(packet / "publish-response.json", {"resumed": True, "job": prior})
            job_id = prior.get("id") or prior.get("job_id")
            registration = "RESUMED"
            if prior.get("status") == "PUBLISHED" and prior.get("theorem_id"):
                job_id = None
                theorem_id = prior["theorem_id"]
                registration = "RESUMED_PUBLISHED"
        if prior is None or prior.get("status") != "PUBLISHED":
            if not job_id:
                raise RuntimeError(f"{packet.name} publication did not return a job id")
            try:
                job = wait_until(
                    lambda: api.request("/publish-jobs/" + str(job_id)),
                    lambda data: data.get("status") in TERMINAL_PUBLISH,
                    timeout=timeout,
                )
            except TimeoutError:
                latest = api.request("/publish-jobs/" + str(job_id))
                dump_json(packet / "publish-job.json", latest)
                return {
                    "packet": packet.name,
                    "status": "PUBLISH_PENDING",
                    "publish_job_id": job_id,
                    "theorem_name": problem["theorem_name"],
                    "registration": registration,
                    "reason": "problem registration is still pending; rerun resumes this exact job",
                }
            dump_json(packet / "publish-job.json", job)
            if job.get("status") != "PUBLISHED":
                raise RuntimeError(f"{packet.name} publication failed: {job.get('status')}")
            theorem_id = job["theorem_id"]
            registration = "PUBLISHED" if registration == "QUEUED" else "RESUMED_PUBLISHED"
        else:
            dump_json(packet / "publish-job.json", prior)
    else:
        if whitespace_norm(live.get("formal_statement") or "") != whitespace_norm(problem["formal_statement"]):
            raise RuntimeError(f"{packet.name} existing theorem has a different formal statement")
        theorem_id = live["theorem_id"]
        registration = "REUSED"
        dump_json(packet / "publish-job.json", {"status": "PUBLISHED", "theorem_id": theorem_id, "reused": True})

    live = api.request("/theorems/" + theorem_id)
    dump_json(packet / "target-before.json", live)
    if live.get("status") == "Proved":
        summary = {
            "packet": packet.name,
            "status": "SKIPPED_ALREADY_PROVED",
            "theorem_id": theorem_id,
            "theorem_name": problem["theorem_name"],
            "registration": registration,
        }
        dump_json(packet / "verification.json", {"status": "ACCEPTED", "skipped": True, "theorem_id": theorem_id})
        return summary

    queued = api.verify(theorem_id, (packet / "solution.lean").read_text(encoding="utf-8"), (packet / "explanation.md").read_text(encoding="utf-8"))
    dump_json(packet / "verify-response.json", queued)
    submission_id = queued.get("submission_id") or queued.get("id")
    if not submission_id:
        raise RuntimeError(f"{packet.name} verify did not return a submission id")
    verdict = wait_until(
        lambda: api.request("/verify?" + urlencode({"submission_id": submission_id})),
        lambda data: data.get("status") in TERMINAL_VERIFY,
        timeout=timeout,
    )
    dump_json(packet / "verification.json", verdict)
    summary = {
        "packet": packet.name,
        "status": verdict.get("status"),
        "theorem_id": theorem_id,
        "submission_id": submission_id,
        "theorem_name": problem["theorem_name"],
        "registration": registration,
    }
    if verdict.get("status") == "ACCEPTED":
        after = api.request("/theorems/" + theorem_id)
        dump_json(packet / "target-after.json", after)
        if after.get("status") != "Proved":
            raise RuntimeError(f"{packet.name} was ACCEPTED but live status is {after.get('status')}")
        proof = api.request("/submissions/" + submission_id + "/solution")
        dump_json(packet / "accepted-source-readback.json", proof)
        if proof.get("content") != (packet / "solution.lean").read_text(encoding="utf-8"):
            raise RuntimeError(f"{packet.name} accepted source does not match the frozen packet")
        dump_json(
            packet / "accepted-source-hash.json",
            {"status": "PASS", "submission_id": submission_id, "sha256": sha256_file(packet / "solution.lean")},
        )
        summary["live_status"] = after.get("status")
    return summary


def publish_artifact(artifact: Path, out: Path, timeout: int = 480) -> dict[str, Any]:
    summary = load_json(artifact / "artifact.json")
    if summary.get("module_only") or not summary.get("packets"):
        raise RuntimeError("publication requires a verified packet; module-only --targets verification cannot be published")
    api = api_client()
    results = []
    for item in summary["packets"]:
        packet = artifact / "packets" / item["name"]
        if item.get("publishable") is False:
            results.append(
                {
                    "packet": item["name"],
                    "path": item["path"],
                    "status": "SKIPPED_NOT_PUBLISHABLE",
                    "reason": "packet compiled but lacks problem.json/explanation.md",
                }
            )
            continue
        result = publish_packet(api, packet, timeout=timeout)
        result["path"] = item["path"]
        results.append(result)
    receipt = {
        "head_sha": summary.get("head_sha"),
        "packets": results,
    }
    dump_json(out / "publication-receipt.json", receipt)
    return receipt


def packet_items(payload: dict[str, Any]) -> list[dict[str, Any]]:
    items: list[dict[str, Any]] = []
    for item in payload.get("packets") or []:
        if isinstance(item, str):
            items.append({"packet": item, "path": item, "status": payload.get("action") or "queued"})
        else:
            items.append(item)
    return items


def comment_markdown(kind: str, payload: dict[str, Any], run_url: str = "") -> str:
    lines = [f"## Prove2Me {kind}"]
    if payload.get("head_sha"):
        lines.append(f"Head SHA: `{payload['head_sha']}`")
    if run_url:
        lines.append(f"Actions run: {run_url}")
    if payload.get("targets"):
        lines.append("Lake targets: " + ", ".join(f"`{name}`" for name in payload["targets"]))
    if payload.get("module_only"):
        lines.append("Module-only verification: no packet was published or submitted.")
    for item in packet_items(payload):
        name = item.get("theorem_name") or item.get("packet") or item.get("name")
        status = item.get("status") or kind
        lines.append(f"- **{name}**: {status}")
        if item.get("theorem_id"):
            lines.append(f"  - theorem `{item['theorem_id']}`")
        if item.get("submission_id"):
            lines.append(f"  - submission `{item['submission_id']}`")
        if item.get("publish_job_id"):
            lines.append(f"  - publish job `{item['publish_job_id']}`")
        if item.get("reason"):
            lines.append(f"  - {item['reason']}")
        if item.get("path"):
            lines.append(f"  - `{item['path']}`")
    if payload.get("error"):
        lines.append("")
        lines.append(redact(str(payload["error"])))
    lines.append("")
    lines.append("Local compilation is not a Prove2Me verdict. Only an authenticated platform response is.")
    return redact("\n".join(lines) + "\n")


def write_github_output(name: str, value: str) -> None:
    output = os.environ.get("GITHUB_OUTPUT")
    if not output:
        print(f"{name}={value}")
        return
    with open(output, "a", encoding="utf-8") as handle:
        if "\n" in value:
            handle.write(f"{name}<<EOF\n{value}\nEOF\n")
        else:
            handle.write(f"{name}={value}\n")


def cmd_parse(args: argparse.Namespace) -> int:
    if args.comment_file is not None:
        comment = args.comment_file.read_text(encoding="utf-8")
    elif args.comment is not None:
        comment = args.comment
    else:
        raise RequestError("parse requires --comment or --comment-file")
    try:
        request = parse_comment(comment, args.actor)
    except RequestError as exc:
        print(redact(str(exc)), file=sys.stderr)
        write_github_output("should_run", "false")
        write_github_output("error", str(exc))
        return 1
    dump_json(args.out, request)
    write_github_output("should_run", "true")
    write_github_output("action", request["action"])
    write_github_output("request_json", json.dumps(request, separators=(",", ":")))
    return 0


def cmd_select(args: argparse.Namespace) -> int:
    request = load_json(args.request)
    files = [line.strip() for line in Path(args.files).read_text(encoding="utf-8").splitlines() if line.strip()]
    try:
        packets = select_packets(request, files, Path(args.workspace))
    except RequestError as exc:
        print(redact(str(exc)), file=sys.stderr)
        write_github_output("should_run", "false")
        write_github_output("error", str(exc))
        return 1
    resolved = {
        **request,
        "packets": packets,
        "targets": request.get("targets") or [],
        "module_only": request.get("action") == "verify" and not packets,
        "head_sha": args.head_sha,
        "pr": args.pr,
    }
    dump_json(args.out, resolved)
    write_github_output("should_run", "true")
    write_github_output("head_sha", args.head_sha)
    write_github_output("packets", " ".join(packets))
    write_github_output("targets", " ".join(request.get("targets") or []))
    write_github_output("action", request["action"])
    write_github_output("resolved_json", json.dumps(resolved, separators=(",", ":")))
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    request = load_json(args.request)
    summary = verify_packets(
        Path(args.workspace),
        request["packets"],
        request["head_sha"],
        Path(args.out),
        targets=request.get("targets") or [],
    )
    (Path(args.out) / "pr-comment.md").write_text(comment_markdown("verification", summary, args.run_url), encoding="utf-8")
    return 0


def cmd_publish(args: argparse.Namespace) -> int:
    receipt = publish_artifact(Path(args.artifact), Path(args.out), timeout=args.timeout)
    markdown = comment_markdown("publication", receipt, args.run_url)
    (Path(args.out) / "pr-comment.md").write_text(markdown, encoding="utf-8")
    print(markdown)
    failed = [
        item
        for item in receipt["packets"]
        if item.get("status")
        not in {"ACCEPTED", "SKIPPED_ALREADY_PROVED", "SKIPPED_NOT_PUBLISHABLE", "PUBLISH_PENDING"}
    ]
    return 1 if failed else 0


def cmd_comment(args: argparse.Namespace) -> int:
    payload = load_json(args.payload) if args.payload else {}
    print(comment_markdown(args.kind, payload, args.run_url), end="")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    parse_cmd = sub.add_parser("parse")
    parse_cmd.add_argument("--comment")
    parse_cmd.add_argument("--comment-file", type=Path)
    parse_cmd.add_argument("--actor", required=True)
    parse_cmd.add_argument("--out", type=Path, required=True)
    parse_cmd.set_defaults(func=cmd_parse)

    select_cmd = sub.add_parser("select")
    select_cmd.add_argument("--request", type=Path, required=True)
    select_cmd.add_argument("--files", type=Path, required=True)
    select_cmd.add_argument("--workspace", type=Path, required=True)
    select_cmd.add_argument("--head-sha", required=True)
    select_cmd.add_argument("--pr", required=True)
    select_cmd.add_argument("--out", type=Path, required=True)
    select_cmd.set_defaults(func=cmd_select)

    verify_cmd = sub.add_parser("verify")
    verify_cmd.add_argument("--request", type=Path, required=True)
    verify_cmd.add_argument("--workspace", type=Path, required=True)
    verify_cmd.add_argument("--out", type=Path, required=True)
    verify_cmd.add_argument("--run-url", default="")
    verify_cmd.set_defaults(func=cmd_verify)

    publish_cmd = sub.add_parser("publish")
    publish_cmd.add_argument("--artifact", type=Path, required=True)
    publish_cmd.add_argument("--out", type=Path, required=True)
    publish_cmd.add_argument("--run-url", default="")
    publish_cmd.add_argument("--timeout", type=int, default=480)
    publish_cmd.set_defaults(func=cmd_publish)

    comment_cmd = sub.add_parser("comment")
    comment_cmd.add_argument("--kind", required=True)
    comment_cmd.add_argument("--payload", type=Path)
    comment_cmd.add_argument("--run-url", default="")
    comment_cmd.set_defaults(func=cmd_comment)

    args = parser.parse_args()
    try:
        return args.func(args)
    except RequestError as exc:
        print(redact(str(exc)), file=sys.stderr)
        return 2
    except Exception as exc:
        print(redact(str(exc)), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
