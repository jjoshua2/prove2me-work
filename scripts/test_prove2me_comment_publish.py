#!/usr/bin/env python3
"""Unit tests for the comment-triggered Prove2Me publisher. No network, no Lean."""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import prove2me_comment_publish as pub


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text if text.endswith("\n") else text + "\n", encoding="utf-8")


AXIOM_LOG = "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
SOLUTION = """import Mathlib
theorem solution (n : Nat) : n + 0 = n := by
  simp
#print axioms solution
"""
STATEMENT = """import Mathlib
theorem Demo.add_zero (n : Nat) : n + 0 = n := by sorry
"""
PROBLEM = {
    "theorem_name": "Demo.add_zero",
    "theorem_title": "n+0=n",
    "formal_statement": "theorem Demo.add_zero (n : Nat) : n + 0 = n := by sorry",
    "natural_language_statement": "Zero is a right identity.",
    "preamble": "import Mathlib",
    "source": "unit test",
    "tags": ["test"],
    "env": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
}


class ParseTests(unittest.TestCase):
    def test_exact_publish_command(self) -> None:
        request = pub.parse_comment("/prove2me publish\n", "jjoshua2")
        self.assertEqual(request["action"], "publish")
        self.assertEqual(request["packets"], [])
        self.assertEqual(request["targets"], [])

    def test_publish_with_packets_and_targets(self) -> None:
        body = (
            "/prove2me publish --targets Solutions.Foo,Solutions.Bar "
            "research/publication_packets/pr210_catchup/direction_local_budget\n"
        )
        request = pub.parse_comment(body, "jjoshua2")
        self.assertEqual(request["targets"], ["Solutions.Foo", "Solutions.Bar"])
        self.assertEqual(
            request["packets"],
            ["research/publication_packets/pr210_catchup/direction_local_budget"],
        )

    def test_verify_verb(self) -> None:
        request = pub.parse_comment("/prove2me verify packing_downward\n", "jjoshua2")
        self.assertEqual(request["action"], "verify")
        self.assertEqual(request["packets"], ["packing_downward"])

    def test_verify_targets_only(self) -> None:
        request = pub.parse_comment(
            "/prove2me verify --targets Solutions.PolynomialDirectionLocalBudgets\n",
            "jjoshua2",
        )
        self.assertEqual(request["action"], "verify")
        self.assertEqual(request["packets"], [])
        self.assertEqual(request["targets"], ["Solutions.PolynomialDirectionLocalBudgets"])

    def test_rejects_invalid_target(self) -> None:
        with self.assertRaises(pub.RequestError):
            pub.parse_comment("/prove2me verify --targets ../Secrets\n", "jjoshua2")
        with self.assertRaises(pub.RequestError):
            pub.parse_comment("/prove2me verify --targets foo;rm\n", "jjoshua2")

    def test_rejects_other_actors(self) -> None:
        with self.assertRaises(pub.RequestError):
            pub.parse_comment("/prove2me publish\n", "someone-else")

    def test_rejects_non_command(self) -> None:
        with self.assertRaises(pub.RequestError):
            pub.parse_comment("please publish this\n", "jjoshua2")
        with self.assertRaises(pub.RequestError):
            pub.parse_comment("/prove2me\n", "jjoshua2")

    def test_rejects_unknown_flag(self) -> None:
        with self.assertRaises(pub.RequestError):
            pub.parse_comment("/prove2me publish --please-do-it\n", "jjoshua2")


class PathTests(unittest.TestCase):
    def test_accepts_short_and_full_paths(self) -> None:
        self.assertEqual(
            pub.normalize_packet_path("pr210_catchup/direction_local_budget"),
            "research/publication_packets/pr210_catchup/direction_local_budget",
        )
        self.assertEqual(
            pub.normalize_packet_path("research/publication_packets/foo"),
            "research/publication_packets/foo",
        )

    def test_rejects_traversal(self) -> None:
        with self.assertRaises(pub.RequestError):
            pub.normalize_packet_path("../Secrets")
        with self.assertRaises(pub.RequestError):
            pub.normalize_packet_path("/etc/passwd")
        with self.assertRaises(pub.RequestError):
            pub.normalize_packet_path("research/publication_packets/../Solutions")


class SelectTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.packet = self.root / "research/publication_packets/pr210_catchup/direction_local_budget"
        write(self.packet / "solution.lean", SOLUTION)
        self.accepted = self.root / "research/publication_packets/near_geodesic_budget"
        write(self.accepted / "solution.lean", SOLUTION)
        write(self.accepted / "accepted-source-hash.json", '{"status":"PASS"}')

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def test_discovers_new_packet_and_skips_accepted(self) -> None:
        files = [
            "research/publication_packets/pr210_catchup/direction_local_budget/solution.lean",
            "research/publication_packets/near_geodesic_budget/solution.lean",
            "Solutions/PolynomialDirectionLocalBudgets.lean",
        ]
        found = pub.select_packets({"packets": []}, files, self.root)
        self.assertEqual(
            found,
            ["research/publication_packets/pr210_catchup/direction_local_budget"],
        )

    def test_specified_packet_is_not_required_on_main(self) -> None:
        found = pub.select_packets({"packets": ["missing-on-main"]}, [], self.root)
        self.assertEqual(found, ["research/publication_packets/missing-on-main"])

    def test_specified_packet_wins(self) -> None:
        found = pub.select_packets(
            {"packets": ["research/publication_packets/pr210_catchup/direction_local_budget"]},
            [],
            self.root,
        )
        self.assertEqual(len(found), 1)

    def test_verify_targets_only_skips_packet_discovery(self) -> None:
        found = pub.select_packets(
            {"action": "verify", "packets": [], "targets": ["Solutions.Foo"]},
            ["research/publication_packets/pr210_catchup/direction_local_budget/solution.lean"],
            self.root,
        )
        self.assertEqual(found, [])

    def test_publish_still_requires_a_packet(self) -> None:
        with self.assertRaises(pub.RequestError):
            pub.select_packets(
                {"action": "publish", "packets": [], "targets": ["Solutions.Foo"]},
                [],
                self.root / "empty",
            )


class VerifyTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.packet = self.root / "research/publication_packets/demo"
        write(self.packet / "solution.lean", SOLUTION)
        write(self.packet / "problem.json", json.dumps(PROBLEM, indent=2))
        write(self.packet / "explanation.md", "Zero is a right identity.")
        write(self.packet / "statement.lean", STATEMENT)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def runner(self, source: Path):
        if "sorry" in source.read_text(encoding="utf-8") and source.name == "solution.lean":
            return 1, "error: sorry"
        return 0, AXIOM_LOG

    def test_complete_packet_is_publishable(self) -> None:
        out = self.root / "_verified"
        summary = pub.verify_packets(
            self.root,
            ["research/publication_packets/demo"],
            "abc123",
            out,
            runner=self.runner,
        )
        self.assertTrue(summary["packets"][0]["publishable"])
        frozen = out / "packets/demo"
        self.assertEqual(json.loads((frozen / "packet-audit.json").read_text())["status"], "PASS")
        self.assertTrue(json.loads((frozen / "manifest.json").read_text())["publishable"])

    def test_incomplete_packet_verifies_but_is_not_publishable(self) -> None:
        incomplete = self.root / "research/publication_packets/partial"
        write(incomplete / "solution.lean", SOLUTION)
        out = self.root / "_verified"
        summary = pub.verify_packets(
            self.root,
            ["research/publication_packets/partial"],
            "abc123",
            out,
            runner=self.runner,
        )
        self.assertFalse(summary["packets"][0]["publishable"])

    def test_rejects_sorry_in_solution(self) -> None:
        write(self.packet / "solution.lean", SOLUTION.replace("simp", "sorry"))
        with self.assertRaises(pub.RequestError):
            pub.verify_packets(
                self.root,
                ["research/publication_packets/demo"],
                "abc123",
                self.root / "_verified",
                runner=self.runner,
            )

    def test_module_only_verify_builds_targets(self) -> None:
        built: list[str] = []

        def builder(_workspace: Path, targets: list[str]) -> None:
            built.extend(targets)

        out = self.root / "_verified"
        summary = pub.verify_packets(
            self.root,
            [],
            "abc123",
            out,
            targets=["Solutions.PolynomialDirectionLocalBudgets"],
            runner=self.runner,
            builder=builder,
        )
        self.assertEqual(built, ["Solutions.PolynomialDirectionLocalBudgets"])
        self.assertTrue(summary["module_only"])
        self.assertEqual(summary["packets"], [])
        self.assertEqual(summary["targets"], ["Solutions.PolynomialDirectionLocalBudgets"])


class PublishGuardTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.packet = Path(self.tmp.name) / "packets/demo"
        write(self.packet / "solution.lean", SOLUTION)
        write(self.packet / "driver.lean", SOLUTION)
        write(self.packet / "statement.lean", STATEMENT)
        write(self.packet / "problem.json", json.dumps(PROBLEM, indent=2))
        write(self.packet / "explanation.md", "Zero is a right identity.")
        files = ["solution.lean", "driver.lean", "statement.lean", "problem.json", "explanation.md"]
        hashes = {name: pub.sha256_file(self.packet / name) for name in files}
        write(
            self.packet / "packet-audit.json",
            json.dumps(
                {
                    "status": "PASS",
                    "exit_codes": {"driver.lean": 0, "solution.lean": 0, "statement.lean": 0},
                    "sha256": {name: hashes[name] for name in ("driver.lean", "solution.lean", "statement.lean")},
                    "axioms": ["Classical.choice", "Quot.sound", "propext"],
                },
                indent=2,
            ),
        )
        write(
            self.packet / "manifest.json",
            json.dumps(
                {
                    "source_commit": "abc123",
                    "mathlib_rev": PROBLEM["env"],
                    "public_dependencies": {},
                    "sha256": hashes,
                    "publishable": True,
                },
                indent=2,
            ),
        )

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def test_hash_mismatch_is_rejected(self) -> None:
        write(self.packet / "solution.lean", SOLUTION + "-- mutated\n")
        with self.assertRaises(RuntimeError):
            pub.validate_artifact_packet(self.packet)

    def test_valid_artifact_passes(self) -> None:
        manifest = pub.validate_artifact_packet(self.packet)
        self.assertTrue(manifest["publishable"])

    def test_comment_redacts_keys(self) -> None:
        markdown = pub.comment_markdown(
            "publication",
            {"error": "failed with p2m_abcdefghijklmnopqrstuvwxyz and Bearer tok_secret"},
        )
        self.assertNotIn("p2m_", markdown)
        self.assertNotIn("tok_secret", markdown)
        self.assertIn("[redacted]", markdown)

    def test_missing_api_key_does_not_fall_back_to_file(self) -> None:
        with patch.dict("os.environ", {}, clear=True):
            with self.assertRaises(RuntimeError):
                pub.api_client()

    def test_module_only_artifact_cannot_be_published(self) -> None:
        artifact = Path(self.tmp.name)
        write(
            artifact / "artifact.json",
            json.dumps(
                {
                    "head_sha": "abc123",
                    "packets": [],
                    "targets": ["Solutions.Foo"],
                    "module_only": True,
                },
                indent=2,
            ),
        )
        with self.assertRaises(RuntimeError):
            pub.publish_artifact(artifact, artifact / "out")


class PolicyTests(unittest.TestCase):
    def test_comment_workflow_is_not_push_triggered(self) -> None:
        text = (Path(__file__).resolve().parents[1] / ".github/workflows/prove2me-comment-publish.yml").read_text(encoding="utf-8")
        self.assertIn("issue_comment:", text)
        self.assertNotRegex(text, r"(?m)^\s+push:")
        self.assertEqual(text.count("secrets.PROVE2ME_API_KEY"), 1)
        publish_at = text.index("\n  publish:\n")
        self.assertGreater(publish_at, text.index("\n  verify:\n"))
        self.assertIn("secrets.PROVE2ME_API_KEY", text[publish_at:])
        self.assertNotIn("secrets.PROVE2ME_API_KEY", text[:publish_at])
        report = text[text.index("\n  report-verify:\n"):]
        self.assertIn("GH_REPO: ${{ github.repository }}", report)
        self.assertNotIn("secrets.PROVE2ME_API_KEY", report)


if __name__ == "__main__":
    raise SystemExit(unittest.main())
