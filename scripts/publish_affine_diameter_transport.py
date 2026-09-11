#!/usr/bin/env python3
"""Build the checked affine-transport packet, then publish only after its audit.

The existing reviewed Prove2Me client is read from an immutable repository
commit; credentials are neither read nor used during --prepare.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import types

SOURCE = "be54654435d3c317d676f3ea03c79d07f089992a"
SOURCE_RUN = "34611873550"
SOURCE_PATH = "Solutions/PolynomialAffineDiameterTransport.lean"
SOURCE_BLOB = "ada90a58fe876f5e0b31ec20a0f8c22b1c408dd1"
CLIENT_COMMIT = "1692538ba9f7661ca079a86f2963fb48ac2270d1"
CLIENT_PATH = "scripts/publish_excess_two_diameter_two.py"
CLIENT_BLOB = "7da71d03920b59b688bae7cc8b4f9c15432adc4a"
PACKET = Path("/tmp/affine-diameter-public")
OUT = Path("affine_diameter_publication_receipts")
NAME = "Hirsch.injective_affine_image_diameter_iff"
TITLE = "Injective affine embeddings preserve vertex-edge diameter"
BINDERS = """    {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (P : Set E) (B : ℕ) :
    Hirsch.DiamLE (f '' P) B ↔ Hirsch.DiamLE P B"""
FORMAL = "namespace Hirsch\ntheorem injective_affine_image_diameter_iff\n" + BINDERS + " := by sorry\nend Hirsch"
PREAMBLE = "import Mathlib\nimport Definitions.Def_Hirsch_model\nopen Set"
NATURAL = (
    "Let E and F be real vector spaces, let f:E→F be an injective affine map, "
    "let P be any subset of E, and let B be a natural number. The vertex-edge "
    "graph of f(P) has padded diameter at most B if and only if the vertex-edge "
    "graph of P does. Adjacency means that the distinct endpoints span an "
    "extreme segment in the set. No surjectivity onto F, equal ambient "
    "dimensions, convexity, boundedness, nonemptiness, or positive B is assumed."
)
EXPLANATION = (
    "Affine maps carry segments and open segments to the corresponding image "
    "segments. Injectivity then preserves and reflects extreme subsets, hence "
    "extreme points and segment-face adjacency. Forward transport composes a "
    "padded walk with f. For reverse transport choose a total left inverse of f; "
    "every nonstationary edge has both endpoints in f(P), since its segment is "
    "an extreme subset of f(P). Pull these endpoints back and use reflected "
    "adjacency. Stationary steps pull back by equality and the endpoint "
    "identities use the left-inverse law. The proof also covers B=0 and sets "
    "without vertices. This supplies dimension-changing graph transport for "
    "slack-coordinate arguments, not the construction of a slack normalization."
)


def read_blob(commit: str, path: str, expected: str) -> bytes:
    data = subprocess.run(["git", "show", commit + ":" + path],
                          check=True, capture_output=True).stdout
    actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if actual != expected:
        raise RuntimeError("immutable source blob mismatch: " + path)
    return data


def expected_packet() -> bytes:
    source = read_blob(SOURCE, SOURCE_PATH, SOURCE_BLOB).decode("utf-8")
    wrapper = (
        "\n\ntheorem solution\n" + BINDERS + " := by\n"
        "  exact Hirsch.affineMap_diamLE_image_iff_of_injective f hf P B\n"
        "\n#print axioms solution\n"
    )
    return (source + wrapper).encode("utf-8")


def prepare() -> None:
    data = expected_packet()
    PACKET.mkdir(parents=True, exist_ok=True)
    (PACKET / "solution.lean").write_bytes(data)
    manifest = {
        "source_commit": SOURCE, "source_run": SOURCE_RUN,
        "source_path": SOURCE_PATH, "source_git_blob": SOURCE_BLOB,
        "standalone_sha256": hashlib.sha256(data).hexdigest(),
        "theorem_name": NAME,
        "evidence_level": "generated source; compilation and axiom audit still required",
    }
    (PACKET / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2), flush=True)


def publish() -> None:
    expected = expected_packet()
    solution = PACKET / "solution.lean"
    if not solution.is_file() or solution.read_bytes() != expected:
        raise RuntimeError("standalone packet differs from the immutable source and wrapper")
    audit = PACKET / "audit-passed.sha256"
    proof_hash = hashlib.sha256(expected).hexdigest()
    if not audit.is_file() or audit.read_text().strip() != proof_hash:
        raise RuntimeError("compile/axiom gate receipt is absent or names another proof")
    text = read_blob(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB).decode("utf-8")
    old_title = '"Normalized two-moment slices have graph diameter at most two"'
    if text.count(old_title) != 1:
        raise RuntimeError("reviewed client title slot changed")
    text = text.replace(old_title, repr(TITLE), 1)
    client = types.ModuleType("reviewed_prove2me_publication_client")
    exec(compile(text, CLIENT_PATH, "exec"), client.__dict__)
    client.VERSION = "0.10.1"
    client.SOURCE = SOURCE
    client.SOURCE_RUN = SOURCE_RUN
    client.THEOREM_NAME = NAME
    client.SOLUTION = solution
    client.SOLUTION_SHA256 = proof_hash
    client.OUT = OUT
    client.PREAMBLE = PREAMBLE
    client.FORMAL = FORMAL
    client.NATURAL = NATURAL
    client.EXPLANATION = EXPLANATION

    def link_mission(api, mission, result):
        tid = result["theorem_id"]
        mid = mission["id"]
        offset = 0
        while True:
            page = api.request(f"/missions/{mid}/comments?limit=100&offset={offset}")
            comments = page.get("comments", [])
            for comment in comments:
                if any(r.get("type") == "theorem" and r.get("id") == tid
                       for r in comment.get("references", [])):
                    client.save(OUT / "mission-comment.json", comment)
                    return comment
            offset += len(comments)
            if not comments or len(comments) < 100 or offset >= int(page.get("total", offset + 1)):
                break
        body = (
            f"Published [injective affine diameter transport](p2m:theorem/{tid})"
            + (f" with its [accepted proof](p2m:solution/{result['submission_id']})"
               if result.get("submission_id") else "")
            + ": an injective affine embedding preserves and reflects extreme points, "
            "edges, and every padded graph-diameter bound, even when ambient dimensions "
            "differ. This completes the graph-semantics transport part needed to apply "
            "the normalized two-moment diameter-two theorem to slack coordinates. "
            "The concrete positive-weight/codimension-two slack normalization still "
            "needs a separate proof. The d≥4 polynomial edge-refinement frontier is unchanged."
        )
        comment = api.request(f"/missions/{mid}/comments",
                              {"body_md": body, "tags": ["reference"]}, "POST")
        client.save(OUT / "mission-comment.json", comment)
        refs = {(r.get("type"), r.get("id")) for r in comment.get("references", [])}
        if ("theorem", tid) not in refs:
            raise RuntimeError("mission theorem reference was not resolved")
        if result.get("submission_id") and ("solution", result["submission_id"]) not in refs:
            raise RuntimeError("mission proof reference was not resolved")
        return comment

    client.link_mission = link_mission
    client.main()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["prepare", "publish"])
    args = parser.parse_args()
    prepare() if args.mode == "prepare" else publish()
