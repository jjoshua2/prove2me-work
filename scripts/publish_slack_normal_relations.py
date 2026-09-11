#!/usr/bin/env python3
"""Prepare/audit/publish the already source-verified PR92 slack certificate.

Preparation has no network or credential access. Publication reuses the frozen,
reviewed Prove2Me client, checks the exact audited bytes, and creates no sketches.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import subprocess
import types
from pathlib import Path

SOURCE = "4a9204edd7f03c7f9676f9dc9762be121e43bf1a"
SOURCE_RUN = "34615241828"
ROOT = "Solutions.PolynomialSlackNormalRelations"
EXPECTED = {
    "Solutions/PolynomialSlackMomentCertificate.lean": "90005f87a9939477770c515ec19345ec93765f2b",
    "Solutions/PolynomialSlackNormalRelations.lean": "d46a7c7ba16d3eda1aae038e3046522af3b83ec0",
}
CLIENT_COMMIT = "1692538ba9f7661ca079a86f2963fb48ac2270d1"
CLIENT_PATH = "scripts/publish_excess_two_diameter_two.py"
CLIENT_BLOB = "7da71d03920b59b688bae7cc8b4f9c15432adc4a"
PACKET = Path("/tmp/slack-relations-public")
OUT = Path("slack_relations_publication_receipts")
NAME = "Hirsch.hpoly_and_row_faces_diamLE_two_of_normal_relations"
TITLE = "Positive normal-relation certificates give intrinsic diameter two"
PREAMBLE = "import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch"
BINDERS = """    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (ht : ∃ i j, t i ≠ t j)
    (hfirst : (∑ i, c i • a i) = 0)
    (hsecond : (∑ i, (t i * c i) • a i) = 0)
    (hmass : (∑ i, c i * b i) = 1)
    (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b)) :
    DiamLE (Hpoly a b) 2 ∧
      ∀ S : Finset (Fin n),
        DiamLE {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} 2"""
FORMAL = "namespace Hirsch\ntheorem hpoly_and_row_faces_diamLE_two_of_normal_relations\n" + BINDERS + " := by sorry\nend Hirsch"
NATURAL = """Consider an n-row real H-polyhedron in R^d, with n=d+2 and a reference extreme vertex. Suppose c_i>0, the slopes t_i are not all equal, sum_i c_i a_i=0, sum_i t_i c_i a_i=0, and sum_i c_i b_i=1. Then the H-polyhedron has padded vertex-edge diameter at most two. Moreover every face obtained by requiring any chosen collection of the original inequalities to be tight has intrinsic padded graph diameter at most two. All hypotheses are finite normal-relation certificates; no diameter bound is assumed. Existence of such certificates from boundedness alone is not asserted."""
EXPLANATION = """The reference extreme vertex makes the positive-diagonally weighted row evaluation map injective: a vector in its kernel annihilates all active rows and is zero by a finite perturbation argument. The two normal identities annihilate its image. Nonconstant slopes make the mass/moment map onto R^2; rank-nullity and n=d+2 identify its kernel exactly with the weighted row-map image. Consequently the affine slack map x -> (c_i(b_i-<a_i,x>)) has image exactly the normalized nonnegative two-moment simplex slice, including the reverse inclusion. Strictly positive scaling identifies original inequalities with nonnegative slacks and original row tightness with zero slack coordinates. The complete two-moment vertex classification and support-preserving two-step routes bound the slice and every coordinate support face intrinsically by two. Injective affine graph transport pulls both bounds back. This does not prove existence of normal-relation witnesses from boundedness or close the high-dimensional Polynomial Hirsch frontier."""


def read_source(commit: str, path: str, expected: str | None = None) -> tuple[str, str]:
    data = subprocess.run(["git", "show", commit + ":" + path], check=True, capture_output=True).stdout
    blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if expected is not None and blob != expected:
        raise RuntimeError("immutable source blob mismatch: " + path)
    return data.decode("utf-8"), blob


def without_comments(text: str) -> str:
    """Remove nested block/line comments, retaining line breaks for scope scanning."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            quoted = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or quoted:
        raise RuntimeError("unterminated source comment/string")
    return "".join(out)


def expected_packet() -> tuple[bytes, list[dict]]:
    visited, visiting, imports, blocks, manifest = set(), set(), {"Mathlib"}, [], []
    def visit(module: str) -> None:
        if module in visited:
            return
        if module in visiting:
            raise RuntimeError("cyclic source imports")
        visiting.add(module)
        path = module.replace(".", "/") + ".lean"
        text, blob = read_source(SOURCE, path, EXPECTED.get(path))
        body = []
        for line in text.splitlines():
            match = re.fullmatch(r"\s*import\s+([A-Za-z0-9_.]+)\s*", line)
            if not match:
                body.append(line)
                continue
            dep = match.group(1)
            if dep.startswith("Solutions."):
                visit(dep)
            elif dep == "Mathlib" or dep.startswith("Mathlib.") or dep == "Definitions.Def_Hirsch_model":
                imports.add(dep)
            else:
                raise RuntimeError("unreviewed external import: " + dep)
        body_text = "\n".join(body) + "\n"
        code = without_comments(body_text)
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", code):
            raise RuntimeError("forbidden proof shortcut in " + path)
        depth = 0
        for line in code.splitlines():
            if re.match(r"^\s*(?:noncomputable\s+)?(?:section|namespace)\b", line):
                depth += 1
            elif re.match(r"^\s*end(?:\s|$)", line):
                depth -= 1
                if depth < 0:
                    raise RuntimeError("unbalanced source scopes in " + path)
        blocks.append("\n/- Frozen source: " + path + " -/\nsection\n" + body_text + "\nend\n" * (depth + 1))
        manifest.append({"path": path, "git_blob": blob})
        visiting.remove(module)
        visited.add(module)
    visit(ROOT)
    wrapper = "\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n\ntheorem solution\n" + BINDERS + " := by\n  exact HirschSlackMoment.hpoly_and_row_faces_diamLE_two_of_normal_relations\n    a b c t hn hc ht hfirst hsecond hmass z hz\n\n#print axioms solution\n"
    data = ("\n".join("import " + x for x in sorted(imports)) + "\n" + "".join(blocks) + wrapper).encode()
    return data, manifest


def prepare() -> None:
    data, sources = expected_packet()
    PACKET.mkdir(parents=True, exist_ok=True)
    (PACKET / "solution.lean").write_bytes(data)
    manifest = {"source_commit": SOURCE, "source_run": SOURCE_RUN, "sources": sources,
                "standalone_sha256": hashlib.sha256(data).hexdigest(), "theorem_name": NAME}
    (PACKET / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2), flush=True)


def publish() -> None:
    expected, _ = expected_packet()
    solution = PACKET / "solution.lean"
    proof_hash = hashlib.sha256(expected).hexdigest()
    if not solution.is_file() or solution.read_bytes() != expected:
        raise RuntimeError("standalone differs from frozen verified source")
    audit = PACKET / "audit-passed.sha256"
    if not audit.is_file() or audit.read_text().strip() != proof_hash:
        raise RuntimeError("standalone compile/axiom receipt absent or mismatched")
    text, _ = read_source(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB)
    slot = '"Normalized two-moment slices have graph diameter at most two"'
    if text.count(slot) != 1:
        raise RuntimeError("reviewed client title slot changed")
    text = text.replace(slot, repr(TITLE), 1)
    client = types.ModuleType("reviewed_slack_publication_client")
    exec(compile(text, CLIENT_PATH, "exec"), client.__dict__)
    client.VERSION = "0.10.1"
    client.SOURCE, client.SOURCE_RUN = SOURCE, SOURCE_RUN
    client.THEOREM_NAME, client.SOLUTION, client.SOLUTION_SHA256 = NAME, solution, proof_hash
    client.OUT, client.PREAMBLE, client.FORMAL = OUT, PREAMBLE, FORMAL
    client.NATURAL, client.EXPLANATION = NATURAL, EXPLANATION

    def link_mission(api, mission, result):
        mid, tid = mission["id"], result["theorem_id"]
        offset = 0
        while True:
            page = api.request(f"/missions/{mid}/comments?limit=100&offset={offset}")
            rows = page.get("comments", [])
            for comment in rows:
                if any(r.get("type") == "theorem" and r.get("id") == tid for r in comment.get("references", [])):
                    client.save(OUT / "mission-comment.json", comment)
                    return comment
            offset += len(rows)
            if not rows or len(rows) < 100 or offset >= int(page.get("total", offset + 1)):
                break
        body = (f"Published [positive-normal-relation diameter certificate](p2m:theorem/{tid})"
                + (f" with [accepted standalone proof](p2m:solution/{result['submission_id']})" if result.get("submission_id") else "")
                + ": with n=d+2, a reference vertex, positive c, nonconstant t, "
                "sum c_i a_i=0, sum t_i c_i a_i=0 and sum c_i b_i=1, the H-polyhedron "
                "AND every original row-support face have intrinsic padded diameter at most two. "
                "The kernel-verified construction proves exact slack-image equality by rank-nullity, "
                "not just image containment. This completes the certificate-to-geometry direction. "
                "Existence of the positive/independent relation witnesses from boundedness alone remains "
                "separate work; arbitrary circuit carriers are NOT assumed to have excess two. "
                "The Polynomial Hirsch root, high-dimensional common-face leaf, and circuit-to-edge "
                "refinement remain open. No conjectural child or new sketch was created. "
                "A potentially shorter diameter-only route is now worth checking: combine the newly "
                "proved sub-balanced section inheritance with facet dimension reduction, preserving "
                "n-d until the low-dimensional Hirsch base case. This last route is a proof plan, "
                "not claimed as a verified consequence in this post.")
        comment = api.request(f"/missions/{mid}/comments", {"body_md": body, "tags": ["reference", "strategy"]}, "POST")
        client.save(OUT / "mission-comment.json", comment)
        refs = {(r.get("type"), r.get("id")) for r in comment.get("references", [])}
        if ("theorem", tid) not in refs:
            raise RuntimeError("mission theorem reference unresolved")
        if result.get("submission_id") and ("solution", result["submission_id"]) not in refs:
            raise RuntimeError("mission solution reference unresolved")
        return comment

    client.link_mission = link_mission
    # Pull exact supporting interfaces for the next proof, without changing them.
    api = client.API(os.environ.get("PROVE2ME_API_KEY", ""))
    targets = {
        "facet_reduction": "11b3500a-b9f8-4b44-94aa-d71354441ddb",
        "subbalanced_sections": "0e4f233c-418a-4884-bbfb-dbfc7f76bc76",
        "dimension_three": "cf588038-4ee8-4c90-b034-348c28d0da21",
    }
    readback = {}
    for label, tid in targets.items():
        record = api.request("/theorems/" + tid)
        readback[label] = {k: record.get(k) for k in ("theorem_id", "theorem_name", "status", "mathlib_rev", "formal_statement", "preamble")}
    client.save(OUT / "next-proof-interfaces.json", readback)
    print("NEXT_PROOF_INTERFACES " + json.dumps(readback, ensure_ascii=False), flush=True)
    client.main()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["prepare", "publish"])
    args = parser.parse_args()
    prepare() if args.mode == "prepare" else publish()
