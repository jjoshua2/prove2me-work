# H-description network continuation: verification handoff

Continue the active direct-routing PR #210; do not overwrite its existing
sources or the independent #208 publication work. This packet adds files only.
It does not require the unpushed selective-carrier packet.

## What is new and what is classical

The dual-network-flow edge bound is classical (Borgwardt--Finhold--Hemmecke,
arXiv:1408.4184). The new delivered work is an exact original-H router and
checker, explicit degeneracy handling with zero-distance tree pivots, actual
common-face normalization and path-certified redundancy removal, automatic
positive-diagonal gain recognition, and the actual-carrier D+6H(n-d) assembly.
No new classical diameter bound or universal Hirsch conclusion is asserted.

## Local gates

```sh
python3 -m py_compile scripts/network_potential_router.py \
  scripts/network_carrier_normalization.py \
  scripts/test_network_potential_router.py scripts/test_network_normalization.py
python3 scripts/test_network_potential_router.py
python3 scripts/test_network_normalization.py
python3 scripts/network_potential_router.py fixtures/perturbed50_input.json
python3 scripts/network_carrier_normalization.py fixtures/dense24_normalized_input.json
lake build Solutions.PolynomialNetworkForestEdges \
  Solutions.PolynomialNetworkFaceQuotient \
  Solutions.PolynomialNetworkCarrierBudget
```

The three Lean modules are NEW UNCOMPILED candidates, with15 axiom printouts.
Audit the standard logical axiom closure locally before a hosted gate. Likely
API-sensitive spots: graph-walk constructor induction, Fin.sum_univ_castSucc,
Pi scalar simplification, and the implicit inequality-face structure of Adj.
Do not weaken two-component connectivity into just a proposed cut direction.

## Scope that must survive verification

1. Every basis edge is tight in the ORIGINAL system; every positive move has
   a two-component common tight graph. Theta=0 is a basis exchange, not an edge.
2. Lock an initial forest spanning ALL common tight equations, not merely a
   convenient subset of a chosen target tree. The route stays in the actual
   smallest endpoint face.
3. Each phase's protected arborescence grows monotonically, and deleted
   original arcs/unordered quotient pairs do not recur. Final target insertion
   can require a separate zero exchange; this adds no ordinary-edge cost.
4. The quotient lift is onto the exact common-equality face. Every removed row
   has a sequential path implication; minimality is independently checked for
   the intrinsic M used by the aggregate theorem.
5. The H-recognizer checks all multiplicative gain cycles and every row. It
   does not recognize arbitrary affine disguises or every two-variable system.
6. The method is not claimed globally shortest or monotone in any arbitrary
   objective. In a cube pyramid, preserving the common base face can cost r
   edges where a two-edge ambient shortcut exists.

## Formalization boundary

The complete finite algorithm and its degeneracy/termination proof are written
in the mathematical note. The new Lean cores prove graph-constant kernels,
vertices/edges, affine row identities and surjectivity primitives, path
implication, phase-label counting, and selected-pair aggregation. They do NOT
yet constitute a complete all-network-input existence theorem or an automatic
Lean H-to-network classifier. Do not report one merely because these cores
compile. Numerical certificates are not emitted Lean proof terms.

The candidate budget wrapper consumes actual selected-pair routes and actual
minimum-row bounds; it does not call a whole-face high-dimensional diameter
oracle. A future wrapper should derive both from a verified NetworkImage and
the completed pivot constructor. Publication requires its own exact interface
and authenticated acceptance, not an inference from these local tests.

## Reproduction and files

Both test scripts are self-contained standard-library rational arithmetic.
They regenerate all numerical inputs and certificates under fixtures. Detailed
execution receipts are in research/NETWORK_*_CHECK_2026-09-12.json, with source
hashes. The conversation ZIP includes the regenerated large cases as well.
No whole graph was enumerated for the24D/50D/32D network examples.

The cube-pyramid direction-count obstruction is an elementary infinite-family
argument in the note, not a new Lean declaration. It explains why the network
normal-matrix criterion goes beyond #210's polynomial direction-count regime:
47 H-facets can coexist with8,388,608 true apex edge directions in dimension24.
