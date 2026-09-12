# Verification handoff: portal debt, strict-geodesic obstruction, safe relaxation

## Coordination

Independent branch from main `321f473d871aad2d692595acd97a667d6a648d06`.
Do not modify or re-verify #205/#206 merely to use these files. All three new
Lean imports resolve on this base. No new workflow, pin change, platform child,
or publication has been made. This continuation does NOT claim a universal
polynomial bound on recursive debt.

## Highest-value statements

- `HirschPortalDebt.active_portal_index_span`: two-sided incidence improves
  portal span from q+2 to q+1 for q-additive-near-geodesic region paths.
- `near_geodesic_carrier_mass`: the #206 pointwise geometric saving implies
  `sum(delta)+r*s <= r*e+(q+3)*s`, including the 4e full-availability q=1 case.
- `fresh_chain_cost` and `signature_mass_eq_endpoint_plus_neutral`: the exact
  finite-set identity behind simple-polytope `sum child dimensions = h+nu`.
- `EdgeTree.length_eq_entries_add_debt`: actual certified edge leaves telescope
  to `length=endpoint entries+total geometric triangle-gap debt`.

Compile the three new modules locally, then inspect their 13 axiom printouts:

```sh
lake build Solutions.PolynomialNearGeodesicWindows \
  Solutions.PolynomialPortalSignatureMass \
  Solutions.PolynomialRecursivePortalDebt
```

No Lean/Lake executable is installed in the originating container. These are
uncompiled proof candidates. Likely elaboration-sensitive points: Walk.take/drop
endpoint types and lengths, Nat.card_Icc simplification, and the indexed
EdgeTree.splice pattern/recursor. Do not weaken metric-slack, simplicity,
full-facet coverage, or edge-leaf hypotheses to make an adapter compile.

The geometry-to-signature bridge and the full near-geodesic deferred clipping
wrapper are NOT complete new Lean declarations. The former should derive active
cardinalities and kernel dimensions from actual simple-vertex tight bases. The
latter should preserve old APIs and add a separate relaxed path certificate,
rather than overwrite `DeferredClipCertificate.shortest` with a weaker claim.
The pointwise carrier excess inequality is unchanged by path selection.

## Reproducible checks

```sh
python3 scripts/test_portal_debt.py
python3 scripts/audit_portal_debt.py
python3 scripts/test_portal_family.py
```

All Python is standard-library only and exact rational/integer arithmetic.
The first script generates the comparative examples and exploration receipt.
The second checks all small graph/finite-set identities, the exact ten-facet
barrier and Dantzig example, and sixteen rejection controls. The third generates
and checks the family for k=0,1,2,4,8,12,20. The two tracked input fixtures contain
all data needed for regeneration. Generated complete certificates and full
geometry are included in the conversation ZIP, not all in the PR.

The full Model validator checks a strict point, positive normal balance, all
candidate vertex bases, simplicity, and genuine facets. It is exponential.
The router does not use ambient graph distances; test-only BFS supplies the
independent comparison. The strict-geodesic barrier lower bound uses shortest
paths INSIDE both polygons, independently of recursive optimization.

## What the results mean

The family has dimension 3, m=10+2k facets, and 16+4k vertices. Its true distance
between the specified vertices is five. Every shortest-facet-path repair of
that pair costs 6+2k even with perfect child paths, whereas allowing one extra
region edge gives five. At k=20 this is 46 versus five. This is unbounded
relative overhead, NOT superpolynomial diameter, NOT a lower bound for every
possible mixed basis-star certificate, and NOT an equivalence with the
monotone-conservative paths studied in arXiv:1510.07678.

Repeated original-row charges occur across descendants; root dimension debt
alone misses them. A 6D, 12-facet, 84-vertex Dantzig example has root debt zero
but lexicographic descendant debt one (seven edges instead of six).

The paper proof covers the infinite truncation family and the complete simple
polytope interpretation. JSON checks are not Lean proof terms, and no public
server verdict is claimed. After the new core is locally green and audited,
a single existing hosted final gate can preserve its receipt. Publication needs
its own honest exact interface and authenticated acceptance.
