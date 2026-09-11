# Slack normal-relation diameter certificate — publication receipt

Authenticated recovery checked at **2026-09-11T16:08:22.162237+00:00**.

## Public result

- Theorem: `Hirsch.hpoly_and_row_faces_diamLE_two_of_normal_relations`.
- Theorem ID: `96cb14a4-aa1b-4d14-93d9-b959e08aa662`.
- Original submission ID: `5e888ccf-0f16-48a1-8992-50d3debf1258`.
- Registration job: `ff7ccb7d-1a85-4d01-86ea-f532ca61ac73`.
- Registration **PUBLISHED** at `2026-09-11T15:56:46.995726+00:00`.
- Proof verdict **ACCEPTED**, updated `2026-09-11T16:05:03.535961+00:00`.
- Authenticated final theorem status **Proved**.
- Platform **0.10.1**, Lean **4.30.0**, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Independent standalone solution SHA-256: `248851588b10bad874626a17463e9c11b542ac3898146abdbb03530fceb57c27`.

Let P be an n-row H-polyhedron in ambient dimension d, with n=d+2 and a reference extreme vertex. Given strictly positive c_i, nonconstant t_i, and the finite normal identities

```
sum c_i a_i = 0,
sum t_i c_i a_i = 0,
sum c_i b_i = 1,
```

P and every face obtained by making any selected collection of the original rows tight have **intrinsic padded graph diameter at most two**.

The proof constructs exact slack-image equality by rank-nullity, including the reverse inclusion, and transports genuine extreme points and segment-face adjacency. No diameter bound or open conjecture is assumed. The theorem does NOT itself establish existence of these relation witnesses from boundedness alone.

## Source and standalone verification

- Frozen source commit: `4a9204edd7f03c7f9676f9dc9762be121e43bf1a`.
- `Solutions/PolynomialSlackMomentCertificate.lean`, blob `90005f87a9939477770c515ec19345ec93765f2b`.
- `Solutions/PolynomialSlackNormalRelations.lean`, blob `d46a7c7ba16d3eda1aae038e3046522af3b83ec0`.
- Original source gate run `34615241828`, job `103315400010`: both modules and all 14 required declarations passed.
- Independent standalone/publication run `34618047572`, job `103324780665`: full dependency build and standalone compilation succeeded; the audit checked all **51** printed reports and found only `propext`, `Classical.choice`, and `Quot.sound`.
- Original proof/partial receipt artifact `10272241257`, `slack-normal-relations-publication`, SHA-256 `862a5869f2c19b882023f6913866232e5e9dc6d831262ad9d07aa8e7803f6414`.

No local runtime success is claimed for this editing conversation. Compilation above was hosted; the independent platform verifier then accepted the exact frozen proof.

## Recovery, not resubmission

The original GitHub monitor was canceled at `2026-09-11T16:02:19Z`, after source/standalone verification and while the existing platform proof was still pending. This did not cancel the Prove2Me submission itself.

A separate lightweight recovery restored and digest-verified the original artifact, checked the proof against frozen Git sources and its existing axiom log, and queried the **same** submission. It found ACCEPTED/live Proved and added the missing mission-board linkage. It performed no new registration, proof submission, or Lean build.

- Recovery run `34620227081`, job `103332067271`, **success**.
- Recovery artifact `10272147736`, `slack-publication-recovered`.
- Recovery artifact SHA-256 `50ee28259636c32192d586fa5c7fae035c5359cc2dba737811b46c3095b05f20`.
- Mission ID `6078cb2d-3594-44b1-a01a-fd452ddae274`.
- Mission comment `02fb1808-74fc-468e-a0bd-5b7d6e216f86`, with resolved theorem and solution references.
- `duplicate_submission: false`; `graph_mutation: false`.

The d>=4 circuit-to-edge frontier `73beca40-31bc-42d5-8350-5ec9ac28bd3e` was authenticated **Open** before and after recovery. No conjectural child was created.

## Next mathematical distinction

This completes the explicit certificate-to-geometry direction. A separate direct small-excess induction is now being verified in PR95: n<=d+3 should imply diameter<=n-d using the already-Proved low-dimensional Hirsch and facet-reduction inputs. Its driver has passed Lean and axiom auditing, but this receipt does not establish its public acceptance. That route can obtain the low-excess diameter-only corollary without proving positive-weight existence. Explicit slack normalization remains useful for constructing coordinates and portals.
