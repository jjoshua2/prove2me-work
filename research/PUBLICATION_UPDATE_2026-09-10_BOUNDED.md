# Bounded simultaneous-clipping publication receipt — 2026-09-10

## Prove2Me theorem

- theorem: `Hirsch.simultaneous_clipping_diameter_of_compact_outer`
- theorem ID: `75d26f37-e0bd-4d73-9128-688fe7d5a80c`
- submission ID: `2c038ea7-ebc9-4f22-80c6-328fab2ea613`
- verdict: **ACCEPTED**
- live status: **Proved**
- platform observed: Prove2Me **0.9.9**

## Verified proof provenance

- source branch: PR #53 / `chatgpt/verify-simultaneous-clipping`
- source commit: `446304d56513437aad9c0a02fc1d202e41783259`
- source/standalone verification run: `34485975796`
- verified artifact: `10155724751`
- artifact digest: `sha256:ff0ff54c263efd482cded2e7edba27324276094a143264adae49731ed6bbdcfe`
- standalone `solution.lean` SHA-256: `fe83809fcda2cc6b2714193964e8f8be6ad2a1705ac4e3383b8dc6621736564f`
- publication run: `34487272212`
- publication receipt artifact: `10156328306`
- receipt artifact digest: `sha256:31e5627831c92711e2850d92b534aed89b4db4d330bd974080ac29f42215458b`

Run `34485975796` compiled the complete source chain and public adapter, generated the standalone proof from the exact dependency closure, independently compiled it, and axiom-audited `solution`. The standalone log reports only `propext`, `Classical.choice`, and `Quot.sound`.

The first one-shot publication run intentionally stopped before registering anything because `/agent/refresh` reported platform `0.9.9` while the publisher was pinned to `0.9.8`. The official upstream `prove2me_workspace/SKILL.md` was then checked and confirmed version `0.9.9`; the publisher retained a strict version check and the second run completed successfully.

## Formal scope

Let `Q` be compact and convex. Simultaneously impose finitely many halfspace cuts. If `Q` has padded graph diameter at most `D` and every exposed face associated with an added inequality in the **final clipped set** has intrinsic padded graph diameter at most `B_i`, then the final clipped set has padded graph diameter at most

`D + sum_i B_i`.

The endpoints may be new final vertices. There is no separate strict-centre hypothesis in the public theorem. This does **not** prove Polynomial Hirsch: the final-face budgets are assumptions, and the theorem does not assert that an arbitrary circuit/projective evolution has the required simultaneous-clipping representation.
