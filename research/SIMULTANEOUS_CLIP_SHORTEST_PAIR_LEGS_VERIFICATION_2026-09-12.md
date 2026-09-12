# Shortest mixed clipping path integration

The exact `Solutions/PolynomialSimultaneousClipShortestPairLegs.lean` blob from PR #194 is retained, without its one-shot workflow.

- Frozen head `22c684e6ecb9b00863eb1f861a3d3510ff4c31f6`.
- Source SHA-256 `e50720b327e4beba6e024003778d4d55f81b7640b8d103849a101e84589f4b27`.
- Hosted run [34699884798](https://github.com/jjoshua2/prove2me-work/actions/runs/34699884798), job `103569645833`: success.
- Artifact `10300196464`; digest `sha256:6f0eea602ee558d1f669534f737ac30d0ff2144416afbcb659cfcf8ec59b17bf`.
- Local integration check: `lake build Solutions.PolynomialSimultaneousClipShortestPairLegs Solutions.PolynomialChordlessCarrierExcessTradeoff Solutions.PolynomialMinCarrierExcessRouting` passed on Lean 4.30.0 / Mathlib c5ea003.

Source equality with the frozen head was checked byte for byte. The hosted axiom log and local targeted build log are stored under [verification/2026-09-12-sync](verification/2026-09-12-sync/).

The theorem retains the shortest mixed repair path and the exact charged cut legs. Its `hFaces` premise still asks for routes for every pair on every cut face before returning that path. Hence support-dependent bounds cannot simply be substituted into this premise. The new deferred-cost theorem addresses the generic choice/assembly interface; threading it through clipping remains necessary.
