# Handoff to a network-enabled Prove2Me coding agent

Continue the user's request to contribute to **The Polynomial Hirsch Conjecture** mission. Read `CONTRIBUTION.md` and independently audit the mathematical argument before publishing anything. Nothing in this package has been submitted or checked by Lean.

Fetch `https://prove2.me/start.md` and follow its current instructions. Use a Prove2Me agent credential supplied securely in your session; this package intentionally contains none. Send the credential only to the documented Prove2Me API. Check for an existing workspace before installing anything.

Retrieve the mission, milestones and their histories, the root's current frontier and existing decompositions, relevant discussions, and the exact definition modules/environment. Do not assume the public frontier observed on September 4 is still current. Search for reusable wedge, padding, and walk-transfer lemmas before creating duplicates.

The proposed root reduction is:

    balanced_hpoly_transfer + balanced_polynomial_bound + DiamLE monotonicity
      -> Hirsch.polynomial_hirsch_conjecture

The first child has a complete mathematical proof in the contribution document and should be formalized. The second is an explicit remaining conjecture, equivalent to the full question after balancing; it is NOT a solved lemma or a new bound. Describe the contribution as formalization infrastructure for a classical wedge/d-step reduction, not as a breakthrough on the conjecture.

`HirschReductionDraft.lean` uses local/generic definitions and explicit hypotheses. It is not an exact-type solution for the mission. It supplies candidate reusable walk-transfer and arithmetic proofs but must be compiled and adapted, not uploaded unchanged.

Follow the current platform policy for posting an open conjectural child. If the platform will not accept such a child, do not disguise it as an established theorem. A complete proof of the structural wedge/transfer lemma is still a useful candidate contribution, subject to the mission's linkage rules.

Before any verification request, compile against the pinned environment. A root sketch must use the exact target type, have a top-level theorem named `solution`, import other published platform children rather than its own target, and have no unproved gaps in the submitted file. Do not introduce fake axioms or change the target definitions. Poll and report the actual server status; never describe a draft as accepted.

The exact-rational checks in `sanity_checks.json` are 52 single-wedge checks and 13 balanced-system checks. They are not a substitute for formal verification.
