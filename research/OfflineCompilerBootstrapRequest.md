# One-time offline compiler bootstrap

The current ChatGPT working container has no Lean/Lake installation and cannot
resolve GitHub or Lean release domains. The connected GitHub artifact download
action is available. Exporting the existing public pinned compiler/dependency
cache once enables subsequent proof edits to compile LOCALLY, rather than using
GitHub Actions as a repeated proof compiler.

This temporary infrastructure PR executes no candidate proof, no Prove2Me call,
and no publication script. Its only expensive operation is restoring and
archiving the existing cache. The export is restricted to the Lean 4.30.0
compiler distribution, `.lake/packages` without Git directories or IR products,
and `git archive` of the public tracked source. It never archives HOME, secrets,
credentials, environment variables, or Git authentication configuration.

The trigger is limited to opening this exact same-repository bootstrap request,
or manual dispatch; it does not run on synchronization or push. Source and
workflow policy checks were executed in the local container before this write.
The artifact has one-day retention. This PR and the temporary export workflow
will be closed/excluded from main after transfer succeeds or fails. No compiler
or platform verdict is claimed by this infrastructure action.
