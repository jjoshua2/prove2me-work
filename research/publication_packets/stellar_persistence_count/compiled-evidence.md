# Corrected proof compiled and axiom-audited

Run35154778307 verifies exact proof head97d58b7d247c4661e437058e2ca2be34c15e63d5.
Driver, solution and statement all compile with exit0 under Lean4.30.0 and
Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f. Every one of the five audited
declarations depends only on propext, Classical.choice and Quot.sound. The
actual raw audit, driver output and verified manifest are preserved here.
The target statement file contains the expected target placeholder; it is not
imported by solution.lean. The actual proof has no admission or sorryAx.

The first run35154274683 found one redundant successor rewrite in the vertex-
count induction. The correction removed that rewrite ONLY. All theorem types,
hypotheses, problem.json and explanation.md are unchanged. See the preserved
first-gate diagnostic; the failed run did not register or submit a platform theorem.
This is not a claim that the initial candidate passed unchanged on its first gate.

The corrected verified ZIP artifact10470098719 was downloaded independently.
Its recomputed SHA256 is71e0569fdb94d0f174e1bc5c37be5dc24902042e406272a9892891367629d4af.
All five frozen file hashes match the raw manifest. The original solution,
problem and explanation are byte-identical to the prepared corrected packet.
The resolved corrected request artifact10470428234 has independently checked
ZIP hashbdd2eb33d8c7ac5bcf3f6668d5928864dfe7c2cb6044163d04e76cb7848b1387.
The first request artifact10470900478 has hash
2caed9c360601fd2221a4671b1a6d77a51649bb1af1523bd492583d99bfc5f45.
Both resolved requests preserve their actual, different proof heads.

The finite semantics/signature suite reran in an independent directory with
only the standalone test and three input files; its full result is byte-identical
(SHA256 c075f39858bbc77b75169f9708491e82baf3e462ccec8323b00eb85d4d976101).
Those tests are supporting evidence, not what established Lean compilation.
There is no local Lean executable; the compiler evidence is specifically the
pinned GitHub gate. No workflow, pin, permission, token or secret-split changes.

The publication job is separate. Read the later authenticated receipt before
claiming ACCEPTED/Proved or attempting any resume. This intermediate note alone
claims successful compilation/audit, not a platform verdict. No proof bytes
were modified after the corrected gate.
