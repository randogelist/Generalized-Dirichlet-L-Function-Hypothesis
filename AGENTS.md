# Generalized Dirichlet L-function Hypothesis

This repository preserves the actual Dirichlet-GRH Cayley equivalences and
the conditional ordinary-RH-to-GRH transfer frontier. Read `README.md`,
`docs/FRONTIER.md`, `docs/BUILD.md`, `docs/YOU_ARE_GOODWORKFLOWFRONTIER_v1_0_15.txt`
and the theorem audit before changing proofs.

- Keep the native targets and all primitive/all-character quantifiers explicit.
- The existing RH iff GRH theorems assume a generalized lift or cross-Cayley
  transfer. Do not drop those premises or report them as proved inputs.
- Preserve the 25 original mathematical source files and their hash provenance.
  Record any deliberate later mathematical changes separately.
- Lean 4.33.0, compatible cached Mathlib, one native Windows `run.cmd`.
  The user performs native compilation; source inspection is not a compiled pass.
- Preserve `YOU_ARE_GOODWORKFLOWFRONTIER`, PASS-ONCE and `LEAN_ANCHORINGS`.
  Reuse requires verified source, dependency, environment and binary fingerprints.
- No proof placeholders, new axioms, unsafe proof shortcuts or `native_decide`.
- Print exact endpoint signatures and audit their transitive axioms. Axiom-clean
  conditional proofs retain their mathematical premises.
- Keep historical source notices separate from admitted native build receipts.
- A universal L-function condition, an infinite family or a proof-bearing
  structure is not finite raw data accepted by a terminating checker.
- Use the workflow modes `B_TIER_DERIVATION`, `A_TIER_PLANNING` and
  `A_TIER_EXECUTION` without treating a mode or package name as a proof tier.
