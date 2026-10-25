# Generalized Dirichlet L-function Hypothesis

Recovered Lean 4.33 sources for the GP/BKQR/Cayley Dirichlet-GRH equivalences
and the SOLOBOLO project's ordinary-RH-to-GRH transfer frontier.

The requested RH/GRH equivalence is present as an **explicitly conditional
theorem** in [RHToGRHCayleyLiftFrontier.lean](RHToGRHCayleyLiftFrontier.lean):

```lean
RHToGRHFrontier.RiemannToGeneralizedCayleyLift →
  (_root_.RiemannHypothesis ↔
    CayleyGRHStrong.TextbookGeneralizedRiemannHypothesis)
```

Its name is `RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT`. The corresponding
primitive-character theorem is `RH_IFF_GRH_OF_GENERALIZED_CAYLEY_LIFT`.
The lift is the remaining input: the source identifies it with `RH → GRH`
but does not prove it. This repository therefore does **not** establish an
unconditional `RH ↔ GRH`.

The new [first-factor reduction](RHToGRHFirstFactorFrontier.lean) isolates the
same open implication as one universal family: **assuming ordinary RH, the
first completed Dirichlet L-factor is nonzero for every primitive character
and every critical square/slit point**. Its two source theorems reduce this
family to the existing four-factor frontier and hence to `RH → GRH`. The other
three factors follow by inverse-character closure and the primitive functional
equation. The universal first-factor condition itself is **not discharged**;
it is not a finite test or an accepted witness. Native checks remain `NOT_RUN`.

## What the source contains

| Result | Source |
|---|---|
| Primitive Dirichlet GRH iff Cayley zero loss, saturation or unit-state energy preservation | [CayleyGRHClosure.lean](CayleyGRHClosure.lean) |
| Primitive Dirichlet GRH implies Mathlib RH; modulus-one Dirichlet RH iff Mathlib RH | [CayleyGRHClosure.lean](CayleyGRHClosure.lean) |
| Actual completed-pair zero-freeness on the critical square/slit domain, logarithmic-derivative totality and Cayley totality iff primitive GRH | [CompletedPairCayleyCoverage.lean](CompletedPairCayleyCoverage.lean) |
| All-character Dirichlet GRH iff primitive-character GRH, via nonvanishing finite Euler factors | [TextbookDirichletGRH.lean](TextbookDirichletGRH.lean) |
| Conditional ordinary `RH ↔ GRH`, given the generalized Cayley lift | [RHToGRHCayleyLiftFrontier.lean](RHToGRHCayleyLiftFrontier.lean) |
| Conditional `RH ↔ GRH`, given cross-Cayley transfer | [RHToGRHCrossCayleyDisassembly.lean](RHToGRHCrossCayleyDisassembly.lean) |
| Four completed-L nonvanishing conditions, under RH, iff the missing implication `RH → GRH` | [RHToGRHCompletedLFactorFrontier.lean](RHToGRHCompletedLFactorFrontier.lean) |
| One universal first completed-L factor condition iff the four-factor condition and thus `RH → GRH` | [RHToGRHFirstFactorFrontier.lean](RHToGRHFirstFactorFrontier.lean) |

The GRH definitions use Mathlib's actual `DirichletCharacter.LFunction` and
zeros in the open strip `0 < Re(s) < 1`. The textbook version quantifies over
every positive modulus and every Dirichlet character; the primitive version
adds `χ.IsPrimitive`. Ordinary RH is `_root_.RiemannHypothesis`.

The universal Cayley algebra applies to each zero predicate separately.
Having that common algebra for zeta and Dirichlet L-functions does not provide
the transfer from the zeta zero set to every character's zero set.

## Source and build status

**Version: `v0_1_0_construction`. Native build and kernel axiom audit: `NOT_RUN`.**

All 25 recovered mathematical modules are preserved byte-for-byte, with their
local import closure included. [Source provenance](provenance/source-files.json)
records the original archive members and hashes. The new first-factor module
and its focused audit have [separate provenance](provenance/new-source-files.json).
Historical filenames and
theorem names containing `A_TIER` are retained as identifiers; they are not a
new verification claim. [Historical evidence](provenance/historical-evidence.json)
separates old source notices from compiler receipts; no native receipt file was
recovered for admission into this assembled repository.

The [audit entry point](GRHFinal/Audit.lean) requests exact signatures and axiom
reports for the endpoints and imports the
[focused first-factor audit](GRHFinal/FirstFactorAudit.lean). The 28-module build
prepares 136 distinct axiom reports. The new assembly still needs the user's native
Windows run. It makes no RH proof, GRH proof or finite accepted witness claim.

Use the installed Windows Lean 4.33.0 and compatible cached Mathlib:

```bat
set "GRH_MATHLIB_ROOT=C:\path\to\mathlib4"
run.cmd
```

See [build instructions](docs/BUILD.md), the [open transfer obligation](docs/FRONTIER.md),
and the [theorem audit](provenance/theorem-audit.json). The runner preserves
`YOU_ARE_GOODWORKFLOWFRONTIER`, PASS-ONCE and `LEAN_ANCHORINGS` fingerprint rules.
The companion RH repository is
[Riemann-Hypothesis-Final](https://github.com/randogelist/Riemann-Hypothesis-Final).
