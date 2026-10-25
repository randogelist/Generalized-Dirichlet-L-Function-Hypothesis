# Native Windows Lean 4.33 build

Current repository verification: `NATIVE_COMPILATION=NOT_RUN` and
`NATIVE_AXIOM_AUDIT=NOT_RUN`. The recovered source files and historical status
notices do not establish a native pass for this assembly. This runner has been
adapted and statically reviewed; it has not been executed on Windows.

From native Windows CMD, use an installed Lean 4.33.0 and an existing compatible
Mathlib checkout with its compiled dependency cache:

```bat
set "GRH_MATHLIB_ROOT=C:\path\to\mathlib4"
run.cmd
```

`run.cmd full` is equivalent. The single plan is `build-modules.txt`: 25 recovered
modules in dependency order, then `RHToGRHFirstFactorFrontier`,
`GRHFinal/FirstFactorAudit`, and `GRHFinal/Audit` (28 modules total).
The two audit entry points prepare 136 distinct axiom reports and expose the
actual theorem types. The first-factor module and its audit are source additions,
not imported native pass receipts. There is no separate
finite-witness search in this assembly.

The runner does not invoke Lake, Python, PowerShell, WSL, an installer, or a
download command. No Lake setup is needed. It interprets
`scripts/cache/Build.lean` directly with the installed Lean executable and uses
Windows `certutil.exe` for SHA-256.

## Existing compiler and cache selection

The default executable is
`%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe`.
Set `GRH_LEAN_EXE` to select another installed executable. Existing
`RH_LEAN_EXE`, then `LEAN_EXE`, are accepted as fallback overrides. The driver
checks that the compiler reports Lean 4.33.0 for native Windows before building.

`GRH_MATHLIB_ROOT` has priority. An invalid explicit value fails instead of
falling back. Without it, the driver checks these existing environment values
in order: `RH_MATHLIB_ROOT`, `MATHLIB_PROJECT_ROOT_OVERRIDE`,
`MATHLIB_CACHE_ROOT`, `GOODWORKFLOWFRONTIER_CACHE_BASE`, and `CACHE_BASE`.
It then considers these fixed locations:

- `%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1`
- `%USERPROFILE%\Downloads\awpi_phi_rh_lean_sieved_v0_1_1`
- `%USERPROFILE%\mathlib4`
- `%USERPROFILE%\Downloads\mathlib4`

Each candidate is checked directly and at its `.lake\packages\mathlib` child.
Admission requires `lean-toolchain` containing exactly
`leanprover/lean4:v4.33.0` and cached
`.lake\build\lib\lean\Mathlib.olean`. Discovery is bounded; it does not search
the whole disk. If no candidate qualifies, set `GRH_MATHLIB_ROOT` explicitly.

Mathlib objects are read from `.lake\build\lib\lean`. Dependency objects are
read from its `.lake\packages` children, or sibling package directories when
Mathlib is itself inside another project's `.lake\packages` directory.
An existing downstream project can therefore supply its actual Mathlib path,
for example `C:\project\.lake\packages\mathlib`.

## PASS-ONCE and LEAN_ANCHORINGS

Successful local receipts are stored under `.grh-cache\full\receipts`.
The source, resolved imports, project dependency receipts, output objects and
companions, audit log, compiler, cached external binaries, flags, import path,
environment, and runner must match their recorded fingerprints before reuse.
Objects without matching receipts are rebuilt. Historical status documents and
receipts from other repositories do not confer admission here.

The unchanged fingerprint algorithm hashes toolchain binaries and external
dependency trees both before and after a run. It writes a deterministically
framed temporary binary stream and hashes it with one `certutil` invocation
per tree. Temporary disk space can reach the size of the largest cache tree;
memory is bounded by the largest single cache file. This can take time for a
large Mathlib cache, but does not recompile those libraries. External cache
changes conservatively invalidate project receipts; project source changes
propagate through dependency receipt fingerprints.

An exclusive `.grh-cache\writer-lock` directory protects this repository's
outputs. Objects are staged before publication, the old receipt is removed
before replacement, and the new receipt is written last. An interrupted build
cannot admit a partially replaced object. If interrupted, ensure no runner is
active before manually removing the stale lock. Do not change sources,
toolchain files, or shared caches while a run is active; the local lock cannot
protect a shared Mathlib checkout from other applications.

## What a pass certifies

Modules compile with `-j 1 -DwarningAsError=true`. The axiom parser permits only
`propext`, `Classical.choice`, and `Quot.sound`. Missing reports in an `Audit`
module, malformed reports, `sorryAx`, compiler-trust axioms, and any other
reported axiom fail the build. The audit applies to the declarations printed
by `GRHFinal/Audit.lean` and `GRHFinal/FirstFactorAudit.lean`; it does not validate
every historical prose claim.

`build-modules.txt` uses forward-slash module paths without `.lean`, one per
line, in dependency order. Blank lines and lines beginning with `#` are ignored.
Module names may contain letters, digits, underscores, and `/`. Duplicates,
missing modules, unresolved imports, and imports from later or unlisted local
modules fail the build. At least one listed module must end in `Audit` and
produce an actual `#print axioms` report.

The run summary and `.grh-cache\full\last-run.txt` distinguish compilation
from the mathematical frontier. Even after a successful build they retain
`RH_TO_GRH_LIFT=OPEN`, `GRH_PROVED=NO`, and `RH_PROVED=NO`. Compilation certifies
the exact conditional statements and their displayed hypotheses; it does not
supply the missing character-wise analytic input or an unconditional RH-to-GRH
implication.
