GP_BKQR_CAYLEY_GRH_COMPLETED_PAIR_A_TIER_LEAN_v0_6_0_FIX1
====================================================

Purpose
-------
This package extends the passing v0_5_2 GRH A-tier closure from a generic
critical-line Cayley detector to an actual completed-Dirichlet analytic layer.
It retains the v0_5_2 source verbatim and adds four modules:

  CompletedDirichletBridge.lean
  PrimitiveCompletedPair.lean
  CompletedPairCayleyAnalytic.lean
  StrongGRHClosure.lean

New mathematical content
------------------------
1. Uses Mathlib's actual DirichletCharacter.completedLFunction.
2. Proves the gamma factor is nonzero for Re(s)>0.
3. Proves L(s,chi)=0 iff completedLFunction(chi,s)=0 in the critical strip.
4. Re-exports Mathlib's genuine primitive functional equation.
5. Proves inverse characters preserve primitivity.
6. Proves exact completed-zero reflection chi <-> chi^-1 under s -> 1-s.
7. Constructs the actual completed inverse-pair
       P_chi(s) = Lambda_chi(s) Lambda_{chi^-1}(s).
8. Derives an object-level functional equation for P_chi.
9. Proves the zero set of P_chi is reflection invariant.
10. Constructs the literal reflection symmetrization
       S_chi(s) = P_chi(s) P_chi(1-s),
    and proves it introduces no new zeros for primitive chi.
11. Centers S_chi at 1/2 and proves literal evenness.
12. Proves the centered-even family RH statement is exactly GRH.
13. For nontrivial chi, proves the pair, symmetrized pair, and centered pair
    are entire; constructs a slit-plane theta through Complex.sqrt.
14. Constructs a genuine logarithmic-derivative Cayley observable from that
    theta and proves `none` occurs exactly at sampled completed-pair zeros.
15. Rebinds the existing zero-loss / saturation / unit-energy formulations to
    zeros of the actual completed pair, giving exact GRH equivalences.

Status
------
This ZIP is a SOURCE CANDIDATE for native Windows Lean 4.33.0 validation.
It was assembled and statically audited here, but it has NOT been kernel-
compiled in this environment. Run run.cmd with the user's native compiler.
Do not call it PASS until the runner ends with PROJECT_BUILD=PASS and RUN=PASS.

No unconditional GRH proof is claimed. The open frontier is now sharper:
derive a critical-line forcing / zero-loss theorem from the actual completed-
pair analytic Cayley observable itself, rather than imposing the previously
constructed geometric real-part detector on its zero set.

Runner policy
-------------
Native Windows Lean 4.33.0 only.
No network. No Python. No PowerShell. No Lake. No WSL.
Persistent .olean cache under %USERPROFILE%\LeanRuns.
If the previous v0_5_2 extracted package/build is available in Downloads, the
runner hydrates matching inherited .olean files; otherwise it compiles them.
