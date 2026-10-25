GP_BKQR_CAYLEY_RH_A_TIER_CLOSURE_LEAN_v0_4_2_FIX2

Purpose
-------
Merge the premise-free constructed Cayley geometry and standard jet-loss
nonnegativity anchor with the actual completed-GolPhi/zeta zero equivalence.

Frozen closure theorem
----------------------
  CayleyRHAClosure.GOLPHI_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH

It states:
  every nontrivial completed-GolPhi zero has zero constructed Cayley loss
  if and only if Mathlib's native RiemannHypothesis holds.

Parallel exact formulations are exported through literal nontrivial zeta
zeros, Cayley contraction saturation, and unit-state energy preservation.

Scope
-----
This package proves an unconditional equivalence/closure criterion. It does
NOT prove the zero-loss proposition unconditionally and therefore does not
claim an unconditional proof of RH.

The literal K2/K4 multiplicity-jet realization of the standard jet loss is
not assumed and is not claimed here. GPBKQRKernel.jetCayleyLoss_nonneg remains
an independent premise-free algebraic anchor.

Run
---
cd /d "%USERPROFILE%\Downloads" && (if exist "GP_BKQR_CAYLEY_RH_A_TIER_CLOSURE_LEAN_v0_4_2_FIX2" rmdir /s /q "GP_BKQR_CAYLEY_RH_A_TIER_CLOSURE_LEAN_v0_4_2_FIX2") && tar -xf "GP_BKQR_CAYLEY_RH_A_TIER_CLOSURE_LEAN_v0_4_2_FIX2.zip" && call "GP_BKQR_CAYLEY_RH_A_TIER_CLOSURE_LEAN_v0_4_2_FIX2\run.cmd"
