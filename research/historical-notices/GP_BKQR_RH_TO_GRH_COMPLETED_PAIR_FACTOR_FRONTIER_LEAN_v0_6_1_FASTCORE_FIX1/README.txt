GP_BKQR RH -> GRH COMPLETED PAIR FACTOR FRONTIER v0.6.1 FASTCORE FIX1

Purpose
=======
Same theorem content as v0.6.0, but the runner no longer recompiles the
ordinary RH Cayley closure or the earlier RH->GRH frontier layers.

Required precompiled baselines
==============================
1. v0.5.0 reflection-pair frontier cache (already produced by the PASS run):
   %USERPROFILE%\LeanRuns\GP_BKQR_RH_TO_GRH_REFLECTION_PAIR_FRONTIER_433_FASTCACHE_R1\build
2. v0.9 Cayley GRH coverage cache.
3. v0.10 textbook all-characters GRH cache.
4. Existing Lean 4.33.0 + cached Mathlib tree.

FASTCORE behavior
=================
Only RHToGRHCompletedPairFactorFrontier.lean is compiled in this package.
Main.lean is then run for theorem/definition introspection and axiom audit.
The heavy ordinary RH Cayley source tree is reused from the v0.5 cache.

No mathematics changed relative to v0.6.0.
