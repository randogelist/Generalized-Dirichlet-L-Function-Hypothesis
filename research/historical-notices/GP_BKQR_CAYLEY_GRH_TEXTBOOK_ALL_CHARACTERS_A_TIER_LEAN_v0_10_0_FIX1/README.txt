GP_BKQR_CAYLEY_GRH_TEXTBOOK_ALL_CHARACTERS_A_TIER_LEAN_v0_10_0

Goal:
Expose the literal textbook Dirichlet-GRH statement over ALL Dirichlet characters,
not only primitive characters, and prove it equivalent to the already-verified
primitive-character GeneralizedRiemannHypothesis.

Mathematical bridge:
For arbitrary chi mod N, Mathlib's primitiveCharacter has conductor M|N and
changeLevel primitiveCharacter = chi.  LFunction_changeLevel writes
  L(s,chi) = L(s,chi*) * finite Euler product.
For Re(s)>0 every added factor 1 - chi*(p) p^(-s) is nonzero because
|chi*(p)| <= 1 and |p^(-s)| < 1.  Therefore every zero in the open critical
strip already comes from the primitive L-function.

A-tier target:
TEXTBOOK_ALL_CHARACTERS_GRH_A_TIER_ATLAS is closed: no theorem hypotheses,
no research/project axioms, no external research-parameter input.

Build note:
This is intentionally a thin extension of the already-passing v0.9.0 FIX1
project cache.  It requires that prior package's build cache, which the user
just produced.  This is a build dependency, not a mathematical theorem input.
