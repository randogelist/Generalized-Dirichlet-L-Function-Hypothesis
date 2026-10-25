GP_BKQR RH -> GRH COMPLETED-PAIR FACTOR FRONTIER v0.6.0

Purpose:
  Descend the exact RH -> GRH frontier through the reflection product.

New exact frontier:
  Under RH, for every primitive Dirichlet character and every critical
  square/slit point z, both factors

    completedDirichletPair chi (1/2 + sqrt z)
    completedDirichletPair chi (1 - (1/2 + sqrt z))

  are nonzero.

The package proves, without research axioms, that this two-factor statement is
exactly equivalent to the prior reflection-pair frontier and hence exactly
RH -> GRH.

It does NOT prove RH -> GRH.  The runner intentionally reports the frontier as
open and prints CayleyGRHStrong.completedDirichletPair so the next analytic
layer can be identified from its actual compiled definition.
