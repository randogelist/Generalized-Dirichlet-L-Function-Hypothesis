# HVR cyclotomic extension

This directory records the additive HVR refinement of the repository's existing
ordinary-RH to Dirichlet-GRH frontier.

The legacy theorem

```lean
RHToGRHFrontier.RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT
```

is unchanged. The HVR extension supplies a new sufficient route into its premise:

```lean
HVRGeneralizedCayleyLiftBridge.
  HVR_RELATIVE_PROPAGATION_IMPLIES_GENERALIZED_CAYLEY_LIFT
```

The new chain is

[
RH
	o
operatorname{Subexp}(D_1)
	o
orall q>0,operatorname{Subexp}(D_q)
	o
orall q>0,operatorname{Subexp}(P_q)
	o
	ext{Generalized Cayley lift}
	o
RHleftrightarrow GRH.
]

The algebraic conductor step is formalized by

```lean
HVRCyclotomicPacketTower.HVR_CYCLOTOMIC_COMPLETED_PACKET_TOWER
```

and uses Mathlib Möbius inversion to recover exact-conductor primitive packets
from the completed cyclotomic packet family.

The B-tier and Lean red arrows are synchronized by

```lean
HVRRHGRHChainSync.RELATIVE_PROPAGATION_IFF_GLOBAL_PROPAGATION
```

which proves that, once the conductor-one packet is HVR-subexponential,

[
orall q>0,operatorname{Subexp}(D_q-D_1)
]

is equivalent to

[
orall q>0,operatorname{Subexp}(D_q).
]

## Remaining substantive frontier

The remaining new mathematical input is:

[
operatorname{Subexp}(D_1)
Longrightarrow
orall q>0,operatorname{Subexp}(D_q-D_1).
]

The repository still does **not** establish this premise and therefore does not
establish unconditional `RH → GRH`.

The joint root is

```lean
GeneralizedDirichletHVRJoint.JOINT_HVR_GENERALIZED_DIRICHLET_MAIN
```

and the native Windows Lean 4.33.0 integration run passed with standard axioms
only. See `provenance/hvr-native-evidence/README.md`.
