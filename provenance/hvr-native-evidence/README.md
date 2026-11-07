# HVR native verification evidence

The HVR extension was prepared outside this repository and then integrated additively.
The following theorem sources were compiled by the user with native Windows Lean 4.33.0
and theorem-level axiom audit output containing only:

- `propext`
- `Classical.choice`
- `Quot.sound`

No `sorryAx` or unapproved axioms were present in the successful receipts.

## Verified sources

| Module | Source SHA256 | Native status |
|---|---|---|
| `HVR_CYCLOTOMIC_COMPLETED_PACKET_TOWER.lean` | `7f2a5482fbed419761d4bae2470319b731a2629f497521c594a6004bf8922d61` | PASS, standard-only |
| `RH_TO_GRH_D_CHAIN.lean` | `11852279e0feb5984454a2e5d1dd2bfea629b1f088c51f245b10113790e90e2d` | PASS, standard-only |
| `HVR_RH_GRH_CHAIN_SYNC.lean` | `ada3c2b91acf48c7ef41d86855b387c9beaaaf1756e0dd4e3b120defe2a27d40` | PASS, standard-only |
| `HVR_GENERALIZED_CAYLEY_LIFT_BRIDGE.lean` | `5b506e037b70d267f8ce8ba421fa55723f6cb13ca138b88e80f7607a044cfa00` | PASS inside joint package, standard-only |
| `JOINT_MAIN.lean` | `865da095887db5e2a9fbad1a914981b8c3d2c6451f8929b7ac9c7d28c369316d` | PASS inside joint package, standard-only |

## Joint native receipt

The combined local integration run reported:

```text
COMPILE_PASS=ALL_JOINT_MODULES
UPSTREAM_LEGACY_THEOREMS_VISIBLE=PASS
HVR_THEOREMS_VISIBLE=PASS
GENERALIZED_CAYLEY_LIFT_BRIDGE=LEAN_DERIVED
HVR_RELATIVE_PROPAGATION_SUPPLIES_REPOSITORY_MAIN_PREMISE=LEAN_DERIVED
REPOSITORY_MAIN_EQUIVALENCE_REUSED_UNCHANGED=PASS
EXACT_TYPE_CHECK=PASS|GeneralizedDirichletHVRJoint.JOINT_HVR_GENERALIZED_DIRICHLET_MAIN
THEOREM_AXIOM_AUDIT=PASS_STANDARD_ONLY
JOINT_PACKAGE=PASS
REMAINING_SUBSTANTIVE_FRONTIER=RELATIVE_COMPLETED_PACKET_PROPAGATION
UNCONDITIONAL_RH_IMPLIES_GRH=NOT_ESTABLISHED
RUN=PASS
```

This evidence certifies the conditional theorem graph. It does not establish
the remaining relative completed-packet propagation premise and therefore does
not establish unconditional `RH → GRH`.
