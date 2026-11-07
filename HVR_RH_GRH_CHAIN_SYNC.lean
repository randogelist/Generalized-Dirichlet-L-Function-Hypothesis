import HVR_CYCLOTOMIC_COMPLETED_PACKET_TOWER
import RH_TO_GRH_D_CHAIN

set_option autoImplicit false

noncomputable section

namespace HVRRHGRHChainSync

open HVRCyclotomicPacketTower

/--
The exact B-tier red arrow written at the completed-packet level.

Starting from HVR Subexp of the conductor-one completed packet, every
relative completed packet against the base level is HVR Subexp.
-/
def RelativePropagationFromBase
    (cyclo : Nat → Packet) : Prop :=
  PacketSubexp (cyclo 1) →
    ∀ q : Nat, 0 < q →
      PacketSubexp (relativePacket cyclo q 1)

/--
Equivalent global form of the same red arrow.
-/
def GlobalPropagationFromBase
    (cyclo : Nat → Packet) : Prop :=
  PacketSubexp (cyclo 1) →
    ∀ q : Nat, 0 < q →
      PacketSubexp (cyclo q)

/--
The B-tier relative completed-packet frontier and the Lean global propagation
premise are exactly equivalent.
-/
theorem RELATIVE_PROPAGATION_IFF_GLOBAL_PROPAGATION
    (cyclo : Nat → Packet) :
    RelativePropagationFromBase cyclo ↔
      GlobalPropagationFromBase cyclo := by
  constructor
  · intro hrel hbase q hq
    have hrelative :
        PacketSubexp (relativePacket cyclo q 1) :=
      hrel hbase q hq
    exact
      (RELATIVE_PACKET_STEP_EQUIVALENCE
        cyclo hbase).mpr hrelative
  · intro hglobal hbase q hq
    have hqsub :
        PacketSubexp (cyclo q) :=
      hglobal hbase q hq
    exact
      (RELATIVE_PACKET_STEP_EQUIVALENCE
        cyclo hbase).mp hqsub

/--
Actual-endpoint RH -> GRH chain synchronized with the B-tier cyclotomic
completed-packet chain.

There are three explicit adapter premises:

* `hdecomp`: actual completed cyclotomic divisor factorization/readout;
* `hRHBase`: actual Mathlib RH gives HVR Subexp at conductor one;
* `hPrimitiveToGRH`: exact-conductor primitive packet Subexp gives the
  repository's actual primitive-character Dirichlet GRH endpoint.

The sole cross-character research premise is `hRelative`.
-/
theorem RH_TO_GRH_D_OF_RELATIVE_CYCLOTOMIC_PROPAGATION
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim)
    (hRHBase :
      _root_.RiemannHypothesis →
        PacketSubexp (cyclo 1))
    (hPrimitiveToGRH :
      (∀ q : Nat, 0 < q → PacketSubexp (prim q)) →
        CayleyGRHClosure.GeneralizedRiemannHypothesis)
    (hRelative :
      RelativePropagationFromBase cyclo) :
    RHToGRHDAssembly.RHToGRHDTarget := by
  intro hRH
  have hbase :
      PacketSubexp (cyclo 1) :=
    hRHBase hRH
  have hglobal :
      ∀ q : Nat, 0 < q →
        PacketSubexp (cyclo q) :=
    (RELATIVE_PROPAGATION_IFF_GLOBAL_PROPAGATION cyclo).mp
      hRelative hbase
  have hprim :
      ∀ q : Nat, 0 < q →
        PacketSubexp (prim q) :=
    (GLOBAL_CYCLOTOMIC_PRIMITIVE_HVR_EQUIVALENCE
      cyclo prim hdecomp).mp hglobal
  exact hPrimitiveToGRH hprim

/--
Literal root type without the project target abbreviation.
-/
theorem RIEMANN_HYPOTHESIS_IMPLIES_GENERALIZED_RIEMANN_HYPOTHESIS
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim)
    (hRHBase :
      _root_.RiemannHypothesis →
        PacketSubexp (cyclo 1))
    (hPrimitiveToGRH :
      (∀ q : Nat, 0 < q → PacketSubexp (prim q)) →
        CayleyGRHClosure.GeneralizedRiemannHypothesis)
    (hRelative :
      RelativePropagationFromBase cyclo) :
    _root_.RiemannHypothesis →
      CayleyGRHClosure.GeneralizedRiemannHypothesis :=
  RH_TO_GRH_D_OF_RELATIVE_CYCLOTOMIC_PROPAGATION
    cyclo prim hdecomp hRHBase hPrimitiveToGRH hRelative

/--
Synchronization atlas.

The first component states that the B-tier relative red arrow is literally
equivalent to the global propagation premise used by the A-tier tower.

The second component is the actual Mathlib-RH -> project-GRH implication
under that same relative red arrow and the explicit structural adapters.
-/
theorem HVR_RH_GRH_B_TIER_LEAN_SYNCHRONIZATION
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim)
    (hRHBase :
      _root_.RiemannHypothesis →
        PacketSubexp (cyclo 1))
    (hPrimitiveToGRH :
      (∀ q : Nat, 0 < q → PacketSubexp (prim q)) →
        CayleyGRHClosure.GeneralizedRiemannHypothesis) :
    (RelativePropagationFromBase cyclo ↔
      GlobalPropagationFromBase cyclo) ∧
    (RelativePropagationFromBase cyclo →
      RHToGRHDAssembly.RHToGRHDTarget) := by
  constructor
  · exact RELATIVE_PROPAGATION_IFF_GLOBAL_PROPAGATION cyclo
  · intro hRelative
    exact
      RH_TO_GRH_D_OF_RELATIVE_CYCLOTOMIC_PROPAGATION
        cyclo prim hdecomp hRHBase hPrimitiveToGRH hRelative

end HVRRHGRHChainSync

#check HVRRHGRHChainSync.RelativePropagationFromBase
#check HVRRHGRHChainSync.GlobalPropagationFromBase
#check HVRRHGRHChainSync.RELATIVE_PROPAGATION_IFF_GLOBAL_PROPAGATION
#check HVRRHGRHChainSync.RH_TO_GRH_D_OF_RELATIVE_CYCLOTOMIC_PROPAGATION
#check HVRRHGRHChainSync.RIEMANN_HYPOTHESIS_IMPLIES_GENERALIZED_RIEMANN_HYPOTHESIS
#check HVRRHGRHChainSync.HVR_RH_GRH_B_TIER_LEAN_SYNCHRONIZATION

#print axioms HVRRHGRHChainSync.RELATIVE_PROPAGATION_IFF_GLOBAL_PROPAGATION
#print axioms HVRRHGRHChainSync.RH_TO_GRH_D_OF_RELATIVE_CYCLOTOMIC_PROPAGATION
#print axioms HVRRHGRHChainSync.RIEMANN_HYPOTHESIS_IMPLIES_GENERALIZED_RIEMANN_HYPOTHESIS
#print axioms HVRRHGRHChainSync.HVR_RH_GRH_B_TIER_LEAN_SYNCHRONIZATION
