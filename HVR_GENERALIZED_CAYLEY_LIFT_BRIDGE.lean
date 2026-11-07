import HVR_RH_GRH_CHAIN_SYNC
import RH_TO_GRH_D_CHAIN

set_option autoImplicit false

noncomputable section

namespace HVRGeneralizedCayleyLiftBridge

open HVRCyclotomicPacketTower
open HVRRHGRHChainSync

/--
The synchronized HVR relative completed-packet propagation route supplies
the exact `RiemannToGeneralizedCayleyLift` proposition used by the existing
Generalized-Dirichlet-L-Function-Hypothesis repository.

The repository theorem identifying the generalized Cayley lift with
`RiemannHypothesis → GeneralizedRiemannHypothesis` is used unchanged.
-/
theorem HVR_RELATIVE_PROPAGATION_IMPLIES_GENERALIZED_CAYLEY_LIFT
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
    RHToGRHFrontier.RiemannToGeneralizedCayleyLift := by
  apply
    RHToGRHFrontier.RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_GRH.mpr
  exact
    HVRRHGRHChainSync.RIEMANN_HYPOTHESIS_IMPLIES_GENERALIZED_RIEMANN_HYPOTHESIS
      cyclo prim hdecomp hRHBase hPrimitiveToGRH hRelative

/--
Under the synchronized HVR relative propagation premise, the repository's
existing primitive-character RH/GRH equivalence theorem applies verbatim.
-/
theorem HVR_RELATIVE_PROPAGATION_IMPLIES_RH_IFF_GRH
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
    _root_.RiemannHypothesis ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis := by
  exact
    RHToGRHFrontier.RH_IFF_GRH_OF_GENERALIZED_CAYLEY_LIFT
      (HVR_RELATIVE_PROPAGATION_IMPLIES_GENERALIZED_CAYLEY_LIFT
        cyclo prim hdecomp hRHBase hPrimitiveToGRH hRelative)

/--
Under the same HVR premise, the repository's advertised textbook
all-character equivalence follows through its existing theorem without
altering that theorem.
-/
theorem HVR_RELATIVE_PROPAGATION_IMPLIES_RH_IFF_TEXTBOOK_GRH
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
    _root_.RiemannHypothesis ↔
      CayleyGRHStrong.TextbookGeneralizedRiemannHypothesis := by
  exact
    RHToGRHFrontier.RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT
      (HVR_RELATIVE_PROPAGATION_IMPLIES_GENERALIZED_CAYLEY_LIFT
        cyclo prim hdecomp hRHBase hPrimitiveToGRH hRelative)

/--
Joint atlas: the HVR route supplies the repository lift, and both existing
repository RH/GRH equivalences are then obtained unchanged.
-/
theorem HVR_GENERALIZED_CAYLEY_LIFT_BRIDGE_ATLAS
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
    RHToGRHFrontier.RiemannToGeneralizedCayleyLift ∧
    (_root_.RiemannHypothesis ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (_root_.RiemannHypothesis ↔
      CayleyGRHStrong.TextbookGeneralizedRiemannHypothesis) := by
  have hLift :
      RHToGRHFrontier.RiemannToGeneralizedCayleyLift :=
    HVR_RELATIVE_PROPAGATION_IMPLIES_GENERALIZED_CAYLEY_LIFT
      cyclo prim hdecomp hRHBase hPrimitiveToGRH hRelative
  exact
    ⟨hLift,
      RHToGRHFrontier.RH_IFF_GRH_OF_GENERALIZED_CAYLEY_LIFT hLift,
      RHToGRHFrontier.RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT hLift⟩

end HVRGeneralizedCayleyLiftBridge

#check RHToGRHFrontier.RiemannToGeneralizedCayleyLift
#check RHToGRHFrontier.RH_IFF_GRH_OF_GENERALIZED_CAYLEY_LIFT
#check RHToGRHFrontier.RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT
#check HVRRHGRHChainSync.HVR_RH_GRH_B_TIER_LEAN_SYNCHRONIZATION
#check HVRGeneralizedCayleyLiftBridge.HVR_RELATIVE_PROPAGATION_IMPLIES_GENERALIZED_CAYLEY_LIFT
#check HVRGeneralizedCayleyLiftBridge.HVR_RELATIVE_PROPAGATION_IMPLIES_RH_IFF_GRH
#check HVRGeneralizedCayleyLiftBridge.HVR_RELATIVE_PROPAGATION_IMPLIES_RH_IFF_TEXTBOOK_GRH
#check HVRGeneralizedCayleyLiftBridge.HVR_GENERALIZED_CAYLEY_LIFT_BRIDGE_ATLAS

#print axioms HVRGeneralizedCayleyLiftBridge.HVR_RELATIVE_PROPAGATION_IMPLIES_GENERALIZED_CAYLEY_LIFT
#print axioms HVRGeneralizedCayleyLiftBridge.HVR_RELATIVE_PROPAGATION_IMPLIES_RH_IFF_GRH
#print axioms HVRGeneralizedCayleyLiftBridge.HVR_RELATIVE_PROPAGATION_IMPLIES_RH_IFF_TEXTBOOK_GRH
#print axioms HVRGeneralizedCayleyLiftBridge.HVR_GENERALIZED_CAYLEY_LIFT_BRIDGE_ATLAS
