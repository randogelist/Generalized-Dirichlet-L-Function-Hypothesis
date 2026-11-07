import HVR_GENERALIZED_CAYLEY_LIFT_BRIDGE
import GRHFinal.Audit

set_option autoImplicit false

noncomputable section

namespace GeneralizedDirichletHVRJoint

open HVRCyclotomicPacketTower
open HVRRHGRHChainSync
open HVRGeneralizedCayleyLiftBridge

/--
The joint-project root.

No original repository theorem is replaced.  The HVR route supplies the
existing generalized Cayley-lift premise under the explicit relative
completed-packet propagation condition; the repository's original main
equivalence theorem is then reused unchanged.
-/
theorem JOINT_HVR_GENERALIZED_DIRICHLET_MAIN
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
      CayleyGRHStrong.TextbookGeneralizedRiemannHypothesis) :=
  HVR_GENERALIZED_CAYLEY_LIFT_BRIDGE_ATLAS
    cyclo prim hdecomp hRHBase hPrimitiveToGRH hRelative

end GeneralizedDirichletHVRJoint

/-
Legacy theorem visibility checks.  These declarations predate the HVR merge
and are intentionally referenced without renaming or wrapping.
-/
#check CayleyGRHStrong.GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH
#check RHToGRHFrontier.RH_TO_GRH_SINGLE_FRONTIER_ATLAS
#check RHToGRHFrontier.RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT
#check RHToGRHPrimitiveCharacter.RH_TO_GRH_PRIMITIVE_CHARACTER_FRONTIER_ATLAS
#check RHToGRHCompletedPairFactor.RH_TO_GRH_COMPLETED_PAIR_FACTOR_FRONTIER_ATLAS

/-
HVR theorem visibility checks.
-/
#check HVRCyclotomicPacketTower.HVR_CYCLOTOMIC_COMPLETED_PACKET_TOWER
#check HVRRHGRHChainSync.HVR_RH_GRH_B_TIER_LEAN_SYNCHRONIZATION
#check HVRGeneralizedCayleyLiftBridge.HVR_GENERALIZED_CAYLEY_LIFT_BRIDGE_ATLAS
#check GeneralizedDirichletHVRJoint.JOINT_HVR_GENERALIZED_DIRICHLET_MAIN

#print axioms GeneralizedDirichletHVRJoint.JOINT_HVR_GENERALIZED_DIRICHLET_MAIN
