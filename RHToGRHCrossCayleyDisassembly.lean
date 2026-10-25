import CayleyRHClosure
import RHToGRHCayleyLiftFrontier

namespace RHToGRHCrossCayley

open CayleyRHAClosure
open CayleyGRHClosure
open CayleyGRHStrong

/--
The cross-family Cayley transport that is still missing after both closure
packages have been established.  It says that the *actual ordinary* GolPhi
Cayley zero-loss property transports to totality of the *actual generalized*
completed-pair Dirichlet-L Cayley observable.

This is a proposition, not an axiom and not a theorem assumption hidden in a
definition.  The theorems below prove that it is exactly equivalent to the
remaining implication RH -> GRH.
-/
def GolPhiToGeneralizedCompletedPairCayleyTransfer : Prop :=
  GolPhiCayleyZeroLoss →
    GeneralizedCompletedPairActualCayleyObservableCriticalTotal

/-- Literal-zeta version of the same cross-family Cayley transport. -/
def ZetaToGeneralizedCompletedPairCayleyTransfer : Prop :=
  ZetaCayleyZeroLoss →
    GeneralizedCompletedPairActualCayleyObservableCriticalTotal

/--
The GolPhi cross-Cayley transport is exactly RH -> GRH.  Thus it is neither a
weaker sufficient condition nor a stronger auxiliary conjecture: it is the
same remaining mathematical content in the merged Cayley language.
-/
theorem GOLPHI_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH :
    GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis) := by
  constructor
  · intro hTransfer hRH
    have hOrdinary : GolPhiCayleyZeroLoss :=
      GOLPHI_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.mpr hRH
    have hGeneralized : GeneralizedCompletedPairActualCayleyObservableCriticalTotal :=
      hTransfer hOrdinary
    exact
      GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mp
        hGeneralized
  · intro hImp hOrdinary
    have hRH : _root_.RiemannHypothesis :=
      GOLPHI_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.mp hOrdinary
    have hGRH : GeneralizedRiemannHypothesis := hImp hRH
    exact
      GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mpr
        hGRH

/-- The literal-zeta cross-Cayley transport is also exactly RH -> GRH. -/
theorem ZETA_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH :
    ZetaToGeneralizedCompletedPairCayleyTransfer ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis) := by
  constructor
  · intro hTransfer hRH
    have hOrdinary : ZetaCayleyZeroLoss :=
      ZETA_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.mpr hRH
    have hGeneralized : GeneralizedCompletedPairActualCayleyObservableCriticalTotal :=
      hTransfer hOrdinary
    exact
      GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mp
        hGeneralized
  · intro hImp hOrdinary
    have hRH : _root_.RiemannHypothesis :=
      ZETA_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.mp hOrdinary
    have hGRH : GeneralizedRiemannHypothesis := hImp hRH
    exact
      GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mpr
        hGRH

/-- The GolPhi and literal-zeta cross-family transports are equivalent. -/
theorem GOLPHI_TRANSFER_IFF_ZETA_TRANSFER :
    GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      ZetaToGeneralizedCompletedPairCayleyTransfer := by
  exact
    GOLPHI_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH.trans
      ZETA_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH.symm

/--
The cross-Cayley formulation is exactly the previously frozen single frontier.
This ties the logical frontier package to the actual ordinary Cayley object.
-/
theorem GOLPHI_CROSS_CAYLEY_TRANSFER_IFF_SINGLE_FRONTIER :
    GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      RHToGRHFrontier.RiemannToGeneralizedCayleyLift := by
  exact
    GOLPHI_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH.trans
      RHToGRHFrontier.RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_GRH.symm

/-- The same transport is exactly RH -> literal all-character textbook GRH. -/
theorem GOLPHI_CROSS_CAYLEY_TRANSFER_IFF_RH_IMPLIES_TEXTBOOK_GRH :
    GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      (_root_.RiemannHypothesis → TextbookGeneralizedRiemannHypothesis) := by
  exact
    GOLPHI_CROSS_CAYLEY_TRANSFER_IFF_SINGLE_FRONTIER.trans
      RHToGRHFrontier.RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_TEXTBOOK_GRH

/-- Once the cross-Cayley transport is supplied, RH and GRH are equivalent. -/
theorem RH_IFF_GRH_OF_CROSS_CAYLEY_TRANSFER
    (hTransfer : GolPhiToGeneralizedCompletedPairCayleyTransfer) :
    _root_.RiemannHypothesis ↔ GeneralizedRiemannHypothesis := by
  exact RHToGRHFrontier.RH_IFF_GRH_OF_GENERALIZED_CAYLEY_LIFT
    (GOLPHI_CROSS_CAYLEY_TRANSFER_IFF_SINGLE_FRONTIER.mp hTransfer)

/--
Frozen disassembly atlas.  The first two conjuncts show that the ordinary
GolPhi and literal-zeta Cayley routes have exactly the same remaining content;
the third identifies that content with the already frozen RH-to-GRH frontier.
-/
theorem RH_TO_GRH_CROSS_CAYLEY_DISASSEMBLY_ATLAS :
    (GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis)) ∧
    (ZetaToGeneralizedCompletedPairCayleyTransfer ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis)) ∧
    (GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      RHToGRHFrontier.RiemannToGeneralizedCayleyLift) := by
  exact ⟨
    GOLPHI_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH,
    ZETA_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH,
    GOLPHI_CROSS_CAYLEY_TRANSFER_IFF_SINGLE_FRONTIER⟩

end RHToGRHCrossCayley
