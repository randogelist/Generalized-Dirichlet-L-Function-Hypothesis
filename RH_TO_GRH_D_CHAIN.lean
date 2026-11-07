import RHToGRHCrossCayleyDisassembly

set_option autoImplicit false

namespace RHToGRHDAssembly

/-- The exact primitive-character Dirichlet-GRH target used by the project. -/
def RHToGRHDTarget : Prop :=
  _root_.RiemannHypothesis →
    CayleyGRHClosure.GeneralizedRiemannHypothesis

/-- The literal all-character textbook Dirichlet-GRH target. -/
def RHToTextbookGRHDTarget : Prop :=
  _root_.RiemannHypothesis →
    CayleyGRHStrong.TextbookGeneralizedRiemannHypothesis

/-- The exact target is definitionally the existing generalized Cayley lift. -/
theorem RH_TO_GRH_D_TARGET_IFF_GENERALIZED_CAYLEY_LIFT :
    RHToGRHDTarget ↔
      RHToGRHFrontier.RiemannToGeneralizedCayleyLift := by
  exact
    RHToGRHFrontier.RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_GRH.symm

/-- The exact target is also definitionally the ordinary-to-generalized
cross-Cayley transport. -/
theorem RH_TO_GRH_D_TARGET_IFF_CROSS_CAYLEY_TRANSFER :
    RHToGRHDTarget ↔
      RHToGRHCrossCayley.GolPhiToGeneralizedCompletedPairCayleyTransfer := by
  exact
    RHToGRHCrossCayley.GOLPHI_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH.symm

/-- Literal-zeta and completed-GolPhi cross transfers give the same target. -/
theorem RH_TO_GRH_D_TARGET_IFF_ZETA_CROSS_CAYLEY_TRANSFER :
    RHToGRHDTarget ↔
      RHToGRHCrossCayley.ZetaToGeneralizedCompletedPairCayleyTransfer := by
  exact
    RHToGRHCrossCayley.ZETA_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH.symm

/-- Explicit deterministic chain:

    Mathlib RH
      -> actual ordinary completed-GolPhi Cayley zero loss
      -> generalized completed-pair actual-Cayley totality
      -> primitive-character Dirichlet GRH.

The sole additional premise is the named cross-family transfer. -/
theorem RH_TO_GRH_D_CHAIN_OF_CROSS_TRANSFER
    (hCross :
      RHToGRHCrossCayley.GolPhiToGeneralizedCompletedPairCayleyTransfer)
    (hRH : _root_.RiemannHypothesis) :
    CayleyGRHClosure.GeneralizedRiemannHypothesis := by
  have hOrdinary : CayleyRHAClosure.GolPhiCayleyZeroLoss :=
    CayleyRHAClosure.GOLPHI_CAYLEY_ZERO_LOSS_IFF_MATHLIB_RH.mpr hRH
  have hGeneralized :
      CayleyGRHStrong.GeneralizedCompletedPairActualCayleyObservableCriticalTotal :=
    hCross hOrdinary
  exact
    CayleyGRHStrong.GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mp
      hGeneralized

/-- The same chain through the existing generalized-lift interface. -/
theorem RH_TO_GRH_D_CHAIN_OF_GENERALIZED_CAYLEY_LIFT
    (hLift : RHToGRHFrontier.RiemannToGeneralizedCayleyLift)
    (hRH : _root_.RiemannHypothesis) :
    CayleyGRHClosure.GeneralizedRiemannHypothesis := by
  exact
    (RHToGRHFrontier.RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_GRH.mp hLift) hRH

/-- Primitive-character GRH implies Mathlib RH by the conductor-one case. -/
theorem GRH_D_TO_MATHLIB_RH
    (hGRH : CayleyGRHClosure.GeneralizedRiemannHypothesis) :
    _root_.RiemannHypothesis := by
  exact CayleyGRHClosure.GRH_IMPLIES_MATHLIB_RH hGRH

/-- Under the named cross transfer, Mathlib RH and primitive Dirichlet GRH
are equivalent. -/
theorem RH_IFF_GRH_D_OF_CROSS_TRANSFER
    (hCross :
      RHToGRHCrossCayley.GolPhiToGeneralizedCompletedPairCayleyTransfer) :
    _root_.RiemannHypothesis ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis := by
  constructor
  · exact RH_TO_GRH_D_CHAIN_OF_CROSS_TRANSFER hCross
  · exact GRH_D_TO_MATHLIB_RH

/-- The primitive target implies the literal all-character textbook target
through the established primitive/imprimitive Euler-factor bridge. -/
theorem RH_TO_TEXTBOOK_GRH_D_CHAIN_OF_CROSS_TRANSFER
    (hCross :
      RHToGRHCrossCayley.GolPhiToGeneralizedCompletedPairCayleyTransfer)
    (hRH : _root_.RiemannHypothesis) :
    CayleyGRHStrong.TextbookGeneralizedRiemannHypothesis := by
  exact
    CayleyGRHStrong.GRH_IMPLIES_TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS
      (RH_TO_GRH_D_CHAIN_OF_CROSS_TRANSFER hCross hRH)

/-- The exact primitive and textbook target implications are equivalent. -/
theorem RH_TO_TEXTBOOK_GRH_D_TARGET_IFF_PRIMITIVE_TARGET :
    RHToTextbookGRHDTarget ↔ RHToGRHDTarget := by
  constructor
  · intro hText hRH
    exact
      CayleyGRHStrong.TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IMPLIES_GRH
        (hText hRH)
  · intro hPrimitive hRH
    exact
      CayleyGRHStrong.GRH_IMPLIES_TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS
        (hPrimitive hRH)

end RHToGRHDAssembly

#check RHToGRHDAssembly.RHToGRHDTarget
#check RHToGRHDAssembly.RH_TO_GRH_D_TARGET_IFF_GENERALIZED_CAYLEY_LIFT
#check RHToGRHDAssembly.RH_TO_GRH_D_TARGET_IFF_CROSS_CAYLEY_TRANSFER
#check RHToGRHDAssembly.RH_TO_GRH_D_CHAIN_OF_CROSS_TRANSFER
#check RHToGRHDAssembly.RH_TO_GRH_D_CHAIN_OF_GENERALIZED_CAYLEY_LIFT
#check RHToGRHDAssembly.RH_IFF_GRH_D_OF_CROSS_TRANSFER
#check RHToGRHDAssembly.RH_TO_TEXTBOOK_GRH_D_CHAIN_OF_CROSS_TRANSFER

#print axioms RHToGRHDAssembly.RH_TO_GRH_D_TARGET_IFF_GENERALIZED_CAYLEY_LIFT
#print axioms RHToGRHDAssembly.RH_TO_GRH_D_TARGET_IFF_CROSS_CAYLEY_TRANSFER
#print axioms RHToGRHDAssembly.RH_TO_GRH_D_CHAIN_OF_CROSS_TRANSFER
#print axioms RHToGRHDAssembly.RH_TO_GRH_D_CHAIN_OF_GENERALIZED_CAYLEY_LIFT
#print axioms RHToGRHDAssembly.RH_IFF_GRH_D_OF_CROSS_TRANSFER
#print axioms RHToGRHDAssembly.RH_TO_TEXTBOOK_GRH_D_CHAIN_OF_CROSS_TRANSFER
