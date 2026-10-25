import RHToGRHCrossCayleyDisassembly

namespace RHToGRHPrimitiveCharacter

open CayleyRHAClosure
open CayleyGRHClosure
open CayleyGRHStrong
open RHToGRHCrossCayley

/--
The RH -> GRH frontier after descending all family wrappers: under ordinary
Riemann Hypothesis, every primitive Dirichlet character has zero-free actual
completed-pair slit-theta on the critical slit domain.

This is a proposition only.  It does not assert or assume the proposition.
-/
def RiemannToPrimitiveCharacterSlitThetaZeroFree : Prop :=
  _root_.RiemannHypothesis →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive →
        CompletedPairSlitThetaCriticalZeroFree χ

/-- Pointwise actual-Cayley version of the same primitive-character frontier. -/
def RiemannToPrimitiveCharacterActualCayleyTotal : Prop :=
  _root_.RiemannHypothesis →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive →
        CompletedPairActualCayleyObservableCriticalTotal χ

/--
The explicit primitive-character slit-theta formulation is definitionally the
family slit-theta lift, with the family wrapper removed.
-/
theorem PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE_IFF_GENERALIZED_ZERO_FREE_LIFT :
    RiemannToPrimitiveCharacterSlitThetaZeroFree ↔
      (_root_.RiemannHypothesis →
        GeneralizedCompletedPairSlitThetaCriticalZeroFree) := by
  constructor
  · intro h hRH N inst χ hprim
    exact h hRH N χ hprim
  · intro h hRH N inst χ hprim
    exact h hRH N χ hprim

/--
The explicit primitive-character actual-Cayley formulation is definitionally
the family actual-Cayley lift, with the family wrapper removed.
-/
theorem PRIMITIVE_CHARACTER_ACTUAL_CAYLEY_TOTAL_IFF_GENERALIZED_CAYLEY_LIFT :
    RiemannToPrimitiveCharacterActualCayleyTotal ↔
      (_root_.RiemannHypothesis →
        GeneralizedCompletedPairActualCayleyObservableCriticalTotal) := by
  constructor
  · intro h hRH N inst χ hprim
    exact h hRH N χ hprim
  · intro h hRH N inst χ hprim
    exact h hRH N χ hprim

/--
Pointwise actual-Cayley totality and pointwise slit-theta zero-freeness are
exactly the same RH -> primitive-character frontier.
-/
theorem PRIMITIVE_CHARACTER_ACTUAL_CAYLEY_TOTAL_IFF_SLIT_THETA_ZERO_FREE :
    RiemannToPrimitiveCharacterActualCayleyTotal ↔
      RiemannToPrimitiveCharacterSlitThetaZeroFree := by
  constructor
  · intro hTotal hRH N inst χ hprim
    exact
      (COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_ZERO_FREE χ).mp
        (hTotal hRH N χ hprim)
  · intro hZero hRH N inst χ hprim
    exact
      (COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_ZERO_FREE χ).mpr
        (hZero hRH N χ hprim)

/--
The primitive-character slit-theta frontier is exactly RH -> GRH.
No additional implication remains between this proposition and GRH.
-/
theorem PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE_IFF_RH_IMPLIES_GRH :
    RiemannToPrimitiveCharacterSlitThetaZeroFree ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis) := by
  constructor
  · intro hPointwise hRH
    have hFamily : GeneralizedCompletedPairSlitThetaCriticalZeroFree :=
      (PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE_IFF_GENERALIZED_ZERO_FREE_LIFT.mp
        hPointwise) hRH
    exact GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH.mp hFamily
  · intro hImp
    apply PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE_IFF_GENERALIZED_ZERO_FREE_LIFT.mpr
    intro hRH
    exact GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH.mpr
      (hImp hRH)

/-- A simpler proof of the actual-Cayley primitive frontier equivalence. -/
theorem PRIMITIVE_CHARACTER_ACTUAL_CAYLEY_TOTAL_IFF_RH_IMPLIES_GRH :
    RiemannToPrimitiveCharacterActualCayleyTotal ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis) := by
  exact
    PRIMITIVE_CHARACTER_ACTUAL_CAYLEY_TOTAL_IFF_SLIT_THETA_ZERO_FREE.trans
      PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE_IFF_RH_IMPLIES_GRH

/--
The previous cross-Cayley transfer is exactly the pointwise primitive-character
zero-free theorem.  This is the desired descent from family language to a
single arbitrary primitive character.
-/
theorem CROSS_CAYLEY_TRANSFER_IFF_PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE :
    GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      RiemannToPrimitiveCharacterSlitThetaZeroFree := by
  exact
    GOLPHI_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH.trans
      PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE_IFF_RH_IMPLIES_GRH.symm

/-- The same descent in the actual-Cayley observable language. -/
theorem CROSS_CAYLEY_TRANSFER_IFF_PRIMITIVE_CHARACTER_ACTUAL_CAYLEY_TOTAL :
    GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      RiemannToPrimitiveCharacterActualCayleyTotal := by
  exact
    GOLPHI_TO_GENERALIZED_COMPLETED_PAIR_CAYLEY_TRANSFER_IFF_RH_IMPLIES_GRH.trans
      PRIMITIVE_CHARACTER_ACTUAL_CAYLEY_TOTAL_IFF_RH_IMPLIES_GRH.symm

/--
Frozen primitive-character disassembly atlas.  Every listed formulation has
exactly the same missing mathematical content: RH -> GRH.
-/
theorem RH_TO_GRH_PRIMITIVE_CHARACTER_FRONTIER_ATLAS :
    (RiemannToPrimitiveCharacterSlitThetaZeroFree ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis)) ∧
    (RiemannToPrimitiveCharacterActualCayleyTotal ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis)) ∧
    (GolPhiToGeneralizedCompletedPairCayleyTransfer ↔
      RiemannToPrimitiveCharacterSlitThetaZeroFree) ∧
    (RiemannToPrimitiveCharacterActualCayleyTotal ↔
      RiemannToPrimitiveCharacterSlitThetaZeroFree) := by
  exact ⟨
    PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE_IFF_RH_IMPLIES_GRH,
    PRIMITIVE_CHARACTER_ACTUAL_CAYLEY_TOTAL_IFF_RH_IMPLIES_GRH,
    CROSS_CAYLEY_TRANSFER_IFF_PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE,
    PRIMITIVE_CHARACTER_ACTUAL_CAYLEY_TOTAL_IFF_SLIT_THETA_ZERO_FREE⟩

end RHToGRHPrimitiveCharacter
