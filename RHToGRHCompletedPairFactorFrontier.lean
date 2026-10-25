import RHToGRHReflectionPairFrontier

namespace RHToGRHCompletedPairFactor

open CayleyGRHStrong
open RHToGRHReflectionPair

/--
The RH -> GRH frontier after unfolding the reflection-symmetrized product.
For each primitive character and each critical square/slit point, BOTH actual
completed Dirichlet-pair factors are nonzero at the reflected points
`s = 1/2 + sqrt z` and `1 - s`.

This is only a proposition defining the open analytic frontier.
-/
def RiemannToPrimitiveCharacterCompletedPairFactorsNonzero : Prop :=
  _root_.RiemannHypothesis →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive →
        ∀ z ∈ completedPairCriticalSquareDomain,
          z ∈ Complex.slitPlane →
            completedDirichletPair χ (1 / 2 + z.sqrt) ≠ 0 ∧
            completedDirichletPair χ (1 - (1 / 2 + z.sqrt)) ≠ 0

/--
Over `ℂ`, nonvanishing of the reflection product is exactly nonvanishing of
both completed-pair factors.  No analytic input is used here.
-/
theorem COMPLETED_PAIR_FACTORS_NONZERO_IFF_REFLECTION_PAIR_NONZERO :
    RiemannToPrimitiveCharacterCompletedPairFactorsNonzero ↔
      RiemannToPrimitiveCharacterReflectionPairNonzero := by
  constructor
  · intro hFactors hRH N inst χ hprim z hzdom hzslit
    rcases hFactors hRH N χ hprim z hzdom hzslit with ⟨h₁, h₂⟩
    rw [reflectionSymmetrizedCompletedPair]
    exact mul_ne_zero h₁ h₂
  · intro hReflection hRH N inst χ hprim z hzdom hzslit
    have hprod := hReflection hRH N χ hprim z hzdom hzslit
    constructor
    · intro hzero
      apply hprod
      rw [reflectionSymmetrizedCompletedPair, hzero, zero_mul]
    · intro hzero
      apply hprod
      rw [reflectionSymmetrizedCompletedPair, hzero, mul_zero]

/-- Hence the two-factor completed-pair statement is exactly RH -> GRH. -/
theorem COMPLETED_PAIR_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH :
    RiemannToPrimitiveCharacterCompletedPairFactorsNonzero ↔
      (_root_.RiemannHypothesis → CayleyGRHClosure.GeneralizedRiemannHypothesis) := by
  exact
    COMPLETED_PAIR_FACTORS_NONZERO_IFF_REFLECTION_PAIR_NONZERO.trans
      REFLECTION_PAIR_NONZERO_IFF_RH_IMPLIES_GRH

/-- First factor, isolated as a pointwise analytic obligation. -/
def CompletedPairFirstFactorPointObligation
    (hRH : _root_.RiemannHypothesis)
    (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive)
    (z : ℂ)
    (hzdom : z ∈ completedPairCriticalSquareDomain)
    (hzslit : z ∈ Complex.slitPlane) : Prop :=
  completedDirichletPair χ (1 / 2 + z.sqrt) ≠ 0

/-- Reflected factor, isolated as a pointwise analytic obligation. -/
def CompletedPairReflectedFactorPointObligation
    (hRH : _root_.RiemannHypothesis)
    (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive)
    (z : ℂ)
    (hzdom : z ∈ completedPairCriticalSquareDomain)
    (hzslit : z ∈ Complex.slitPlane) : Prop :=
  completedDirichletPair χ (1 - (1 / 2 + z.sqrt)) ≠ 0

/-- Frozen two-factor disassembly atlas. -/
theorem RH_TO_GRH_COMPLETED_PAIR_FACTOR_FRONTIER_ATLAS :
    (RiemannToPrimitiveCharacterCompletedPairFactorsNonzero ↔
      RiemannToPrimitiveCharacterReflectionPairNonzero) ∧
    (RiemannToPrimitiveCharacterCompletedPairFactorsNonzero ↔
      (_root_.RiemannHypothesis → CayleyGRHClosure.GeneralizedRiemannHypothesis)) := by
  exact ⟨
    COMPLETED_PAIR_FACTORS_NONZERO_IFF_REFLECTION_PAIR_NONZERO,
    COMPLETED_PAIR_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH⟩

end RHToGRHCompletedPairFactor
