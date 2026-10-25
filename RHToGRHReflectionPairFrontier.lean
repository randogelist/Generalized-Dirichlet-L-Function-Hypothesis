import RHToGRHCenteredPairFrontier

namespace RHToGRHReflectionPair

open CayleyGRHStrong
open RHToGRHCenteredPair

/--
The RH -> GRH frontier with the centered-completed-pair wrapper unfolded.
For each primitive character and each critical square/slit point, the
reflection-symmetrized completed Dirichlet pair at `1/2 + sqrt z` is nonzero.

This is only a proposition defining the open analytic frontier.
-/
def RiemannToPrimitiveCharacterReflectionPairNonzero : Prop :=
  _root_.RiemannHypothesis →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive →
        ∀ z ∈ completedPairCriticalSquareDomain,
          z ∈ Complex.slitPlane →
            reflectionSymmetrizedCompletedPair χ (1 / 2 + z.sqrt) ≠ 0

/-- Unfolding `centeredCompletedDirichletPair` is definitionally exact. -/
theorem REFLECTION_PAIR_NONZERO_IFF_CENTERED_PAIR_NONZERO :
    RiemannToPrimitiveCharacterReflectionPairNonzero ↔
      RiemannToPrimitiveCharacterCenteredCompletedPairNonzero := by
  rfl

/-- Hence this reflection-pair statement is exactly RH -> GRH. -/
theorem REFLECTION_PAIR_NONZERO_IFF_RH_IMPLIES_GRH :
    RiemannToPrimitiveCharacterReflectionPairNonzero ↔
      (_root_.RiemannHypothesis → CayleyGRHClosure.GeneralizedRiemannHypothesis) := by
  exact
    REFLECTION_PAIR_NONZERO_IFF_CENTERED_PAIR_NONZERO.trans
      CENTERED_COMPLETED_PAIR_NONZERO_IFF_RH_IMPLIES_GRH

/-- Pointwise analytic obligation after all logical/family wrappers are fixed. -/
def ReflectionPairPointObligation
    (hRH : _root_.RiemannHypothesis)
    (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive)
    (z : ℂ)
    (hzdom : z ∈ completedPairCriticalSquareDomain)
    (hzslit : z ∈ Complex.slitPlane) : Prop :=
  reflectionSymmetrizedCompletedPair χ (1 / 2 + z.sqrt) ≠ 0

/-- Frozen reflection-pair disassembly atlas. -/
theorem RH_TO_GRH_REFLECTION_PAIR_FRONTIER_ATLAS :
    (RiemannToPrimitiveCharacterReflectionPairNonzero ↔
      RiemannToPrimitiveCharacterCenteredCompletedPairNonzero) ∧
    (RiemannToPrimitiveCharacterReflectionPairNonzero ↔
      (_root_.RiemannHypothesis → CayleyGRHClosure.GeneralizedRiemannHypothesis)) := by
  exact ⟨
    REFLECTION_PAIR_NONZERO_IFF_CENTERED_PAIR_NONZERO,
    REFLECTION_PAIR_NONZERO_IFF_RH_IMPLIES_GRH⟩

end RHToGRHReflectionPair
