import RHToGRHPrimitiveCharacterFrontier

namespace RHToGRHCenteredPair

open CayleyGRHStrong
open RHToGRHPrimitiveCharacter

/--
The primitive-character RH -> GRH frontier with the slit-theta wrapper fully
unfolded.  For every primitive Dirichlet character and every point in the
critical square/slit domain, the centered completed Dirichlet pair evaluated
at the principal square root must be nonzero.

This is a proposition only; it is not asserted here.
-/
def RiemannToPrimitiveCharacterCenteredCompletedPairNonzero : Prop :=
  _root_.RiemannHypothesis →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive →
        ∀ z ∈ completedPairCriticalSquareDomain,
          z ∈ Complex.slitPlane →
            centeredCompletedDirichletPair χ z.sqrt ≠ 0

/--
Unfolding `CompletedPairSlitThetaCriticalZeroFree` and
`completedPairSlitTheta` shows that the centered-pair formulation is exactly
our previous primitive-character zero-free frontier.
-/
theorem CENTERED_COMPLETED_PAIR_NONZERO_IFF_PRIMITIVE_SLIT_THETA_ZERO_FREE :
    RiemannToPrimitiveCharacterCenteredCompletedPairNonzero ↔
      RiemannToPrimitiveCharacterSlitThetaZeroFree := by
  rfl

/-- Hence the centered completed-pair nonvanishing target is exactly RH -> GRH. -/
theorem CENTERED_COMPLETED_PAIR_NONZERO_IFF_RH_IMPLIES_GRH :
    RiemannToPrimitiveCharacterCenteredCompletedPairNonzero ↔
      (_root_.RiemannHypothesis → CayleyGRHClosure.GeneralizedRiemannHypothesis) := by
  exact
    CENTERED_COMPLETED_PAIR_NONZERO_IFF_PRIMITIVE_SLIT_THETA_ZERO_FREE.trans
      PRIMITIVE_CHARACTER_SLIT_THETA_ZERO_FREE_IFF_RH_IMPLIES_GRH

/--
A pointwise form exposing the actual analytic obligation after fixing the RH
hypothesis, modulus, primitive character, and critical square point.
-/
def CenteredCompletedPairPointObligation
    (hRH : _root_.RiemannHypothesis)
    (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive)
    (z : ℂ)
    (hzdom : z ∈ completedPairCriticalSquareDomain)
    (hzslit : z ∈ Complex.slitPlane) : Prop :=
  centeredCompletedDirichletPair χ z.sqrt ≠ 0

/-- The global frontier is precisely the universal closure of the point obligation. -/
theorem CENTERED_COMPLETED_PAIR_GLOBAL_IFF_POINTWISE :
    RiemannToPrimitiveCharacterCenteredCompletedPairNonzero ↔
      (_root_.RiemannHypothesis →
        ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          ∀ (hprim : χ.IsPrimitive) (z : ℂ)
            (hzdom : z ∈ completedPairCriticalSquareDomain)
            (hzslit : z ∈ Complex.slitPlane),
              CenteredCompletedPairPointObligation
                (N := N) (χ := χ) hRH hprim z hzdom hzslit) := by
  rfl

/-- Frozen one-layer analytic disassembly atlas. -/
theorem RH_TO_GRH_CENTERED_PAIR_FRONTIER_ATLAS :
    (RiemannToPrimitiveCharacterCenteredCompletedPairNonzero ↔
      RiemannToPrimitiveCharacterSlitThetaZeroFree) ∧
    (RiemannToPrimitiveCharacterCenteredCompletedPairNonzero ↔
      (_root_.RiemannHypothesis → CayleyGRHClosure.GeneralizedRiemannHypothesis)) := by
  exact ⟨
    CENTERED_COMPLETED_PAIR_NONZERO_IFF_PRIMITIVE_SLIT_THETA_ZERO_FREE,
    CENTERED_COMPLETED_PAIR_NONZERO_IFF_RH_IMPLIES_GRH⟩

end RHToGRHCenteredPair
