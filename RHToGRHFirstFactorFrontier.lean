import RHToGRHCompletedLFactorFrontier
import PrimitiveCompletedPair

/-!
Source candidate: not compiled or natively axiom-audited in this session.
This reduces the four-factor frontier to one universal first-factor family.
It does not establish that family, RH, or RH -> GRH.
-/

set_option autoImplicit false

namespace RHToGRHFirstFactor

open CayleyGRHStrong
open RHToGRHCompletedLFactor

def RiemannToPrimitiveCharacterFirstCompletedLFactorNonzero : Prop :=
  _root_.RiemannHypothesis →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive →
        ∀ z ∈ completedPairCriticalSquareDomain,
          z ∈ Complex.slitPlane →
            DirichletCharacter.completedLFunction χ (1 / 2 + z.sqrt) ≠ 0

theorem FIRST_FACTOR_IFF_FOUR_FACTORS :
    RiemannToPrimitiveCharacterFirstCompletedLFactorNonzero ↔
      RiemannToPrimitiveCharacterCompletedLFactorsNonzero := by
  constructor
  · intro h hRH N inst χ hχ z hzdom hzslit
    have hχs := h hRH N χ hχ z hzdom hzslit
    have hχis := h hRH N χ⁻¹ (primitive_inv hχ) z hzdom hzslit
    refine ⟨hχs, hχis, ?_, ?_⟩
    · intro hzero
      exact hχis ((PRIMITIVE_COMPLETED_ZERO_REFLECTION_IFF hχ
        (1 / 2 + z.sqrt)).mp hzero)
    · intro hzero
      have hback := (PRIMITIVE_COMPLETED_ZERO_REFLECTION_IFF
        (primitive_inv hχ) (1 / 2 + z.sqrt)).mp hzero
      exact hχs (by simpa only [inv_inv] using hback)
  · intro h hRH N inst χ hχ z hzdom hzslit
    exact (h hRH N χ hχ z hzdom hzslit).1

theorem FIRST_FACTOR_IFF_RH_IMPLIES_GRH :
    RiemannToPrimitiveCharacterFirstCompletedLFactorNonzero ↔
      (_root_.RiemannHypothesis →
        CayleyGRHClosure.GeneralizedRiemannHypothesis) := by
  exact FIRST_FACTOR_IFF_FOUR_FACTORS.trans
    COMPLETED_L_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH

end RHToGRHFirstFactor
