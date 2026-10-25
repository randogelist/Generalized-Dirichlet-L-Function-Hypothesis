import RHToGRHCompletedPairFactorFrontier

namespace RHToGRHCompletedLFactor

open CayleyGRHStrong
open RHToGRHCompletedPairFactor

/--
The RH -> GRH frontier after unfolding each completed Dirichlet pair.
For every primitive character and every critical square/slit point, all four
completed Dirichlet L factors occurring at `s = 1/2 + sqrt z` and `1 - s`
are nonzero.

This definition is still only the open analytic frontier; no RH -> GRH claim
is assumed or proved here.
-/
def RiemannToPrimitiveCharacterCompletedLFactorsNonzero : Prop :=
  _root_.RiemannHypothesis →
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive →
        ∀ z ∈ completedPairCriticalSquareDomain,
          z ∈ Complex.slitPlane →
            DirichletCharacter.completedLFunction χ (1 / 2 + z.sqrt) ≠ 0 ∧
            DirichletCharacter.completedLFunction χ⁻¹ (1 / 2 + z.sqrt) ≠ 0 ∧
            DirichletCharacter.completedLFunction χ (1 - (1 / 2 + z.sqrt)) ≠ 0 ∧
            DirichletCharacter.completedLFunction χ⁻¹ (1 - (1 / 2 + z.sqrt)) ≠ 0

/--
Unfolding `completedDirichletPair` turns the two completed-pair nonvanishing
conditions into exactly four completed-L nonvanishing conditions.  This step
is pure algebra and uses no analytic hypothesis beyond the frontier arguments.
-/
theorem COMPLETED_L_FACTORS_NONZERO_IFF_COMPLETED_PAIR_FACTORS_NONZERO :
    RiemannToPrimitiveCharacterCompletedLFactorsNonzero ↔
      RiemannToPrimitiveCharacterCompletedPairFactorsNonzero := by
  constructor
  · intro hL hRH N inst χ hprim z hzdom hzslit
    rcases hL hRH N χ hprim z hzdom hzslit with ⟨hχs, hχis, hχr, hχir⟩
    constructor
    · rw [completedDirichletPair]
      exact mul_ne_zero hχs hχis
    · rw [completedDirichletPair]
      exact mul_ne_zero hχr hχir
  · intro hPair hRH N inst χ hprim z hzdom hzslit
    rcases hPair hRH N χ hprim z hzdom hzslit with ⟨hPs, hPr⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hzero
      apply hPs
      rw [completedDirichletPair, hzero, zero_mul]
    · intro hzero
      apply hPs
      rw [completedDirichletPair, hzero, mul_zero]
    · intro hzero
      apply hPr
      rw [completedDirichletPair, hzero, zero_mul]
    · intro hzero
      apply hPr
      rw [completedDirichletPair, hzero, mul_zero]

/-- Thus the four explicit completed-L factors are still exactly RH -> GRH. -/
theorem COMPLETED_L_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH :
    RiemannToPrimitiveCharacterCompletedLFactorsNonzero ↔
      (_root_.RiemannHypothesis → CayleyGRHClosure.GeneralizedRiemannHypothesis) := by
  exact
    COMPLETED_L_FACTORS_NONZERO_IFF_COMPLETED_PAIR_FACTORS_NONZERO.trans
      COMPLETED_PAIR_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH

/-- One first-half completed-L point obligation, isolated for the analytic step. -/
def CompletedLFirstCharacterPointObligation
    (hRH : _root_.RiemannHypothesis)
    (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hprim : χ.IsPrimitive)
    (z : ℂ)
    (hzdom : z ∈ completedPairCriticalSquareDomain)
    (hzslit : z ∈ Complex.slitPlane) : Prop :=
  DirichletCharacter.completedLFunction χ (1 / 2 + z.sqrt) ≠ 0

/-- Frozen four-factor disassembly atlas. -/
theorem RH_TO_GRH_COMPLETED_L_FACTOR_FRONTIER_ATLAS :
    (RiemannToPrimitiveCharacterCompletedLFactorsNonzero ↔
      RiemannToPrimitiveCharacterCompletedPairFactorsNonzero) ∧
    (RiemannToPrimitiveCharacterCompletedLFactorsNonzero ↔
      (_root_.RiemannHypothesis → CayleyGRHClosure.GeneralizedRiemannHypothesis)) := by
  exact ⟨
    COMPLETED_L_FACTORS_NONZERO_IFF_COMPLETED_PAIR_FACTORS_NONZERO,
    COMPLETED_L_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH⟩

end RHToGRHCompletedLFactor
