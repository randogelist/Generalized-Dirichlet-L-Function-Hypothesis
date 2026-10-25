import CompletedPairCayleyAnalytic

namespace CayleyGRHStrong

open CayleyGRHClosure

/-- Cayley zero loss tested on nontrivial zeros of the actual completed
primitive inverse-pair. -/
def PrimitiveCompletedPairCayleyZeroLoss
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, PrimitiveCompletedPairNontrivialZero χ s →
    CayleyRHAClosure.spectralCayleyLoss s = 0

/-- Cayley saturation tested on nontrivial zeros of the actual completed pair. -/
def PrimitiveCompletedPairCayleySaturation
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, PrimitiveCompletedPairNontrivialZero χ s →
    CayleyRHAClosure.spectralCayleyTransmission s = 1

/-- Unit-energy preservation tested on nontrivial zeros of the actual completed pair. -/
def PrimitiveCompletedPairCayleyUnitEnergyPreservation
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, PrimitiveCompletedPairNontrivialZero χ s →
    GPBKQRKernel.scalarEnergy (GPBKQRKernel.cayleyStep s.re 1) =
      GPBKQRKernel.scalarEnergy 1

/-- Pair-level zero loss is exactly pair RH. -/
theorem PRIMITIVE_COMPLETED_PAIR_CAYLEY_ZERO_LOSS_IFF_PAIR_RH
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    PrimitiveCompletedPairCayleyZeroLoss χ ↔
      PrimitiveCompletedPairRiemannHypothesis χ := by
  change CayleyZeroLossFor (PrimitiveCompletedPairNontrivialZero χ) ↔
    CriticalLineZeroHypothesis (PrimitiveCompletedPairNontrivialZero χ)
  exact CAYLEY_ZERO_LOSS_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (PrimitiveCompletedPairNontrivialZero χ)

/-- Pair-level saturation is exactly pair RH. -/
theorem PRIMITIVE_COMPLETED_PAIR_CAYLEY_SATURATION_IFF_PAIR_RH
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    PrimitiveCompletedPairCayleySaturation χ ↔
      PrimitiveCompletedPairRiemannHypothesis χ := by
  change CayleySaturationFor (PrimitiveCompletedPairNontrivialZero χ) ↔
    CriticalLineZeroHypothesis (PrimitiveCompletedPairNontrivialZero χ)
  exact CAYLEY_SATURATION_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (PrimitiveCompletedPairNontrivialZero χ)

/-- Pair-level unit-energy preservation is exactly pair RH. -/
theorem PRIMITIVE_COMPLETED_PAIR_CAYLEY_UNIT_ENERGY_IFF_PAIR_RH
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    PrimitiveCompletedPairCayleyUnitEnergyPreservation χ ↔
      PrimitiveCompletedPairRiemannHypothesis χ := by
  change CayleyUnitEnergyPreservationFor (PrimitiveCompletedPairNontrivialZero χ) ↔
    CriticalLineZeroHypothesis (PrimitiveCompletedPairNontrivialZero χ)
  exact CAYLEY_UNIT_ENERGY_PRESERVATION_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (PrimitiveCompletedPairNontrivialZero χ)

/-- Family-level zero-loss criterion for all primitive completed inverse-pairs. -/
def GeneralizedCompletedPairCayleyZeroLoss : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → PrimitiveCompletedPairCayleyZeroLoss χ

/-- Family-level saturation criterion for all primitive completed inverse-pairs. -/
def GeneralizedCompletedPairCayleySaturation : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → PrimitiveCompletedPairCayleySaturation χ

/-- Family-level unit-energy criterion for all primitive completed inverse-pairs. -/
def GeneralizedCompletedPairCayleyUnitEnergyPreservation : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → PrimitiveCompletedPairCayleyUnitEnergyPreservation χ

/-- Strong completed-pair GRH closure in zero-loss form. -/
theorem GENERALIZED_COMPLETED_PAIR_CAYLEY_ZERO_LOSS_IFF_GRH :
    GeneralizedCompletedPairCayleyZeroLoss ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).1
      ((PRIMITIVE_COMPLETED_PAIR_CAYLEY_ZERO_LOSS_IFF_PAIR_RH χ).1 (h N χ hχ))
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_CAYLEY_ZERO_LOSS_IFF_PAIR_RH χ).2
      ((PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).2 (h N χ hχ))

/-- Strong completed-pair GRH closure in saturation form. -/
theorem GENERALIZED_COMPLETED_PAIR_CAYLEY_SATURATION_IFF_GRH :
    GeneralizedCompletedPairCayleySaturation ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).1
      ((PRIMITIVE_COMPLETED_PAIR_CAYLEY_SATURATION_IFF_PAIR_RH χ).1 (h N χ hχ))
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_CAYLEY_SATURATION_IFF_PAIR_RH χ).2
      ((PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).2 (h N χ hχ))

/-- Strong completed-pair GRH closure in unit-energy-preservation form. -/
theorem GENERALIZED_COMPLETED_PAIR_CAYLEY_UNIT_ENERGY_IFF_GRH :
    GeneralizedCompletedPairCayleyUnitEnergyPreservation ↔
      GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).1
      ((PRIMITIVE_COMPLETED_PAIR_CAYLEY_UNIT_ENERGY_IFF_PAIR_RH χ).1 (h N χ hχ))
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_CAYLEY_UNIT_ENERGY_IFF_PAIR_RH χ).2
      ((PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).2 (h N χ hχ))

/-- Collected strong completed-Dirichlet GRH atlas.  This includes the actual
completed-L zero bridge, the genuine primitive functional-equation pair, and
the three family-level Cayley formulations. -/
theorem COMPLETED_PAIR_GRH_A_TIER_CLOSURE_ATLAS :
    (CompletedGeneralizedRiemannHypothesis ↔ GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairRiemannHypothesis ↔ GeneralizedRiemannHypothesis) ∧
    (GeneralizedCenteredCompletedPairRiemannHypothesis ↔ GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairCayleyZeroLoss ↔ GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairCayleySaturation ↔ GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairCayleyUnitEnergyPreservation ↔
      GeneralizedRiemannHypothesis) ∧
    (GeneralizedRiemannHypothesis → _root_.RiemannHypothesis) := by
  exact ⟨COMPLETED_GRH_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_RH_IFF_GRH,
    GENERALIZED_CENTERED_COMPLETED_PAIR_RH_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_CAYLEY_ZERO_LOSS_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_CAYLEY_SATURATION_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_CAYLEY_UNIT_ENERGY_IFF_GRH,
    GRH_IMPLIES_MATHLIB_RH⟩

end CayleyGRHStrong
