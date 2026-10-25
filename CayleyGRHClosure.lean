import CayleyRHClosure
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace CayleyGRHClosure

/-- Critical-line localization for an arbitrary complex zero predicate. -/
def CriticalLineZeroHypothesis (Zero : ℂ → Prop) : Prop :=
  ∀ s : ℂ, Zero s → s.re = (1 / 2 : ℝ)

/-- Global Cayley zero loss for an arbitrary complex zero predicate. -/
def CayleyZeroLossFor (Zero : ℂ → Prop) : Prop :=
  ∀ s : ℂ, Zero s → CayleyRHAClosure.spectralCayleyLoss s = 0

/-- Global Cayley contraction saturation for an arbitrary zero predicate. -/
def CayleySaturationFor (Zero : ℂ → Prop) : Prop :=
  ∀ s : ℂ, Zero s → CayleyRHAClosure.spectralCayleyTransmission s = 1

/-- Global unit-state Cayley energy preservation for an arbitrary zero predicate. -/
def CayleyUnitEnergyPreservationFor (Zero : ℂ → Prop) : Prop :=
  ∀ s : ℂ, Zero s →
    GPBKQRKernel.scalarEnergy (GPBKQRKernel.cayleyStep s.re 1) =
      GPBKQRKernel.scalarEnergy 1

/-- Universal zero-set closure: Cayley zero loss is exactly critical-line localization. -/
theorem CAYLEY_ZERO_LOSS_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (Zero : ℂ → Prop) :
    CayleyZeroLossFor Zero ↔ CriticalLineZeroHypothesis Zero := by
  constructor
  · intro h s hs
    exact (CayleyRHAClosure.spectralCayleyLoss_eq_zero_iff_criticalLine s).1
      (h s hs)
  · intro h s hs
    exact (CayleyRHAClosure.spectralCayleyLoss_eq_zero_iff_criticalLine s).2
      (h s hs)

/-- Universal zero-set closure in Cayley saturation form. -/
theorem CAYLEY_SATURATION_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (Zero : ℂ → Prop) :
    CayleySaturationFor Zero ↔ CriticalLineZeroHypothesis Zero := by
  constructor
  · intro h s hs
    exact (CayleyRHAClosure.spectralCayleyTransmission_eq_one_iff_criticalLine s).1
      (h s hs)
  · intro h s hs
    exact (CayleyRHAClosure.spectralCayleyTransmission_eq_one_iff_criticalLine s).2
      (h s hs)

/-- Universal zero-set closure in unit-energy-preservation form. -/
theorem CAYLEY_UNIT_ENERGY_PRESERVATION_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (Zero : ℂ → Prop) :
    CayleyUnitEnergyPreservationFor Zero ↔ CriticalLineZeroHypothesis Zero := by
  constructor
  · intro h s hs
    exact (CayleyRHAClosure.spectralCayleyUnitEnergy_preserved_iff_criticalLine s).1
      (h s hs)
  · intro h s hs
    exact (CayleyRHAClosure.spectralCayleyUnitEnergy_preserved_iff_criticalLine s).2
      (h s hs)

/-- Exact zero-predicate equivalence transports Cayley zero-loss closure. -/
theorem ZERO_EQUIV_TRANSPORTS_CAYLEY_ZERO_LOSS
    (Zero₁ Zero₂ : ℂ → Prop)
    (hZero : ∀ s : ℂ, Zero₁ s ↔ Zero₂ s) :
    CayleyZeroLossFor Zero₁ ↔ CayleyZeroLossFor Zero₂ := by
  constructor
  · intro h s hs
    exact h s ((hZero s).2 hs)
  · intro h s hs
    exact h s ((hZero s).1 hs)

/-- A nontrivial zero of the analytically continued Dirichlet L-function. -/
def DirichletNontrivialZero
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (s : ℂ) : Prop :=
  DirichletCharacter.LFunction χ s = 0 ∧
    0 < s.re ∧
    s.re < 1

/-- The Riemann hypothesis for one Dirichlet character. -/
def DirichletRiemannHypothesis
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, DirichletNontrivialZero χ s → s.re = (1 / 2 : ℝ)

/-- Cayley zero loss for all nontrivial zeros of one Dirichlet L-function. -/
def DirichletCayleyZeroLoss
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, DirichletNontrivialZero χ s →
    CayleyRHAClosure.spectralCayleyLoss s = 0

/-- Cayley saturation for all nontrivial zeros of one Dirichlet L-function. -/
def DirichletCayleySaturation
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, DirichletNontrivialZero χ s →
    CayleyRHAClosure.spectralCayleyTransmission s = 1

/-- Unit Cayley energy preservation for all nontrivial zeros of one Dirichlet L-function. -/
def DirichletCayleyUnitEnergyPreservation
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, DirichletNontrivialZero χ s →
    GPBKQRKernel.scalarEnergy (GPBKQRKernel.cayleyStep s.re 1) =
      GPBKQRKernel.scalarEnergy 1

/-- Per-character Cayley zero loss is exactly the per-character RH statement. -/
theorem DIRICHLET_CAYLEY_ZERO_LOSS_IFF_RH
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    DirichletCayleyZeroLoss χ ↔ DirichletRiemannHypothesis χ := by
  change CayleyZeroLossFor (DirichletNontrivialZero χ) ↔
    CriticalLineZeroHypothesis (DirichletNontrivialZero χ)
  exact CAYLEY_ZERO_LOSS_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (DirichletNontrivialZero χ)

/-- Per-character Cayley saturation is exactly the per-character RH statement. -/
theorem DIRICHLET_CAYLEY_SATURATION_IFF_RH
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    DirichletCayleySaturation χ ↔ DirichletRiemannHypothesis χ := by
  change CayleySaturationFor (DirichletNontrivialZero χ) ↔
    CriticalLineZeroHypothesis (DirichletNontrivialZero χ)
  exact CAYLEY_SATURATION_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (DirichletNontrivialZero χ)

/-- Per-character unit energy preservation is exactly the per-character RH statement. -/
theorem DIRICHLET_CAYLEY_UNIT_ENERGY_PRESERVATION_IFF_RH
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    DirichletCayleyUnitEnergyPreservation χ ↔
      DirichletRiemannHypothesis χ := by
  change CayleyUnitEnergyPreservationFor (DirichletNontrivialZero χ) ↔
    CriticalLineZeroHypothesis (DirichletNontrivialZero χ)
  exact CAYLEY_UNIT_ENERGY_PRESERVATION_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (DirichletNontrivialZero χ)

/-- Standard GRH for primitive Dirichlet characters. -/
def GeneralizedRiemannHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → DirichletRiemannHypothesis χ

/-- Family-level Cayley zero loss over all primitive Dirichlet characters. -/
def GeneralizedDirichletCayleyZeroLoss : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → DirichletCayleyZeroLoss χ

/-- Family-level Cayley saturation over all primitive Dirichlet characters. -/
def GeneralizedDirichletCayleySaturation : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → DirichletCayleySaturation χ

/-- Family-level unit Cayley energy preservation over all primitive characters. -/
def GeneralizedDirichletCayleyUnitEnergyPreservation : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → DirichletCayleyUnitEnergyPreservation χ

/-- Main GRH closure: family-level Cayley zero loss is exactly Dirichlet GRH. -/
theorem GENERALIZED_DIRICHLET_CAYLEY_ZERO_LOSS_IFF_GRH :
    GeneralizedDirichletCayleyZeroLoss ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (DIRICHLET_CAYLEY_ZERO_LOSS_IFF_RH χ).1 (h N χ hχ)
  · intro h N _ χ hχ
    exact (DIRICHLET_CAYLEY_ZERO_LOSS_IFF_RH χ).2 (h N χ hχ)

/-- Equivalent GRH closure in Cayley saturation form. -/
theorem GENERALIZED_DIRICHLET_CAYLEY_SATURATION_IFF_GRH :
    GeneralizedDirichletCayleySaturation ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (DIRICHLET_CAYLEY_SATURATION_IFF_RH χ).1 (h N χ hχ)
  · intro h N _ χ hχ
    exact (DIRICHLET_CAYLEY_SATURATION_IFF_RH χ).2 (h N χ hχ)

/-- Equivalent GRH closure in unit-energy-preservation form. -/
theorem GENERALIZED_DIRICHLET_CAYLEY_UNIT_ENERGY_PRESERVATION_IFF_GRH :
    GeneralizedDirichletCayleyUnitEnergyPreservation ↔
      GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (DIRICHLET_CAYLEY_UNIT_ENERGY_PRESERVATION_IFF_RH χ).1
      (h N χ hχ)
  · intro h N _ χ hχ
    exact (DIRICHLET_CAYLEY_UNIT_ENERGY_PRESERVATION_IFF_RH χ).2
      (h N χ hχ)

/-- The modulus-one Dirichlet RH statement is exactly Mathlib's native RH. -/
theorem MOD_ONE_DIRICHLET_RH_IFF_MATHLIB_RH :
    DirichletRiemannHypothesis (1 : DirichletCharacter ℂ 1) ↔
      _root_.RiemannHypothesis := by
  constructor
  · intro hD
    unfold _root_.RiemannHypothesis
    intro s hz htriv hs1
    have hs : 0 < s.re ∧ s.re < 1 :=
      CayleyGolPhi.NONTRIVIAL_ZETA_ZERO_MEM_CRITICAL_STRIP
        ⟨hz, htriv, hs1⟩
    apply hD s
    refine ⟨?_, hs.1, hs.2⟩
    simpa using hz
  · intro hRH s hs
    have hstrip : 0 < s.re ∧ s.re < 1 := ⟨hs.2.1, hs.2.2⟩
    have hz : riemannZeta s = 0 := by
      simpa using hs.1
    exact hRH s hz
      (CayleyGolPhi.CRITICAL_STRIP_NOT_TRIVIAL hstrip)
      (CayleyGolPhi.CRITICAL_STRIP_NE_ONE hstrip)

/-- Standard Dirichlet GRH contains classical Mathlib RH as its modulus-one instance. -/
theorem GRH_IMPLIES_MATHLIB_RH :
    GeneralizedRiemannHypothesis → _root_.RiemannHypothesis := by
  intro hGRH
  apply MOD_ONE_DIRICHLET_RH_IFF_MATHLIB_RH.mp
  exact hGRH 1 (1 : DirichletCharacter ℂ 1)
    DirichletCharacter.isPrimitive_one_level_one

/-- Collected A-tier GRH closure atlas. -/
theorem CAYLEY_GRH_A_TIER_CLOSURE_ATLAS :
    (GeneralizedDirichletCayleyZeroLoss ↔ GeneralizedRiemannHypothesis) ∧
    (GeneralizedDirichletCayleySaturation ↔ GeneralizedRiemannHypothesis) ∧
    (GeneralizedDirichletCayleyUnitEnergyPreservation ↔
      GeneralizedRiemannHypothesis) ∧
    (GeneralizedRiemannHypothesis → _root_.RiemannHypothesis) := by
  exact ⟨GENERALIZED_DIRICHLET_CAYLEY_ZERO_LOSS_IFF_GRH,
    GENERALIZED_DIRICHLET_CAYLEY_SATURATION_IFF_GRH,
    GENERALIZED_DIRICHLET_CAYLEY_UNIT_ENERGY_PRESERVATION_IFF_GRH,
    GRH_IMPLIES_MATHLIB_RH⟩

end CayleyGRHClosure
