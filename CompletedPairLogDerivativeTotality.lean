import CompletedPairSquareSlitGeometry

namespace CayleyGRHStrong

/-- The genuine logarithmic derivative of the completed-pair slit theta,
made partial exactly at theta zeros.  Unlike the older external Cayley loss,
this object is built directly from the analytic completed-L theta. -/
noncomputable def completedPairSlitThetaLogDerivative
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (z : ℂ) : Option ℂ :=
  if hzero : completedPairSlitTheta χ z = 0 then
    none
  else
    some (completedPairSlitThetaPrime χ z / completedPairSlitTheta χ z)

/-- The analytic logarithmic derivative is undefined exactly at a literal zero
of the completed-pair slit theta. -/
theorem COMPLETED_PAIR_SLIT_THETA_LOG_DERIVATIVE_NONE_IFF_ZERO
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (z : ℂ) :
    completedPairSlitThetaLogDerivative χ z = none ↔
      completedPairSlitTheta χ z = 0 := by
  by_cases hzero : completedPairSlitTheta χ z = 0
  · simp [completedPairSlitThetaLogDerivative, hzero]
  · simp [completedPairSlitThetaLogDerivative, hzero]

/-- Totality of the actual logarithmic derivative on the squared critical-strip
part of the principal slit plane. -/
def CompletedPairSlitThetaCriticalLogDerivativeTotal
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ z : ℂ, z ∈ completedPairCriticalSquareDomain → z ∈ Complex.slitPlane →
    completedPairSlitThetaLogDerivative χ z ≠ none

/-- On each character, totality of the genuine logarithmic derivative is
exactly zero-freeness of the genuine completed-pair theta on the same domain. -/
theorem COMPLETED_PAIR_SLIT_THETA_CRITICAL_LOG_DERIVATIVE_TOTAL_IFF_ZERO_FREE
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    CompletedPairSlitThetaCriticalLogDerivativeTotal χ ↔
      CompletedPairSlitThetaCriticalZeroFree χ := by
  constructor
  · intro htotal z hzdom hzslit hzero
    exact (htotal z hzdom hzslit)
      ((COMPLETED_PAIR_SLIT_THETA_LOG_DERIVATIVE_NONE_IFF_ZERO χ z).2 hzero)
  · intro hfree z hzdom hzslit hnone
    exact (hfree z hzdom hzslit)
      ((COMPLETED_PAIR_SLIT_THETA_LOG_DERIVATIVE_NONE_IFF_ZERO χ z).1 hnone)

/-- Family-level totality of the genuine completed-pair logarithmic derivative. -/
def GeneralizedCompletedPairSlitThetaCriticalLogDerivativeTotal : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → CompletedPairSlitThetaCriticalLogDerivativeTotal χ

/-- GRH is exactly totality of the actual completed-pair logarithmic derivative
on the squared critical-strip slit domain.  This is an object-level analytic
reformulation, not an external real-part detector. -/
theorem GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_LOG_DERIVATIVE_TOTAL_IFF_GRH :
    GeneralizedCompletedPairSlitThetaCriticalLogDerivativeTotal ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis := by
  constructor
  · intro htotal
    apply GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH.mp
    intro N _ χ hχ
    exact (COMPLETED_PAIR_SLIT_THETA_CRITICAL_LOG_DERIVATIVE_TOTAL_IFF_ZERO_FREE χ).1
      (htotal N χ hχ)
  · intro hGRH N _ χ hχ
    have hfreeFamily : GeneralizedCompletedPairSlitThetaCriticalZeroFree :=
      GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH.mpr hGRH
    exact (COMPLETED_PAIR_SLIT_THETA_CRITICAL_LOG_DERIVATIVE_TOTAL_IFF_ZERO_FREE χ).2
      (hfreeFamily N χ hχ)

/-- Direct denominator characterization for the genuine two-point completed-pair
Cayley observable.  No primitivity and no GRH statement is used here. -/
theorem COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_NONE_IFF_THETA_ZERO
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (a r : ℝ) :
    completedPairActualCayleyObservable χ a r = none ↔
      completedPairSlitTheta χ (CayleyGolPhi.cayleyPointPlus a r) = 0 ∨
      completedPairSlitTheta χ (CayleyGolPhi.cayleyPointMinus a r) = 0 := by
  by_cases hp : completedPairSlitTheta χ (CayleyGolPhi.cayleyPointPlus a r) = 0
  · simp [completedPairActualCayleyObservable, hp]
  · by_cases hm : completedPairSlitTheta χ (CayleyGolPhi.cayleyPointMinus a r) = 0
    · simp [completedPairActualCayleyObservable, hp, hm]
    · simp [completedPairActualCayleyObservable, hp, hm]

/-- A Cayley sample is critical-domain admissible when both literal sample
points lie in the squared centered critical strip and in the principal slit plane. -/
def CompletedPairCriticalCayleySample (a r : ℝ) : Prop :=
  CayleyGolPhi.cayleyPointPlus a r ∈ completedPairCriticalSquareDomain ∧
  CayleyGolPhi.cayleyPointPlus a r ∈ Complex.slitPlane ∧
  CayleyGolPhi.cayleyPointMinus a r ∈ completedPairCriticalSquareDomain ∧
  CayleyGolPhi.cayleyPointMinus a r ∈ Complex.slitPlane

/-- Zero-freeness of the actual theta makes the genuine two-point Cayley
observable defined at every admissible critical sample. -/
theorem COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_DEFINED_OF_CRITICAL_ZERO_FREE
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hfree : CompletedPairSlitThetaCriticalZeroFree χ)
    (a r : ℝ) (hadm : CompletedPairCriticalCayleySample a r) :
    completedPairActualCayleyObservable χ a r ≠ none := by
  intro hnone
  rcases hadm with ⟨hpdom, hpslit, hmdom, hmslit⟩
  rcases (COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_NONE_IFF_THETA_ZERO χ a r).1 hnone with hp | hm
  · exact (hfree _ hpdom hpslit) hp
  · exact (hfree _ hmdom hmslit) hm

/-- Totality of the genuine two-point Cayley observable on admissible critical
samples for one character. -/
def CompletedPairActualCayleyObservableCriticalTotal
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ a r : ℝ, CompletedPairCriticalCayleySample a r →
    completedPairActualCayleyObservable χ a r ≠ none

/-- Actual theta zero-freeness implies totality of the actual two-point Cayley
observable on all admissible critical samples. -/
theorem COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_OF_ZERO_FREE
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N)
    (hfree : CompletedPairSlitThetaCriticalZeroFree χ) :
    CompletedPairActualCayleyObservableCriticalTotal χ := by
  intro a r hadm
  exact COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_DEFINED_OF_CRITICAL_ZERO_FREE
    χ hfree a r hadm

/-- Family-level totality of the actual two-point Cayley observable on every
admissible critical sample. -/
def GeneralizedCompletedPairActualCayleyObservableCriticalTotal : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → CompletedPairActualCayleyObservableCriticalTotal χ

/-- GRH implies totality of the literal completed-pair Cayley observable on all
admissible critical samples.  The converse is intentionally not claimed here;
it would require a separate coverage theorem for the Cayley parameterization. -/
theorem GRH_IMPLIES_GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL :
    CayleyGRHClosure.GeneralizedRiemannHypothesis →
      GeneralizedCompletedPairActualCayleyObservableCriticalTotal := by
  intro hGRH N _ χ hχ
  have hfreeFamily : GeneralizedCompletedPairSlitThetaCriticalZeroFree :=
    GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH.mpr hGRH
  exact COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_OF_ZERO_FREE
    χ (hfreeFamily N χ hχ)

/-- Collected v0.8 analytic-totality atlas.  The logarithmic-derivative totality
is exactly GRH; the concrete two-point Cayley observable totality follows on
its explicitly admissible critical sample domain. -/
theorem COMPLETED_PAIR_GRH_LOG_DERIVATIVE_A_TIER_ATLAS :
    (GeneralizedCompletedPairSlitThetaCriticalZeroFree ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairSlitThetaCriticalLogDerivativeTotal ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (CayleyGRHClosure.GeneralizedRiemannHypothesis →
      GeneralizedCompletedPairActualCayleyObservableCriticalTotal) ∧
    (CayleyGRHClosure.GeneralizedRiemannHypothesis → _root_.RiemannHypothesis) := by
  exact ⟨GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_LOG_DERIVATIVE_TOTAL_IFF_GRH,
    GRH_IMPLIES_GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL,
    CayleyGRHClosure.GRH_IMPLIES_MATHLIB_RH⟩

end CayleyGRHStrong
