import CayleyGRHClosure

namespace CayleyGRHStrong

open CayleyGRHClosure

/-- In the open right half-plane, the archimedean factor of a Dirichlet
L-function is nonzero.  This is the key analytic fact needed to transport
zeros between Mathlib's `LFunction` and `completedLFunction`. -/
theorem gammaFactor_ne_zero_of_re_pos
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hχ.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith

/-- In the open right half-plane, Mathlib's ordinary and completed Dirichlet
L-functions have exactly the same zeros. -/
theorem LFUNCTION_EQ_ZERO_IFF_COMPLETED_LFUNCTION_EQ_ZERO_OF_RE_POS
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = 0 ↔
      DirichletCharacter.completedLFunction χ s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simpa using hs
  have hΓ : DirichletCharacter.gammaFactor χ s ≠ 0 :=
    gammaFactor_ne_zero_of_re_pos χ hs
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)]
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right hΓ
  · intro h
    simp [h]

/-- A nontrivial zero expressed directly with Mathlib's completed Dirichlet
L-function. -/
def CompletedDirichletNontrivialZero
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : Prop :=
  DirichletCharacter.completedLFunction χ s = 0 ∧
    0 < s.re ∧
    s.re < 1

/-- In the critical strip, the literal L-zero predicate and the literal
completed-L zero predicate coincide pointwise. -/
theorem DIRICHLET_NONTRIVIAL_ZERO_IFF_COMPLETED_DIRICHLET_NONTRIVIAL_ZERO
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    DirichletNontrivialZero χ s ↔ CompletedDirichletNontrivialZero χ s := by
  constructor
  · rintro ⟨hz, h0, h1⟩
    exact ⟨(LFUNCTION_EQ_ZERO_IFF_COMPLETED_LFUNCTION_EQ_ZERO_OF_RE_POS χ h0).1 hz,
      h0, h1⟩
  · rintro ⟨hz, h0, h1⟩
    exact ⟨(LFUNCTION_EQ_ZERO_IFF_COMPLETED_LFUNCTION_EQ_ZERO_OF_RE_POS χ h0).2 hz,
      h0, h1⟩

/-- The critical-line statement for the actual completed Dirichlet L-function. -/
def CompletedDirichletRiemannHypothesis
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, CompletedDirichletNontrivialZero χ s → s.re = (1 / 2 : ℝ)

/-- Completion does not change the Dirichlet RH statement. -/
theorem COMPLETED_DIRICHLET_RH_IFF_DIRICHLET_RH
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    CompletedDirichletRiemannHypothesis χ ↔
      DirichletRiemannHypothesis χ := by
  constructor
  · intro h s hs
    exact h s
      ((DIRICHLET_NONTRIVIAL_ZERO_IFF_COMPLETED_DIRICHLET_NONTRIVIAL_ZERO χ s).1 hs)
  · intro h s hs
    exact h s
      ((DIRICHLET_NONTRIVIAL_ZERO_IFF_COMPLETED_DIRICHLET_NONTRIVIAL_ZERO χ s).2 hs)

/-- GRH stated directly for the actual completed primitive Dirichlet L-functions. -/
def CompletedGeneralizedRiemannHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → CompletedDirichletRiemannHypothesis χ

/-- The completed-L formulation is exactly the existing Dirichlet GRH. -/
theorem COMPLETED_GRH_IFF_GRH :
    CompletedGeneralizedRiemannHypothesis ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (COMPLETED_DIRICHLET_RH_IFF_DIRICHLET_RH χ).1 (h N χ hχ)
  · intro h N _ χ hχ
    exact (COMPLETED_DIRICHLET_RH_IFF_DIRICHLET_RH χ).2 (h N χ hχ)

/-- Cayley zero loss tested on zeros of the actual completed Dirichlet L-function. -/
def CompletedDirichletCayleyZeroLoss
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, CompletedDirichletNontrivialZero χ s →
    CayleyRHAClosure.spectralCayleyLoss s = 0

/-- The completed-L Cayley criterion is exactly completed Dirichlet RH. -/
theorem COMPLETED_DIRICHLET_CAYLEY_ZERO_LOSS_IFF_COMPLETED_RH
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    CompletedDirichletCayleyZeroLoss χ ↔
      CompletedDirichletRiemannHypothesis χ := by
  change CayleyZeroLossFor (CompletedDirichletNontrivialZero χ) ↔
    CriticalLineZeroHypothesis (CompletedDirichletNontrivialZero χ)
  exact CAYLEY_ZERO_LOSS_FOR_IFF_CRITICAL_LINE_ZERO_HYPOTHESIS
    (CompletedDirichletNontrivialZero χ)

/-- Family-level Cayley zero loss over actual completed primitive Dirichlet L-functions. -/
def GeneralizedCompletedDirichletCayleyZeroLoss : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → CompletedDirichletCayleyZeroLoss χ

/-- First strong GRH bridge: completed-L Cayley zero loss is exactly GRH. -/
theorem GENERALIZED_COMPLETED_DIRICHLET_CAYLEY_ZERO_LOSS_IFF_GRH :
    GeneralizedCompletedDirichletCayleyZeroLoss ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (COMPLETED_DIRICHLET_RH_IFF_DIRICHLET_RH χ).1
      ((COMPLETED_DIRICHLET_CAYLEY_ZERO_LOSS_IFF_COMPLETED_RH χ).1 (h N χ hχ))
  · intro h N _ χ hχ
    exact (COMPLETED_DIRICHLET_CAYLEY_ZERO_LOSS_IFF_COMPLETED_RH χ).2
      ((COMPLETED_DIRICHLET_RH_IFF_DIRICHLET_RH χ).2 (h N χ hχ))

end CayleyGRHStrong
