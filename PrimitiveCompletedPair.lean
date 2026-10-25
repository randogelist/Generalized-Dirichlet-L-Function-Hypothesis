import CompletedDirichletBridge

namespace CayleyGRHStrong

open CayleyGRHClosure

/-- Primitive characters remain primitive under inversion. -/
theorem primitive_inv
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  change DirichletCharacter.conductor χ⁻¹ = N
  rw [DirichletCharacter.conductor_inv]
  change DirichletCharacter.conductor χ = N at hχ
  exact hχ

/-- Mathlib's genuine primitive completed-L functional equation, re-exported
as an explicit project theorem. -/
theorem PRIMITIVE_COMPLETED_LFUNCTION_FUNCTIONAL_EQUATION
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      N ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ s := by
  exact hχ.completedLFunction_one_sub s

/-- Exact zero reflection from the genuine primitive functional equation.
No nonvanishing claim for the root number is needed: the reverse implication
is obtained by applying the functional equation to the inverse character. -/
theorem PRIMITIVE_COMPLETED_ZERO_REFLECTION_IFF
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) = 0 ↔
      DirichletCharacter.completedLFunction χ⁻¹ s = 0 := by
  constructor
  · intro h
    have hfe := (primitive_inv hχ).completedLFunction_one_sub (1 - s)
    simpa [h] using hfe
  · intro h
    have hfe := hχ.completedLFunction_one_sub s
    simpa [h] using hfe

/-- Equivalent reflected-zero orientation. -/
theorem PRIMITIVE_COMPLETED_ZERO_AT_S_IFF_INVERSE_AT_ONE_SUB
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ s = 0 ↔
      DirichletCharacter.completedLFunction χ⁻¹ (1 - s) = 0 := by
  simpa using PRIMITIVE_COMPLETED_ZERO_REFLECTION_IFF hχ (1 - s)

/-- The completed nontrivial zero set is carried to the inverse character by
reflection across `s ↦ 1 - s`. -/
theorem PRIMITIVE_COMPLETED_NONTRIVIAL_ZERO_REFLECT
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : CompletedDirichletNontrivialZero χ s) :
    CompletedDirichletNontrivialZero χ⁻¹ (1 - s) := by
  rcases hs with ⟨hz, h0, h1⟩
  refine ⟨(PRIMITIVE_COMPLETED_ZERO_AT_S_IFF_INVERSE_AT_ONE_SUB hχ s).1 hz, ?_, ?_⟩
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
  · simp only [Complex.sub_re, Complex.one_re]
    linarith

/-- Exact reflection equivalence of completed nontrivial zero predicates. -/
theorem PRIMITIVE_COMPLETED_NONTRIVIAL_ZERO_REFLECTION_IFF
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    CompletedDirichletNontrivialZero χ s ↔
      CompletedDirichletNontrivialZero χ⁻¹ (1 - s) := by
  constructor
  · exact PRIMITIVE_COMPLETED_NONTRIVIAL_ZERO_REFLECT hχ
  · intro hs
    have hback := PRIMITIVE_COMPLETED_NONTRIVIAL_ZERO_REFLECT (primitive_inv hχ) hs
    simpa using hback

/-- The completed inverse-pair object suggested by the primitive functional equation. -/
noncomputable def completedDirichletPair
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  DirichletCharacter.completedLFunction χ s *
    DirichletCharacter.completedLFunction χ⁻¹ s

/-- The completed inverse-pair is invariant under replacing a character by its inverse. -/
theorem COMPLETED_DIRICHLET_PAIR_INV
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    completedDirichletPair χ⁻¹ s = completedDirichletPair χ s := by
  simp [completedDirichletPair, mul_comm]

/-- The explicit scalar factor in the primitive completed-pair functional equation. -/
noncomputable def completedDirichletPairFunctionalFactor
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
    ((N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ⁻¹)

/-- Object-level functional equation for the actual completed inverse-pair.
This is obtained by multiplying Mathlib's primitive functional equations for
`χ` and `χ⁻¹`. -/
theorem PRIMITIVE_COMPLETED_DIRICHLET_PAIR_FUNCTIONAL_EQUATION
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    completedDirichletPair χ (1 - s) =
      completedDirichletPairFunctionalFactor χ s * completedDirichletPair χ s := by
  unfold completedDirichletPair completedDirichletPairFunctionalFactor
  rw [hχ.completedLFunction_one_sub s,
    (primitive_inv hχ).completedLFunction_one_sub s]
  simp only [inv_inv]
  ring

/-- The pair vanishes exactly when one of its two completed factors vanishes. -/
theorem COMPLETED_DIRICHLET_PAIR_EQ_ZERO_IFF
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    completedDirichletPair χ s = 0 ↔
      DirichletCharacter.completedLFunction χ s = 0 ∨
      DirichletCharacter.completedLFunction χ⁻¹ s = 0 := by
  simp [completedDirichletPair]

/-- For a primitive character, the completed inverse-pair zero set is exactly
reflection invariant.  This is an object-level consequence of the genuine
Dirichlet functional equation. -/
theorem PRIMITIVE_COMPLETED_DIRICHLET_PAIR_ZERO_REFLECTION_IFF
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    completedDirichletPair χ (1 - s) = 0 ↔
      completedDirichletPair χ s = 0 := by
  rw [COMPLETED_DIRICHLET_PAIR_EQ_ZERO_IFF,
    COMPLETED_DIRICHLET_PAIR_EQ_ZERO_IFF]
  have hA := PRIMITIVE_COMPLETED_ZERO_REFLECTION_IFF hχ s
  have hB := PRIMITIVE_COMPLETED_ZERO_REFLECTION_IFF (primitive_inv hχ) s
  simpa [or_comm] using or_congr hA hB

/-- A nontrivial zero of the actual completed inverse-pair. -/
def PrimitiveCompletedPairNontrivialZero
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : Prop :=
  completedDirichletPair χ s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- RH formulated on the actual completed inverse-pair. -/
def PrimitiveCompletedPairRiemannHypothesis
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, PrimitiveCompletedPairNontrivialZero χ s → s.re = (1 / 2 : ℝ)

/-- For a primitive character, the completed inverse-pair RH statement is
exactly the original per-character Dirichlet RH. -/
theorem PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    PrimitiveCompletedPairRiemannHypothesis χ ↔
      DirichletRiemannHypothesis χ := by
  constructor
  · intro hpair s hs
    have hcomp : DirichletCharacter.completedLFunction χ s = 0 :=
      (LFUNCTION_EQ_ZERO_IFF_COMPLETED_LFUNCTION_EQ_ZERO_OF_RE_POS χ hs.2.1).1 hs.1
    apply hpair s
    refine ⟨?_, hs.2.1, hs.2.2⟩
    simp [completedDirichletPair, hcomp]
  · intro hRH s hs
    rcases hs with ⟨hpair, h0, h1⟩
    rcases (COMPLETED_DIRICHLET_PAIR_EQ_ZERO_IFF χ s).1 hpair with hz | hz
    · have hL : DirichletCharacter.LFunction χ s = 0 :=
        (LFUNCTION_EQ_ZERO_IFF_COMPLETED_LFUNCTION_EQ_ZERO_OF_RE_POS χ h0).2 hz
      exact hRH s ⟨hL, h0, h1⟩
    · have href : DirichletCharacter.completedLFunction χ (1 - s) = 0 :=
        (PRIMITIVE_COMPLETED_ZERO_REFLECTION_IFF hχ s).2 hz
      have href0 : 0 < (1 - s).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have href1 : (1 - s).re < 1 := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      have hLref : DirichletCharacter.LFunction χ (1 - s) = 0 :=
        (LFUNCTION_EQ_ZERO_IFF_COMPLETED_LFUNCTION_EQ_ZERO_OF_RE_POS χ href0).2 href
      have hline := hRH (1 - s) ⟨hLref, href0, href1⟩
      simp only [Complex.sub_re, Complex.one_re] at hline
      linarith

/-- Family-level RH for the actual completed primitive inverse-pairs. -/
def GeneralizedCompletedPairRiemannHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → PrimitiveCompletedPairRiemannHypothesis χ

/-- The completed inverse-pair family statement is exactly GRH. -/
theorem GENERALIZED_COMPLETED_PAIR_RH_IFF_GRH :
    GeneralizedCompletedPairRiemannHypothesis ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).1 (h N χ hχ)
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).2 (h N χ hχ)

end CayleyGRHStrong
