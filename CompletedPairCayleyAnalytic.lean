import PrimitiveCompletedPair
import Mathlib.Analysis.Complex.SqrtDeriv

namespace CayleyGRHStrong

open CayleyGRHClosure

/-- Reflection symmetrization of the genuine completed primitive inverse-pair.
Unlike the raw pair, this object has literal `s ↦ 1 - s` symmetry without
having to choose a square root of a root number. -/
noncomputable def reflectionSymmetrizedCompletedPair
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  completedDirichletPair χ s * completedDirichletPair χ (1 - s)

/-- Literal reflection symmetry of the symmetrized completed pair. -/
theorem REFLECTION_SYMMETRIZED_COMPLETED_PAIR_ONE_SUB
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    reflectionSymmetrizedCompletedPair χ (1 - s) =
      reflectionSymmetrizedCompletedPair χ s := by
  simp [reflectionSymmetrizedCompletedPair, mul_comm]

/-- For primitive characters, symmetrization introduces no new zeros: the
second factor has exactly the reflected zero set of the first. -/
theorem PRIMITIVE_REFLECTION_SYMMETRIZED_PAIR_ZERO_IFF_PAIR_ZERO
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    reflectionSymmetrizedCompletedPair χ s = 0 ↔
      completedDirichletPair χ s = 0 := by
  unfold reflectionSymmetrizedCompletedPair
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact (PRIMITIVE_COMPLETED_DIRICHLET_PAIR_ZERO_REFLECTION_IFF hχ s).1 h
  · intro h
    exact Or.inl h

/-- Centered reflection-symmetric completed pair. -/
noncomputable def centeredCompletedDirichletPair
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (w : ℂ) : ℂ :=
  reflectionSymmetrizedCompletedPair χ ((1 / 2 : ℂ) + w)

/-- Centering converts reflection symmetry into literal evenness. -/
theorem CENTERED_COMPLETED_DIRICHLET_PAIR_EVEN
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (w : ℂ) :
    centeredCompletedDirichletPair χ (-w) =
      centeredCompletedDirichletPair χ w := by
  unfold centeredCompletedDirichletPair
  have h := REFLECTION_SYMMETRIZED_COMPLETED_PAIR_ONE_SUB χ ((1 / 2 : ℂ) + w)
  convert h using 1 <;> ring

/-- For primitive characters, a zero of the centered even object is exactly a
zero of the genuine completed inverse-pair at the corresponding spectral point. -/
theorem PRIMITIVE_CENTERED_COMPLETED_PAIR_ZERO_IFF_PAIR_ZERO
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (w : ℂ) :
    centeredCompletedDirichletPair χ w = 0 ↔
      completedDirichletPair χ ((1 / 2 : ℂ) + w) = 0 := by
  unfold centeredCompletedDirichletPair
  exact PRIMITIVE_REFLECTION_SYMMETRIZED_PAIR_ZERO_IFF_PAIR_ZERO hχ _

/-- Centered nontrivial zero predicate for the actual reflection-even object. -/
def CenteredCompletedPairNontrivialZero
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (w : ℂ) : Prop :=
  centeredCompletedDirichletPair χ w = 0 ∧
    -(1 / 2 : ℝ) < w.re ∧ w.re < (1 / 2 : ℝ)

/-- RH stated on zeros of the actual centered, reflection-even completed pair. -/
def CenteredCompletedPairRiemannHypothesis
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ w : ℂ, CenteredCompletedPairNontrivialZero χ w → w.re = 0

/-- For primitive characters, the centered-even completed-pair formulation is
exactly the completed-pair RH formulation. -/
theorem PRIMITIVE_CENTERED_COMPLETED_PAIR_RH_IFF_PAIR_RH
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    CenteredCompletedPairRiemannHypothesis χ ↔
      PrimitiveCompletedPairRiemannHypothesis χ := by
  constructor
  · intro hcenter s hs
    let w : ℂ := s - (1 / 2 : ℂ)
    have hwzero : centeredCompletedDirichletPair χ w = 0 := by
      apply (PRIMITIVE_CENTERED_COMPLETED_PAIR_ZERO_IFF_PAIR_ZERO hχ w).2
      convert hs.1 using 1 <;> dsimp [w] <;> ring
    have hw0 : -(1 / 2 : ℝ) < w.re := by
      dsimp [w]
      norm_num [Complex.sub_re]
      linarith [hs.2.1]
    have hw1 : w.re < (1 / 2 : ℝ) := by
      dsimp [w]
      norm_num [Complex.sub_re]
      linarith [hs.2.2]
    have hwline := hcenter w ⟨hwzero, hw0, hw1⟩
    dsimp [w] at hwline
    norm_num [Complex.sub_re] at hwline
    linarith
  · intro hpair w hw
    have hpzero : completedDirichletPair χ ((1 / 2 : ℂ) + w) = 0 :=
      (PRIMITIVE_CENTERED_COMPLETED_PAIR_ZERO_IFF_PAIR_ZERO hχ w).1 hw.1
    have hs0 : 0 < ((1 / 2 : ℂ) + w).re := by
      norm_num [Complex.add_re]
      linarith [hw.2.1]
    have hs1 : ((1 / 2 : ℂ) + w).re < 1 := by
      norm_num [Complex.add_re]
      linarith [hw.2.2]
    have hline := hpair ((1 / 2 : ℂ) + w) ⟨hpzero, hs0, hs1⟩
    norm_num [Complex.add_re] at hline
    linarith

/-- Family-level centered-even completed-pair statement. -/
def GeneralizedCenteredCompletedPairRiemannHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → CenteredCompletedPairRiemannHypothesis χ

/-- The actual centered, reflection-even completed-pair family statement is
exactly GRH. -/
theorem GENERALIZED_CENTERED_COMPLETED_PAIR_RH_IFF_GRH :
    GeneralizedCenteredCompletedPairRiemannHypothesis ↔
      GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    exact (PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).1
      ((PRIMITIVE_CENTERED_COMPLETED_PAIR_RH_IFF_PAIR_RH hχ).1 (h N χ hχ))
  · intro h N _ χ hχ
    exact (PRIMITIVE_CENTERED_COMPLETED_PAIR_RH_IFF_PAIR_RH hχ).2
      ((PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).2 (h N χ hχ))

/-- The genuine completed inverse-pair is entire whenever `χ` is nontrivial.
The inverse character is nontrivial for the same reason. -/
theorem COMPLETED_DIRICHLET_PAIR_DIFFERENTIABLE
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) :
    Differentiable ℂ (completedDirichletPair χ) := by
  have hχinv : χ⁻¹ ≠ 1 := by
    intro hi
    apply hχ
    have h := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) hi
    simpa using h
  exact (DirichletCharacter.differentiable_completedLFunction hχ).mul
    (DirichletCharacter.differentiable_completedLFunction hχinv)

/-- The reflection-symmetrized pair is entire for nontrivial `χ`. -/
theorem REFLECTION_SYMMETRIZED_COMPLETED_PAIR_DIFFERENTIABLE
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) :
    Differentiable ℂ (reflectionSymmetrizedCompletedPair χ) := by
  have hP := COMPLETED_DIRICHLET_PAIR_DIFFERENTIABLE (χ := χ) hχ
  intro s
  unfold reflectionSymmetrizedCompletedPair
  exact (hP s).mul ((hP (1 - s)).comp s (by fun_prop))

/-- The centered reflection-even pair is entire for nontrivial `χ`. -/
theorem CENTERED_COMPLETED_DIRICHLET_PAIR_DIFFERENTIABLE
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) :
    Differentiable ℂ (centeredCompletedDirichletPair χ) := by
  have hS := REFLECTION_SYMMETRIZED_COMPLETED_PAIR_DIFFERENTIABLE (χ := χ) hχ
  intro w
  unfold centeredCompletedDirichletPair
  exact (hS ((1 / 2 : ℂ) + w)).comp w (by fun_prop)

/-- Slit-plane theta built from the actual centered completed Dirichlet pair. -/
noncomputable def completedPairSlitTheta
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  centeredCompletedDirichletPair χ (Complex.sqrt z)

/-- The completed-pair theta is analytic on the principal-sqrt slit plane for
nontrivial characters. -/
theorem COMPLETED_PAIR_SLIT_THETA_DIFFERENTIABLE_ON
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (completedPairSlitTheta χ) Complex.slitPlane := by
  have hC := CENTERED_COMPLETED_DIRICHLET_PAIR_DIFFERENTIABLE (χ := χ) hχ
  intro z hz
  unfold completedPairSlitTheta
  exact ((hC (Complex.sqrt z)).comp z
    (Complex.differentiableAt_sqrt hz)).differentiableWithinAt

/-- For primitive characters, theta zeros are literally completed-pair zeros
under the centered-square-root pullback. -/
theorem PRIMITIVE_COMPLETED_PAIR_THETA_ZERO_IFF_PAIR_ZERO
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (z : ℂ) :
    completedPairSlitTheta χ z = 0 ↔
      completedDirichletPair χ
        ((1 / 2 : ℂ) + Complex.sqrt z) = 0 := by
  unfold completedPairSlitTheta
  exact PRIMITIVE_CENTERED_COMPLETED_PAIR_ZERO_IFF_PAIR_ZERO hχ _

/-- Literal derivative used in the completed-pair logarithmic Cayley observable. -/
noncomputable def completedPairSlitThetaPrime
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (z : ℂ) : ℂ :=
  deriv (completedPairSlitTheta χ) z

/-- An actual analytic Cayley observable built from the completed primitive pair.
It is undefined exactly at a denominator zero, as in the ordinary-RH Cayley layer. -/
noncomputable def completedPairActualCayleyObservable
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (a r : ℝ) : Option ℂ :=
  let zp := CayleyGolPhi.cayleyPointPlus a r
  let zm := CayleyGolPhi.cayleyPointMinus a r
  if hzero : completedPairSlitTheta χ zp = 0 ∨ completedPairSlitTheta χ zm = 0 then
    none
  else
    let Rp := completedPairSlitThetaPrime χ zp / completedPairSlitTheta χ zp
    let Rm := completedPairSlitThetaPrime χ zm / completedPairSlitTheta χ zm
    some ((4 * (a : ℂ)) * ((zm * Rm - zp * Rp) / (zm - zp)))

/-- Direct object-level bridge: the completed-pair Cayley observable is
undefined exactly when a sampled Cayley point pulls back to a genuine
completed-pair zero.  No GRH implication is used. -/
theorem PRIMITIVE_COMPLETED_PAIR_CAYLEY_OBSERVABLE_NONE_IFF_PAIR_ZERO
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (a r : ℝ) :
    completedPairActualCayleyObservable χ a r = none ↔
      completedDirichletPair χ
          ((1 / 2 : ℂ) + Complex.sqrt (CayleyGolPhi.cayleyPointPlus a r)) = 0 ∨
      completedDirichletPair χ
          ((1 / 2 : ℂ) + Complex.sqrt (CayleyGolPhi.cayleyPointMinus a r)) = 0 := by
  have hnone :
      completedPairActualCayleyObservable χ a r = none ↔
        completedPairSlitTheta χ (CayleyGolPhi.cayleyPointPlus a r) = 0 ∨
        completedPairSlitTheta χ (CayleyGolPhi.cayleyPointMinus a r) = 0 := by
    by_cases hp : completedPairSlitTheta χ (CayleyGolPhi.cayleyPointPlus a r) = 0
    · simp [completedPairActualCayleyObservable, hp]
    · by_cases hm : completedPairSlitTheta χ (CayleyGolPhi.cayleyPointMinus a r) = 0
      · simp [completedPairActualCayleyObservable, hp, hm]
      · simp [completedPairActualCayleyObservable, hp, hm]
  constructor
  · intro h
    rcases hnone.mp h with hp | hm
    · exact Or.inl <|
        (PRIMITIVE_COMPLETED_PAIR_THETA_ZERO_IFF_PAIR_ZERO hχ _).mp hp
    · exact Or.inr <|
        (PRIMITIVE_COMPLETED_PAIR_THETA_ZERO_IFF_PAIR_ZERO hχ _).mp hm
  · intro h
    apply hnone.mpr
    rcases h with hp | hm
    · exact Or.inl <|
        (PRIMITIVE_COMPLETED_PAIR_THETA_ZERO_IFF_PAIR_ZERO hχ _).mpr hp
    · exact Or.inr <|
        (PRIMITIVE_COMPLETED_PAIR_THETA_ZERO_IFF_PAIR_ZERO hχ _).mpr hm

end CayleyGRHStrong
