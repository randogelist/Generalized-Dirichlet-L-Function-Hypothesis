import CompletedPairLogDerivativeTotality

namespace CayleyGRHStrong

/-- The two literal Cayley sample points are complex conjugates. -/
theorem CAYLEY_POINT_MINUS_EQ_CONJ_PLUS (a r : ℝ) :
    CayleyGolPhi.cayleyPointMinus a r =
      (starRingEnd ℂ) (CayleyGolPhi.cayleyPointPlus a r) := by
  apply Complex.ext
  · simp [CayleyGolPhi.cayleyPointMinus, CayleyGolPhi.cayleyPointPlus]
  · simp [CayleyGolPhi.cayleyPointMinus, CayleyGolPhi.cayleyPointPlus]

/-- Symmetric form of the conjugate-pair identity. -/
theorem CAYLEY_POINT_PLUS_EQ_CONJ_MINUS (a r : ℝ) :
    CayleyGolPhi.cayleyPointPlus a r =
      (starRingEnd ℂ) (CayleyGolPhi.cayleyPointMinus a r) := by
  apply Complex.ext
  · simp [CayleyGolPhi.cayleyPointMinus, CayleyGolPhi.cayleyPointPlus]
  · simp [CayleyGolPhi.cayleyPointMinus, CayleyGolPhi.cayleyPointPlus]

/-- The principal slit plane is invariant under complex conjugation. -/
theorem CONJ_MEM_SLIT_PLANE_IFF (z : ℂ) :
    (starRingEnd ℂ) z ∈ Complex.slitPlane ↔ z ∈ Complex.slitPlane := by
  simp [Complex.mem_slitPlane_iff]

/-- The squared centered critical-strip domain is invariant under conjugation. -/
theorem CONJ_MEM_COMPLETED_PAIR_CRITICAL_SQUARE_DOMAIN
    {z : ℂ} (hz : z ∈ completedPairCriticalSquareDomain) :
    (starRingEnd ℂ) z ∈ completedPairCriticalSquareDomain := by
  rcases hz with ⟨w, hw, rfl⟩
  refine ⟨(starRingEnd ℂ) w, ?_, ?_⟩
  · simpa [CenteredCriticalStripPoint] using hw
  · simp

/-- Algebraic coverage of a non-critical-line square by the literal Cayley
pair.  For `w.re ≠ 0`, choose radius `a = re(w)^2 + im(w)^2` and
`r = im(w)^2 / a`; one of the upper/lower Cayley points is exactly `w^2`.
This is the real geometry behind the old `(a,r)` parametrization. -/
theorem CAYLEY_PAIR_COVERS_SQUARE_OF_RE_NE_ZERO
    (w : ℂ) (hwre : w.re ≠ 0) :
    ∃ a r : ℝ,
      CayleyGolPhi.cayleyPointPlus a r = w ^ 2 ∨
      CayleyGolPhi.cayleyPointMinus a r = w ^ 2 := by
  let a : ℝ := w.re ^ 2 + w.im ^ 2
  have ha_pos : 0 < a := by
    dsimp [a]
    nlinarith [sq_pos_of_ne_zero hwre, sq_nonneg w.im]
  have ha : a ≠ 0 := ne_of_gt ha_pos
  let r : ℝ := w.im ^ 2 / a
  have har : a * r = w.im ^ 2 := by
    dsimp [r]
    field_simp [ha]
  have haone : a * (1 - r) = w.re ^ 2 := by
    calc
      a * (1 - r) = a - a * r := by ring
      _ = a - w.im ^ 2 := by rw [har]
      _ = w.re ^ 2 := by dsimp [a]; ring
  have hreal : a * (1 - 2 * r) = w.re ^ 2 - w.im ^ 2 := by
    calc
      a * (1 - 2 * r) = a - 2 * (a * r) := by ring
      _ = a - 2 * w.im ^ 2 := by rw [har]
      _ = w.re ^ 2 - w.im ^ 2 := by dsimp [a]; ring
  have himag :
      CayleyGolPhi.cayleyImagMagnitude a r = 2 * |w.re * w.im| := by
    unfold CayleyGolPhi.cayleyImagMagnitude
    rw [har, haone]
    have hsquare : w.im ^ 2 * w.re ^ 2 = (w.re * w.im) ^ 2 := by ring
    rw [hsquare, Real.sqrt_sq_eq_abs]
  by_cases hsign : 0 ≤ w.re * w.im
  · refine ⟨a, r, Or.inl ?_⟩
    apply Complex.ext
    · change a * (1 - 2 * r) = (w ^ 2).re
      rw [hreal]
      simp only [pow_two, Complex.mul_re]
    · change CayleyGolPhi.cayleyImagMagnitude a r = (w ^ 2).im
      rw [himag, abs_of_nonneg hsign]
      simp only [pow_two, Complex.mul_im]
      ring
  · have hsign' : w.re * w.im ≤ 0 := le_of_not_ge hsign
    refine ⟨a, r, Or.inr ?_⟩
    apply Complex.ext
    · change a * (1 - 2 * r) = (w ^ 2).re
      rw [hreal]
      simp only [pow_two, Complex.mul_re]
    · change -CayleyGolPhi.cayleyImagMagnitude a r = (w ^ 2).im
      rw [himag, abs_of_nonpos hsign']
      simp only [pow_two, Complex.mul_im]
      ring

/-- Every point of the actual squared critical-strip slit domain occurs as one
member of an admissible literal Cayley conjugate pair.  This is the missing
coverage theorem needed to turn two-point observable totality into an exact
GRH equivalence. -/
theorem COMPLETED_PAIR_CRITICAL_CAYLEY_PARAMETER_COVERAGE
    {z : ℂ}
    (hzdom : z ∈ completedPairCriticalSquareDomain)
    (hzslit : z ∈ Complex.slitPlane) :
    ∃ a r : ℝ,
      CompletedPairCriticalCayleySample a r ∧
      (CayleyGolPhi.cayleyPointPlus a r = z ∨
       CayleyGolPhi.cayleyPointMinus a r = z) := by
  rcases hzdom with ⟨w, hwstrip, rfl⟩
  have hdom : w ^ 2 ∈ completedPairCriticalSquareDomain :=
    ⟨w, hwstrip, rfl⟩
  have hwre : w.re ≠ 0 :=
    (SQUARE_MEM_SLIT_PLANE_IFF_RE_NE_ZERO w).1 hzslit
  rcases CAYLEY_PAIR_COVERS_SQUARE_OF_RE_NE_ZERO w hwre with
    ⟨a, r, hplus | hminus⟩
  · have hconjDom : (starRingEnd ℂ) (w ^ 2) ∈ completedPairCriticalSquareDomain :=
      CONJ_MEM_COMPLETED_PAIR_CRITICAL_SQUARE_DOMAIN hdom
    have hconjSlit : (starRingEnd ℂ) (w ^ 2) ∈ Complex.slitPlane :=
      (CONJ_MEM_SLIT_PLANE_IFF (w ^ 2)).2 hzslit
    have hminusConj :
        CayleyGolPhi.cayleyPointMinus a r = (starRingEnd ℂ) (w ^ 2) := by
      rw [CAYLEY_POINT_MINUS_EQ_CONJ_PLUS, hplus]
    refine ⟨a, r, ?_, Or.inl hplus⟩
    exact ⟨by simpa [hplus] using hdom,
      by simpa [hplus] using hzslit,
      by simpa [hminusConj] using hconjDom,
      by simpa [hminusConj] using hconjSlit⟩
  · have hconjDom : (starRingEnd ℂ) (w ^ 2) ∈ completedPairCriticalSquareDomain :=
      CONJ_MEM_COMPLETED_PAIR_CRITICAL_SQUARE_DOMAIN hdom
    have hconjSlit : (starRingEnd ℂ) (w ^ 2) ∈ Complex.slitPlane :=
      (CONJ_MEM_SLIT_PLANE_IFF (w ^ 2)).2 hzslit
    have hplusConj :
        CayleyGolPhi.cayleyPointPlus a r = (starRingEnd ℂ) (w ^ 2) := by
      rw [CAYLEY_POINT_PLUS_EQ_CONJ_MINUS, hminus]
    refine ⟨a, r, ?_, Or.inr hminus⟩
    exact ⟨by simpa [hplusConj] using hconjDom,
      by simpa [hplusConj] using hconjSlit,
      by simpa [hminus] using hdom,
      by simpa [hminus] using hzslit⟩

/-- The concrete two-point completed-pair Cayley observable is total on all
admissible critical samples iff the actual slit-theta is zero-free on the full
critical square/slit domain.  The reverse implication uses the coverage theorem
above and is the new content beyond v0.8. -/
theorem COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_ZERO_FREE
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    CompletedPairActualCayleyObservableCriticalTotal χ ↔
      CompletedPairSlitThetaCriticalZeroFree χ := by
  constructor
  · intro htotal z hzdom hzslit hzero
    rcases COMPLETED_PAIR_CRITICAL_CAYLEY_PARAMETER_COVERAGE hzdom hzslit with
      ⟨a, r, hadm, hplus | hminus⟩
    · have hnone : completedPairActualCayleyObservable χ a r = none :=
        (COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_NONE_IFF_THETA_ZERO χ a r).2
          (Or.inl (by simpa [hplus] using hzero))
      exact (htotal a r hadm) hnone
    · have hnone : completedPairActualCayleyObservable χ a r = none :=
        (COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_NONE_IFF_THETA_ZERO χ a r).2
          (Or.inr (by simpa [hminus] using hzero))
      exact (htotal a r hadm) hnone
  · exact COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_OF_ZERO_FREE χ

/-- Full family equivalence: totality of the literal two-point completed-pair
Cayley observable on its admissible critical samples is exactly GRH. -/
theorem GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH :
    GeneralizedCompletedPairActualCayleyObservableCriticalTotal ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis := by
  constructor
  · intro htotal
    apply GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH.mp
    intro N _ χ hχ
    exact (COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_ZERO_FREE χ).1
      (htotal N χ hχ)
  · exact GRH_IMPLIES_GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL

/-- v0.9 atlas: every major actual completed-L analytic formulation, including
literal two-point Cayley observable totality, is now exactly equivalent to GRH. -/
theorem COMPLETED_PAIR_GRH_CAYLEY_COVERAGE_A_TIER_ATLAS :
    (GeneralizedCompletedPairSlitThetaCriticalZeroFree ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairSlitThetaCriticalLogDerivativeTotal ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairActualCayleyObservableCriticalTotal ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (CayleyGRHClosure.GeneralizedRiemannHypothesis → _root_.RiemannHypothesis) := by
  exact ⟨GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_LOG_DERIVATIVE_TOTAL_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH,
    CayleyGRHClosure.GRH_IMPLIES_MATHLIB_RH⟩

end CayleyGRHStrong
