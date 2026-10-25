import StrongGRHClosure

namespace CayleyGRHStrong

/-- The principal complex square root really is a square root.  We state this
explicitly because it is the algebraic input needed to descend an even entire
function through `w ↦ w^2`. -/
theorem COMPLEX_SQRT_SQUARE (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  unfold Complex.sqrt
  simpa using
    (Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0))

/-- Every square root of `w^2` differs from `w` by at most sign.  In particular,
the principal square root of `w^2` is `w` or `-w`. -/
theorem COMPLEX_SQRT_SQUARE_EQ_OR_NEG (w : ℂ) :
    Complex.sqrt (w ^ 2) = w ∨ Complex.sqrt (w ^ 2) = -w := by
  have hs : (Complex.sqrt (w ^ 2)) ^ 2 = w ^ 2 := COMPLEX_SQRT_SQUARE (w ^ 2)
  have hprod :
      (Complex.sqrt (w ^ 2) - w) * (Complex.sqrt (w ^ 2) + w) = 0 := by
    calc
      (Complex.sqrt (w ^ 2) - w) * (Complex.sqrt (w ^ 2) + w) =
          (Complex.sqrt (w ^ 2)) ^ 2 - w ^ 2 := by ring
      _ = 0 := by rw [hs]; ring
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · exact Or.inl (sub_eq_zero.mp hminus)
  · right
    rw [eq_neg_iff_add_eq_zero]
    exact hplus

/-- Because the centered completed pair is even, the principal-sqrt theta is a
literal value-level descent through the squaring map.  This identity holds on
all of `ℂ`; no slit-plane or GRH hypothesis is needed. -/
theorem COMPLETED_PAIR_SLIT_THETA_SQUARE
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (w : ℂ) :
    completedPairSlitTheta χ (w ^ 2) = centeredCompletedDirichletPair χ w := by
  unfold completedPairSlitTheta
  rcases COMPLEX_SQRT_SQUARE_EQ_OR_NEG w with hsqrt | hsqrt
  · rw [hsqrt]
  · rw [hsqrt, CENTERED_COMPLETED_DIRICHLET_PAIR_EVEN]

/-- The zero version of the exact square-descent identity. -/
theorem COMPLETED_PAIR_SLIT_THETA_SQUARE_ZERO_IFF
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (w : ℂ) :
    completedPairSlitTheta χ (w ^ 2) = 0 ↔
      centeredCompletedDirichletPair χ w = 0 := by
  rw [COMPLETED_PAIR_SLIT_THETA_SQUARE]

/-- Squaring converts the centered critical line `re w = 0` exactly into the
closed negative real axis, i.e. the complement of Mathlib's principal slit
plane. -/
theorem SQUARE_NOT_MEM_SLIT_PLANE_IFF_RE_EQ_ZERO (w : ℂ) :
    w ^ 2 ∉ Complex.slitPlane ↔ w.re = 0 := by
  constructor
  · intro hnot
    have hre : (w ^ 2).re ≤ 0 := by
      by_contra h
      have hpos : 0 < (w ^ 2).re := lt_of_not_ge h
      exact hnot (Complex.mem_slitPlane_iff.mpr (Or.inl hpos))
    have him : (w ^ 2).im = 0 := by
      by_contra h
      exact hnot (Complex.mem_slitPlane_iff.mpr (Or.inr h))
    simp only [pow_two, Complex.mul_re, Complex.mul_im] at hre him
    by_cases hx : w.re = 0
    · exact hx
    · have hxy : w.re * w.im = 0 := by
        nlinarith [him]
      have hy : w.im = 0 := (mul_eq_zero.mp hxy).resolve_left hx
      rw [hy] at hre
      norm_num at hre
      nlinarith [sq_nonneg w.re]
  · intro hw hz
    rw [Complex.mem_slitPlane_iff] at hz
    rcases hz with hre | him
    · simp only [pow_two, Complex.mul_re] at hre
      rw [hw] at hre
      norm_num at hre
      nlinarith [sq_nonneg w.im]
    · apply him
      simp only [pow_two, Complex.mul_im]
      rw [hw]
      ring

/-- The off-critical-line version: a centered point is off the critical line
exactly when its square lies in the principal slit plane. -/
theorem SQUARE_MEM_SLIT_PLANE_IFF_RE_NE_ZERO (w : ℂ) :
    w ^ 2 ∈ Complex.slitPlane ↔ w.re ≠ 0 := by
  rw [← not_iff_not]
  simpa using SQUARE_NOT_MEM_SLIT_PLANE_IFF_RE_EQ_ZERO w

/-- The centered critical strip used by the completed-pair square coordinate. -/
def CenteredCriticalStripPoint (w : ℂ) : Prop :=
  -(1 / 2 : ℝ) < w.re ∧ w.re < (1 / 2 : ℝ)

/-- The squared image of the centered critical strip. -/
def completedPairCriticalSquareDomain : Set ℂ :=
  {z : ℂ | ∃ w : ℂ, CenteredCriticalStripPoint w ∧ z = w ^ 2}

/-- The actual completed-pair theta is zero-free on the part of the squared
critical strip lying in the principal slit plane.  This is an analytic
zero-free formulation, not the earlier external real-part loss predicate. -/
def CompletedPairSlitThetaCriticalZeroFree
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ z : ℂ, z ∈ completedPairCriticalSquareDomain → z ∈ Complex.slitPlane →
    completedPairSlitTheta χ z ≠ 0

/-- Per character, zero-freeness of the actual slit-theta on the critical
square/slit domain is exactly RH for the centered completed pair. -/
theorem COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_CENTERED_RH
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    CompletedPairSlitThetaCriticalZeroFree χ ↔
      CenteredCompletedPairRiemannHypothesis χ := by
  constructor
  · intro hfree w hw
    by_contra hre
    have hslit : w ^ 2 ∈ Complex.slitPlane :=
      (SQUARE_MEM_SLIT_PLANE_IFF_RE_NE_ZERO w).2 hre
    have hdom : w ^ 2 ∈ completedPairCriticalSquareDomain := by
      exact ⟨w, ⟨hw.2.1, hw.2.2⟩, rfl⟩
    have htheta : completedPairSlitTheta χ (w ^ 2) = 0 :=
      (COMPLETED_PAIR_SLIT_THETA_SQUARE_ZERO_IFF χ w).2 hw.1
    exact (hfree (w ^ 2) hdom hslit) htheta
  · intro hcenter z hzdom hzslit htheta
    rcases hzdom with ⟨w, hwstrip, rfl⟩
    have hwzero : centeredCompletedDirichletPair χ w = 0 :=
      (COMPLETED_PAIR_SLIT_THETA_SQUARE_ZERO_IFF χ w).1 htheta
    have hwline : w.re = 0 := hcenter w ⟨hwzero, hwstrip.1, hwstrip.2⟩
    have hnslit : w ^ 2 ∉ Complex.slitPlane :=
      (SQUARE_NOT_MEM_SLIT_PLANE_IFF_RE_EQ_ZERO w).2 hwline
    exact hnslit hzslit

/-- Family-level zero-freeness of the genuine completed-pair slit-theta. -/
def GeneralizedCompletedPairSlitThetaCriticalZeroFree : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → CompletedPairSlitThetaCriticalZeroFree χ

/-- Strong analytic GRH equivalence: GRH is exactly zero-freeness of the
actual completed-pair slit-theta on the squared critical-strip slit domain. -/
theorem GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH :
    GeneralizedCompletedPairSlitThetaCriticalZeroFree ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hχ
    have hcenter : CenteredCompletedPairRiemannHypothesis χ :=
      (COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_CENTERED_RH χ).1
        (h N χ hχ)
    exact (PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).1
      ((PRIMITIVE_CENTERED_COMPLETED_PAIR_RH_IFF_PAIR_RH hχ).1 hcenter)
  · intro h N _ χ hχ
    have hcenter : CenteredCompletedPairRiemannHypothesis χ :=
      (PRIMITIVE_CENTERED_COMPLETED_PAIR_RH_IFF_PAIR_RH hχ).2
        ((PRIMITIVE_COMPLETED_PAIR_RH_IFF_DIRICHLET_RH hχ).2 (h N χ hχ))
    exact (COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_CENTERED_RH χ).2 hcenter

/-- The old completed-pair A-tier atlas together with the stronger actual
slit-theta zero-free formulation. -/
theorem COMPLETED_PAIR_GRH_SLIT_THETA_A_TIER_ATLAS :
    (CompletedGeneralizedRiemannHypothesis ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairRiemannHypothesis ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCenteredCompletedPairRiemannHypothesis ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairSlitThetaCriticalZeroFree ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairCayleyZeroLoss ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairCayleySaturation ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairCayleyUnitEnergyPreservation ↔
      CayleyGRHClosure.GeneralizedRiemannHypothesis) ∧
    (CayleyGRHClosure.GeneralizedRiemannHypothesis → _root_.RiemannHypothesis) := by
  exact ⟨COMPLETED_GRH_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_RH_IFF_GRH,
    GENERALIZED_CENTERED_COMPLETED_PAIR_RH_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_CAYLEY_ZERO_LOSS_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_CAYLEY_SATURATION_IFF_GRH,
    GENERALIZED_COMPLETED_PAIR_CAYLEY_UNIT_ENERGY_IFF_GRH,
    CayleyGRHClosure.GRH_IMPLIES_MATHLIB_RH⟩

end CayleyGRHStrong
