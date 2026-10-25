import CompletedPairCayleyCoverage
import Mathlib.Analysis.Normed.Ring.Finite

namespace CayleyGRHStrong

open CayleyGRHClosure

/-- The literal textbook Dirichlet-GRH statement: every nontrivial zero of the
L-function of every Dirichlet character (primitive or imprimitive) in the open
critical strip lies on the critical line.  There is no primitivity hypothesis
in this definition. -/
def TextbookGeneralizedRiemannHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    DirichletRiemannHypothesis χ

/-- A complex Dirichlet-character value has norm at most one.  If it is
nonzero then it comes from the finite unit group `(ZMod N)ˣ`, hence has finite
multiplicative order and therefore norm exactly one. -/
theorem DIRICHLET_CHARACTER_NORM_APPLY_LE_ONE
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖χ n‖ ≤ 1 := by
  by_cases hzero : χ n = 0
  · simp [hzero]
  · have hcopZ : IsCoprime (n : ℤ) (N : ℤ) := by
      apply (χ.apply_ne_zero_iff (n : ℤ)).1
      simpa using hzero
    have hcop : n.Coprime N := by
      exact_mod_cast hcopZ
    have hu : IsUnit (n : ZMod N) :=
      (ZMod.isUnit_iff_coprime n N).2 hcop
    rw [χ.toUnitHom_eq_char' hu]
    have hfinDom : IsOfFinOrder hu.unit :=
      isOfFinOrder_of_finite hu.unit
    have hfinUnits : IsOfFinOrder ((MulChar.toUnitHom χ) hu.unit) :=
      (MulChar.toUnitHom χ).isOfFinOrder hfinDom
    have hfinVal : IsOfFinOrder
        ((↑((MulChar.toUnitHom χ) hu.unit)) : ℂ) :=
      (Units.isOfFinOrder_val).2 hfinUnits
    exact le_of_eq hfinVal.norm_eq_one

/-- The finite Euler factors introduced by changing the level of a Dirichlet
character cannot vanish in the open right half-plane.  Their possible zeros
all lie on `Re(s)=0`. -/
theorem DIRICHLET_CHANGE_LEVEL_EULER_FACTOR_NE_ZERO_OF_RE_POS
    {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0 < s.re) :
    1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have hmul : χ p * (p : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnormEq : ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ = 1 := by
    have h := congrArg norm hmul
    simpa using h
  have hχnorm : ‖χ p‖ ≤ 1 :=
    DIRICHLET_CHARACTER_NORM_APPLY_LE_ONE χ p
  have hpowlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hp.one_lt
    · simp only [Complex.neg_re]
      linarith
  have hprodlt : ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ < 1 := by
    calc
      ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right hχnorm (norm_nonneg _)
      _ < 1 := by simpa using hpowlt
  linarith

/-- Hence the entire finite Euler product in Mathlib's `LFunction_changeLevel`
formula is nonzero throughout `Re(s)>0`. -/
theorem DIRICHLET_CHANGE_LEVEL_EULER_PRODUCT_NE_ZERO_OF_RE_POS
    {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 0 < s.re) :
    (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hpMem
  exact DIRICHLET_CHANGE_LEVEL_EULER_FACTOR_NE_ZERO_OF_RE_POS χ
    (Nat.prime_of_mem_primeFactors hpMem) hs

/-- A zero of an arbitrary Dirichlet L-function in the open right half-plane
is already a zero of the L-function of its associated primitive character.
This is the load-bearing primitive-reduction lemma for the textbook GRH
wrapper. -/
theorem LFUNCTION_ZERO_IMPLIES_PRIMITIVE_LFUNCTION_ZERO_IN_CRITICAL_STRIP
    {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction χ.primitiveCharacter s = 0 := by
  have hs_ne_one : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs1
  have hchange := DirichletCharacter.LFunction_changeLevel
    χ.conductor_dvd_level χ.primitiveCharacter (s := s) (Or.inr hs_ne_one)
  rw [χ.changeLevel_primitiveCharacter] at hchange
  have hprod :
      (∏ p ∈ N.primeFactors,
        (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))) ≠ 0 :=
    DIRICHLET_CHANGE_LEVEL_EULER_PRODUCT_NE_ZERO_OF_RE_POS
      (N := N) χ.primitiveCharacter hs0
  rw [hz] at hchange
  have hmul :
      DirichletCharacter.LFunction χ.primitiveCharacter s *
        (∏ p ∈ N.primeFactors,
          (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))) = 0 :=
    hchange.symm
  rcases mul_eq_zero.mp hmul with hprim | hfactor
  · exact hprim
  · exact (hprod hfactor).elim

/-- The primitive-character GRH already formalized in the project implies the
literal textbook statement for every Dirichlet character. -/
theorem GRH_IMPLIES_TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS :
    GeneralizedRiemannHypothesis → TextbookGeneralizedRiemannHypothesis := by
  intro hGRH N _ χ s hs
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprimZero : DirichletCharacter.LFunction χ.primitiveCharacter s = 0 :=
    LFUNCTION_ZERO_IMPLIES_PRIMITIVE_LFUNCTION_ZERO_IN_CRITICAL_STRIP
      χ hs.2.1 hs.2.2 hs.1
  have hprimRH : DirichletRiemannHypothesis χ.primitiveCharacter :=
    hGRH χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  exact hprimRH s ⟨hprimZero, hs.2.1, hs.2.2⟩

/-- Conversely the all-character textbook formulation trivially contains the
primitive-character formulation as a special case. -/
theorem TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IMPLIES_GRH :
    TextbookGeneralizedRiemannHypothesis → GeneralizedRiemannHypothesis := by
  intro hText N _ χ _hχ
  exact hText N χ

/-- Closed equivalence between the literal all-Dirichlet-character textbook
GRH and the project's primitive-character GRH. -/
theorem TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IFF_GRH :
    TextbookGeneralizedRiemannHypothesis ↔ GeneralizedRiemannHypothesis := by
  exact ⟨TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IMPLIES_GRH,
    GRH_IMPLIES_TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS⟩

/-- The already-verified actual two-point completed-L Cayley observable is
therefore total on the full critical parameter domain exactly when the literal
textbook all-character GRH holds. -/
theorem GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_TEXTBOOK_GRH :
    GeneralizedCompletedPairActualCayleyObservableCriticalTotal ↔
      TextbookGeneralizedRiemannHypothesis := by
  exact GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.trans
    TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IFF_GRH.symm

/-- Closed A-tier atlas whose headline GRH statement has no primitive-character
hypothesis in its definition. -/
theorem TEXTBOOK_ALL_CHARACTERS_GRH_A_TIER_ATLAS :
    (TextbookGeneralizedRiemannHypothesis ↔ GeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairSlitThetaCriticalZeroFree ↔
      TextbookGeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairSlitThetaCriticalLogDerivativeTotal ↔
      TextbookGeneralizedRiemannHypothesis) ∧
    (GeneralizedCompletedPairActualCayleyObservableCriticalTotal ↔
      TextbookGeneralizedRiemannHypothesis) ∧
    (TextbookGeneralizedRiemannHypothesis → _root_.RiemannHypothesis) := by
  refine ⟨TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IFF_GRH, ?_, ?_, ?_, ?_⟩
  · exact GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_ZERO_FREE_IFF_GRH.trans
      TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IFF_GRH.symm
  · exact GENERALIZED_COMPLETED_PAIR_SLIT_THETA_CRITICAL_LOG_DERIVATIVE_TOTAL_IFF_GRH.trans
      TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IFF_GRH.symm
  · exact GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_TEXTBOOK_GRH
  · intro hText
    exact CayleyGRHClosure.GRH_IMPLIES_MATHLIB_RH
      (TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IMPLIES_GRH hText)

end CayleyGRHStrong
