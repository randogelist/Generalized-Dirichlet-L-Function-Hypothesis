import TextbookDirichletGRH

namespace RHToGRHFrontier

open CayleyGRHClosure
open CayleyGRHStrong

/--
The single family-level cross-bridge still missing after the ordinary-RH and
Dirichlet-GRH Cayley equivalence closures: assuming ordinary RH, the actual
completed-pair Dirichlet-L Cayley observable is total on the full generalized
critical parameter domain.

This is deliberately a proposition, not an axiom.  Proving this proposition
is exactly the constructive frontier of this subbranch.
-/
def RiemannToGeneralizedCayleyLift : Prop :=
  _root_.RiemannHypothesis →
    GeneralizedCompletedPairActualCayleyObservableCriticalTotal

/--
The Cayley lift frontier is exactly the missing implication RH -> primitive
Dirichlet GRH.  No analytic content is hidden in this wrapper: the equivalence
uses the already-compiled generalized actual-Cayley-totality iff GRH theorem.
-/
theorem RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_GRH :
    RiemannToGeneralizedCayleyLift ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis) := by
  constructor
  · intro hLift hRH
    exact
      GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mp
        (hLift hRH)
  · intro hImp hRH
    exact
      GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mpr
        (hImp hRH)

/--
The same single Cayley lift is exactly RH -> literal textbook GRH over all
Dirichlet characters, using the already-closed primitive/all-character bridge.
-/
theorem RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_TEXTBOOK_GRH :
    RiemannToGeneralizedCayleyLift ↔
      (_root_.RiemannHypothesis → TextbookGeneralizedRiemannHypothesis) := by
  constructor
  · intro hLift hRH
    have hGRH : GeneralizedRiemannHypothesis :=
      GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mp
        (hLift hRH)
    exact GRH_IMPLIES_TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS hGRH
  · intro hImp hRH
    have hGRH : GeneralizedRiemannHypothesis :=
      TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IMPLIES_GRH (hImp hRH)
    exact
      GENERALIZED_COMPLETED_PAIR_ACTUAL_CAYLEY_OBSERVABLE_CRITICAL_TOTAL_IFF_GRH.mpr
        hGRH

/-- The converse direction GRH -> RH is already closed in the GRH package. -/
theorem GRH_TO_RH_ALREADY_CLOSED :
    GeneralizedRiemannHypothesis → _root_.RiemannHypothesis := by
  exact CayleyGRHClosure.GRH_IMPLIES_MATHLIB_RH

/--
Once the single Cayley lift frontier is proved, ordinary RH and primitive
Dirichlet GRH are equivalent.
-/
theorem RH_IFF_GRH_OF_GENERALIZED_CAYLEY_LIFT
    (hLift : RiemannToGeneralizedCayleyLift) :
    _root_.RiemannHypothesis ↔ GeneralizedRiemannHypothesis := by
  constructor
  · exact
      (RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_GRH.mp hLift)
  · exact GRH_TO_RH_ALREADY_CLOSED

/--
Once the same lift is proved, ordinary RH is also equivalent to the literal
all-Dirichlet-character textbook GRH statement.
-/
theorem RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT
    (hLift : RiemannToGeneralizedCayleyLift) :
    _root_.RiemannHypothesis ↔ TextbookGeneralizedRiemannHypothesis := by
  constructor
  · exact
      (RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_TEXTBOOK_GRH.mp hLift)
  · intro hText
    exact GRH_TO_RH_ALREADY_CLOSED
      (TEXTBOOK_GENERALIZED_RIEMANN_HYPOTHESIS_IMPLIES_GRH hText)

/--
Assembly form for the intended subbranch: an already-obtained theorem of RH,
plus the one new generalized Cayley lift, yields primitive-character GRH.
-/
theorem GRH_OF_CONSTRUCTED_RH_AND_GENERALIZED_CAYLEY_LIFT
    (hRH : _root_.RiemannHypothesis)
    (hLift : RiemannToGeneralizedCayleyLift) :
    GeneralizedRiemannHypothesis := by
  exact
    (RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_GRH.mp hLift) hRH

/--
The same assembly immediately yields literal textbook GRH for every Dirichlet
character; no separate imprimitive-character construction is required.
-/
theorem TEXTBOOK_GRH_OF_CONSTRUCTED_RH_AND_GENERALIZED_CAYLEY_LIFT
    (hRH : _root_.RiemannHypothesis)
    (hLift : RiemannToGeneralizedCayleyLift) :
    TextbookGeneralizedRiemannHypothesis := by
  exact
    (RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_TEXTBOOK_GRH.mp hLift) hRH

/--
Frozen logical atlas for the RH -> GRH subbranch.  It does NOT prove the lift;
it proves that there is exactly one family-level missing bridge and records
all consequences once that bridge is supplied.
-/
theorem RH_TO_GRH_SINGLE_FRONTIER_ATLAS :
    (RiemannToGeneralizedCayleyLift ↔
      (_root_.RiemannHypothesis → GeneralizedRiemannHypothesis)) ∧
    (RiemannToGeneralizedCayleyLift ↔
      (_root_.RiemannHypothesis → TextbookGeneralizedRiemannHypothesis)) ∧
    (GeneralizedRiemannHypothesis → _root_.RiemannHypothesis) := by
  exact ⟨RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_GRH,
    RIEMANN_TO_GENERALIZED_CAYLEY_LIFT_IFF_RH_IMPLIES_TEXTBOOK_GRH,
    GRH_TO_RH_ALREADY_CLOSED⟩

end RHToGRHFrontier
