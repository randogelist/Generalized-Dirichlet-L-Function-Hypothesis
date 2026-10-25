# Ordinary RH to Dirichlet GRH

The exact existing conditional equivalence is

```lean
theorem RH_IFF_TEXTBOOK_GRH_OF_GENERALIZED_CAYLEY_LIFT
    (hLift : RiemannToGeneralizedCayleyLift) :
    _root_.RiemannHypothesis ↔ TextbookGeneralizedRiemannHypothesis
```

The names in this excerpt are opened in
[RHToGRHCayleyLiftFrontier.lean](../RHToGRHCayleyLiftFrontier.lean).
The mathematical source and its hypotheses are unchanged.

`RiemannToGeneralizedCayleyLift` is defined there as

```lean
_root_.RiemannHypothesis →
  GeneralizedCompletedPairActualCayleyObservableCriticalTotal
```

The generalized totality predicate quantifies over primitive Dirichlet
characters. The completed-pair source connects it to primitive GRH, and
[TextbookDirichletGRH.lean](../TextbookDirichletGRH.lean) connects primitive GRH
to all-character GRH. Consequently the lift is equivalent to `RH → GRH`.
This reformulation does not discharge the lift.

## Existing disassembly

The source successively expresses the same open implication as generalized
Cayley totality, cross-Cayley transfer, primitive-character slit zero-freeness,
centered completed-pair nonvanishing, reflection-pair conditions, and four
explicit completed Dirichlet L-factor conditions. The new first-factor module
then reduces those four conditions to a single universal family.

For every primitive character χ, with `s = 1/2 + sqrt z` on the source's
critical square/slit domain, the final condition requires, assuming RH:

- `completedLFunction χ s ≠ 0`;
- `completedLFunction χ⁻¹ s ≠ 0`;
- `completedLFunction χ (1-s) ≠ 0`;
- `completedLFunction χ⁻¹ (1-s) ≠ 0`.

The exact domains and quantifiers are in
[RHToGRHCompletedLFactorFrontier.lean](../RHToGRHCompletedLFactorFrontier.lean).
`COMPLETED_L_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH` proves the equivalence between
that universal implication and `RH → GRH`; it does not supply the factors'
nonvanishing.

## Precise remaining condition

The new definition
`RHToGRHFirstFactor.RiemannToPrimitiveCharacterFirstCompletedLFactorNonzero`
is exactly

```lean
_root_.RiemannHypothesis →
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive →
      ∀ z ∈ CayleyGRHStrong.completedPairCriticalSquareDomain,
        z ∈ Complex.slitPlane →
          DirichletCharacter.completedLFunction χ (1 / 2 + z.sqrt) ≠ 0
```

[RHToGRHFirstFactorFrontier.lean](../RHToGRHFirstFactorFrontier.lean) contains
source proofs of `FIRST_FACTOR_IFF_FOUR_FACTORS` and
`FIRST_FACTOR_IFF_RH_IMPLIES_GRH`. The first uses the same condition for `χ⁻¹`
and the existing primitive completed-L zero-reflection theorem to recover
the other three factors. The second composes that reduction with
`COMPLETED_L_FACTORS_NONZERO_IFF_RH_IMPLIES_GRH`.

This is a reduction to **one universal analytic condition**, not to one scalar
sample, finitely many characters, or a terminating certificate. All positive
moduli, all primitive characters, and every point in the stated domain remain
quantified. The condition is **OPEN / NOT_DISCHARGED**. Both new theorem sources
and their prepared signature/axiom checks are **NOT_RUN** natively; no
unconditional `RH → GRH`, `RH ↔ GRH`, RH proof, or GRH proof is claimed.

## Remaining work

Derive a family-level analytic transfer from the ordinary zeta RH input to
the universal first-factor nonvanishing condition above. Per-character equivalences and a common
scalar Cayley identity alone do not derive it. The existing source already
contains the converse `GRH → RH` through the modulus-one character.

These universal analytic propositions are not finite raw witnesses, and this
repository does not include a terminating checker whose acceptance proves
the lift. Compilation of a conditional theorem would certify its conditional
statement, not establish its premise.

One inherited auxiliary pointwise theorem has a potentially implicit `hRH`
parameter. The [audit entry point](../GRHFinal/Audit.lean) exposes its elaborated
signature for the native run; see [theorem-audit.json](../provenance/theorem-audit.json).
It is not used by the principal lift and four-factor proof chains according
to source inspection. No source-level uncertainty is reported as a compiler
error or a verified pass.
