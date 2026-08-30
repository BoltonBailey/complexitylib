/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Chain.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Chain.Internal

/-!
# Time-bounded description composition

This module proves the finite upper-chain inequality licensed by an explicit
program-composition contract. It does not assume that unrelated machines can
compose descriptions. Both source clocks and budgets, the target clock, the
compiler, and its encoded-length cost occur in the public theorem.

For the canonical `pair` program codec the first description is doubled, so
the exact bound is `2 * firstBound + 2 + secondBound`. A reverse-program-pair
variant exposes the alternative orientation rather than hiding this codec loss
inside asymptotic notation.
-/


public section

namespace Complexity

/-- A composition contract remains valid after restricting either description
budget. -/
theorem TimeBoundedProgramCompositionAt.restrict_bounds
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {compile : List Bool → List Bool → List Bool}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime jointTime firstBound secondBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine compile firstOutput secondOutput firstTime secondTime
      jointTime firstBound secondBound)
    {smallerFirstBound smallerSecondBound : ℕ}
    (hfirst : smallerFirstBound ≤ firstBound)
    (hsecond : smallerSecondBound ≤ secondBound) :
    TimeBoundedProgramCompositionAt jointMachine firstMachine secondMachine
      compile firstOutput secondOutput firstTime secondTime jointTime
      smallerFirstBound smallerSecondBound :=
  hcompose.restrict_bounds_internal hfirst hsecond

/-- A composition contract remains valid after enlarging its target clock. -/
theorem TimeBoundedProgramCompositionAt.mono_jointTime
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {compile : List Bool → List Bool → List Bool}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime firstJointTime secondJointTime firstBound secondBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine compile firstOutput secondOutput firstTime secondTime
      firstJointTime firstBound secondBound)
    (hjoint : firstJointTime ≤ secondJointTime) :
    TimeBoundedProgramCompositionAt jointMachine firstMachine secondMachine
      compile firstOutput secondOutput firstTime secondTime secondJointTime
      firstBound secondBound :=
  hcompose.mono_jointTime_internal hjoint

/-- Generic finite upper-chain rule: if bounded descriptions can be compiled
within `combinedBound`, their joint bounded complexity obeys that bound. -/
theorem timeBoundedKolmogorovComplexity_pair_le_of_composition
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {compile : List Bool → List Bool → List Bool}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime jointTime firstBound secondBound combinedBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine compile firstOutput secondOutput firstTime secondTime
      jointTime firstBound secondBound)
    (hlength : ∀ firstProgram secondProgram,
      firstProgram.length ≤ firstBound →
      secondProgram.length ≤ secondBound →
      (compile firstProgram secondProgram).length ≤ combinedBound)
    (hfirst : firstMachine.timeBoundedKolmogorovComplexity
      firstOutput firstTime ≤ (firstBound : WithTop ℕ))
    (hsecond : secondMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        secondOutput firstOutput secondTime ≤ (secondBound : WithTop ℕ)) :
    jointMachine.timeBoundedKolmogorovComplexity
        (pair firstOutput secondOutput) jointTime ≤
      (combinedBound : WithTop ℕ) :=
  timeBoundedKolmogorovComplexity_pair_le_of_composition_internal
    hcompose hlength hfirst hsecond

/-- Using canonical `pair` on programs yields the exact codec cost
`2 * firstBound + 2 + secondBound`. -/
theorem timeBoundedKolmogorovComplexity_pair_le_of_pair_composition
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime jointTime firstBound secondBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine pair firstOutput secondOutput firstTime secondTime
      jointTime firstBound secondBound)
    (hfirst : firstMachine.timeBoundedKolmogorovComplexity
      firstOutput firstTime ≤ (firstBound : WithTop ℕ))
    (hsecond : secondMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        secondOutput firstOutput secondTime ≤ (secondBound : WithTop ℕ)) :
    jointMachine.timeBoundedKolmogorovComplexity
        (pair firstOutput secondOutput) jointTime ≤
      (2 * firstBound + 2 + secondBound : ℕ) :=
  timeBoundedKolmogorovComplexity_pair_le_of_pair_composition_internal
    hcompose hfirst hsecond

/-- Reversing the program-pair orientation doubles the second description
instead, giving `2 * secondBound + 2 + firstBound`. -/
theorem timeBoundedKolmogorovComplexity_pair_le_of_reverse_pair_composition
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime jointTime firstBound secondBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine (fun firstProgram secondProgram =>
        pair secondProgram firstProgram) firstOutput secondOutput
      firstTime secondTime jointTime firstBound secondBound)
    (hfirst : firstMachine.timeBoundedKolmogorovComplexity
      firstOutput firstTime ≤ (firstBound : WithTop ℕ))
    (hsecond : secondMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        secondOutput firstOutput secondTime ≤ (secondBound : WithTop ℕ)) :
    jointMachine.timeBoundedKolmogorovComplexity
        (pair firstOutput secondOutput) jointTime ≤
      (2 * secondBound + 2 + firstBound : ℕ) :=
  timeBoundedKolmogorovComplexity_pair_le_of_reverse_pair_composition_internal
    hcompose hfirst hsecond

/-- A condition-first composition contract remains valid after restricting its
two description budgets. -/
theorem TimeBoundedConditionalPairCompositionAt.restrict_bounds
    {jointTapes conditionTapes resultTapes : ℕ}
    {jointMachine : TM jointTapes} {conditionMachine : TM conditionTapes}
    {resultMachine : OracleTM resultTapes}
    {compile : List Bool → List Bool → List Bool}
    {result condition : List Bool}
    {conditionTime resultTime jointTime conditionBound resultBound : ℕ}
    (hcompose : TimeBoundedConditionalPairCompositionAt jointMachine
      conditionMachine resultMachine compile result condition conditionTime
      resultTime jointTime conditionBound resultBound)
    {smallerConditionBound smallerResultBound : ℕ}
    (hcondition : smallerConditionBound ≤ conditionBound)
    (hresult : smallerResultBound ≤ resultBound) :
    TimeBoundedConditionalPairCompositionAt jointMachine conditionMachine
      resultMachine compile result condition conditionTime resultTime jointTime
      smallerConditionBound smallerResultBound :=
  hcompose.restrict_bounds_internal hcondition hresult

/-- Enlarging the target clock preserves a condition-first composition
contract. -/
theorem TimeBoundedConditionalPairCompositionAt.mono_jointTime
    {jointTapes conditionTapes resultTapes : ℕ}
    {jointMachine : TM jointTapes} {conditionMachine : TM conditionTapes}
    {resultMachine : OracleTM resultTapes}
    {compile : List Bool → List Bool → List Bool}
    {result condition : List Bool}
    {conditionTime resultTime firstJointTime secondJointTime
      conditionBound resultBound : ℕ}
    (hcompose : TimeBoundedConditionalPairCompositionAt jointMachine
      conditionMachine resultMachine compile result condition conditionTime
      resultTime firstJointTime conditionBound resultBound)
    (hjoint : firstJointTime ≤ secondJointTime) :
    TimeBoundedConditionalPairCompositionAt jointMachine conditionMachine
      resultMachine compile result condition conditionTime resultTime
      secondJointTime conditionBound resultBound :=
  hcompose.mono_jointTime_internal hjoint

/-- A condition-first compiler with additive encoded length gives the exact
upper chain rule
`C(pair result condition) ≤ C(result | condition) + C(condition) + constant`.
Finiteness and budget hypotheses are explicit because the machines are not yet
fixed universal evaluators. -/
theorem timeBoundedKolmogorovComplexity_pair_le_add_of_conditional_composition
    {jointTapes conditionTapes resultTapes : ℕ}
    {jointMachine : TM jointTapes} {conditionMachine : TM conditionTapes}
    {resultMachine : OracleTM resultTapes}
    {compile : List Bool → List Bool → List Bool}
    {result condition : List Bool}
    {conditionTime resultTime jointTime conditionBound resultBound constant : ℕ}
    (hcompose : TimeBoundedConditionalPairCompositionAt jointMachine
      conditionMachine resultMachine compile result condition conditionTime
      resultTime jointTime conditionBound resultBound)
    (hlength : ∀ conditionProgram resultProgram,
      conditionProgram.length ≤ conditionBound →
      resultProgram.length ≤ resultBound →
      (compile conditionProgram resultProgram).length ≤
        resultProgram.length + conditionProgram.length + constant)
    (hconditionFinite : conditionMachine.timeBoundedKolmogorovComplexity
      condition conditionTime ≠ ⊤)
    (hresultFinite :
      resultMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        result condition resultTime ≠ ⊤)
    (hconditionBound : conditionMachine.timeBoundedKolmogorovComplexity
      condition conditionTime ≤ (conditionBound : WithTop ℕ))
    (hresultBound :
      resultMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        result condition resultTime ≤ (resultBound : WithTop ℕ)) :
    jointMachine.timeBoundedKolmogorovComplexity
        (pair result condition) jointTime ≤
      resultMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
            result condition resultTime +
          conditionMachine.timeBoundedKolmogorovComplexity
            condition conditionTime +
        (constant : WithTop ℕ) :=
  timeBoundedKolmogorovComplexity_pair_le_add_of_conditional_composition_internal
    hcompose hlength hconditionFinite hresultFinite hconditionBound hresultBound

end Complexity
