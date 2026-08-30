/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Defs

/-!
# Time-bounded description composition -- definitions

A chain-rule upper bound is not valid for arbitrary unrelated machines. This
module therefore isolates the operational premise that a joint machine can
compose a bounded program for `firstOutput` with a bounded conditional program
for `secondOutput` given `firstOutput`. The program compiler, both source
clocks, the target clock, and both description budgets remain explicit.

The joint output uses the library's canonical `pair` codec. The compiled
program syntax is a parameter: later evaluator constructions may use `pair`,
its reverse orientation, or a more efficient self-delimiting code.
-/


@[expose] public section

namespace Complexity

/-- Under fixed description budgets and clocks, `compile` composes an ordinary
program for `firstOutput` and a random-access conditional program for
`secondOutput` into a program for their canonical pair.

This is deliberately an operational contract, not an assumption that arbitrary
machines satisfy a chain rule. -/
def TimeBoundedProgramCompositionAt
    {jointTapes firstTapes secondTapes : ℕ}
    (jointMachine : TM jointTapes) (firstMachine : TM firstTapes)
    (secondMachine : OracleTM secondTapes)
    (compile : List Bool → List Bool → List Bool)
    (firstOutput secondOutput : List Bool)
    (firstTime secondTime jointTime firstBound secondBound : ℕ) : Prop :=
  ∀ firstProgram secondProgram,
    firstProgram.length ≤ firstBound →
    secondProgram.length ≤ secondBound →
    firstMachine.ProducesInTime firstProgram firstOutput firstTime →
    secondMachine.ProducesInTime
        (RandomAccessCondition.oracle firstOutput)
        secondProgram secondOutput secondTime →
    jointMachine.ProducesInTime
      (compile firstProgram secondProgram)
      (pair firstOutput secondOutput) jointTime

/-- Condition-first composition for the chain-rule orientation used by SoI.
The ordinary program produces `condition`; the oracle program then produces
`result` given random access to that condition; the joint output is nevertheless
ordered as `pair result condition`.

Keeping this contract distinct from `TimeBoundedProgramCompositionAt` prevents
an unnoticed swap between `C(y) + C(x | y)` and the encoded output
`pair x y`. -/
def TimeBoundedConditionalPairCompositionAt
    {jointTapes conditionTapes resultTapes : ℕ}
    (jointMachine : TM jointTapes) (conditionMachine : TM conditionTapes)
    (resultMachine : OracleTM resultTapes)
    (compile : List Bool → List Bool → List Bool)
    (result condition : List Bool)
    (conditionTime resultTime jointTime conditionBound resultBound : ℕ) : Prop :=
  ∀ conditionProgram resultProgram,
    conditionProgram.length ≤ conditionBound →
    resultProgram.length ≤ resultBound →
    conditionMachine.ProducesInTime
      conditionProgram condition conditionTime →
    resultMachine.ProducesInTime
        (RandomAccessCondition.oracle condition)
        resultProgram result resultTime →
    jointMachine.ProducesInTime
      (compile conditionProgram resultProgram)
      (pair result condition) jointTime

end Complexity
