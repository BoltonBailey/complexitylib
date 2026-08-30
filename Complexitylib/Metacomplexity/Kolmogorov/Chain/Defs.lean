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

end Complexity
