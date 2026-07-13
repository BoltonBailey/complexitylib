/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Encoding.Family

/-!
# Encoded-circuit evaluator — executable validation

Small executable checks complement the universal codec and semantic-correctness
theorems. They make the intended malformed-input behavior easy to inspect and
guard against accidental changes to the concrete wire format.

This module is not part of the public import graph. Build it explicitly with
`lake build --wfail Complexitylib.Circuits.Encoding.Validation`.
-/

namespace Complexity

namespace CircuitCode.Validation

/-- A two-input AND circuit with no negated edges. -/
def andCircuit : RawCircuit :=
  [{ op := .and
     input₀ := 0
     input₁ := 1
     negated₀ := false
     negated₁ := false }]

/-- A malformed circuit whose sole gate refers to its own output wire. -/
def selfReferentialCircuit : RawCircuit :=
  [{ op := .or
     input₀ := 0
     input₁ := 2
     negated₀ := false
     negated₁ := false }]

/-- A conjunction whose first incoming edge is negated. -/
def negatedCircuit : RawCircuit :=
  [{ op := .and
     input₀ := 0
     input₁ := 1
     negated₀ := true
     negated₁ := false }]

/-- A two-gate DAG whose output gate reads the shared first-gate value twice. -/
def sharedCircuit : RawCircuit :=
  [{ op := .or
     input₀ := 0
     input₁ := 1
     negated₀ := false
     negated₁ := false },
   { op := .and
     input₀ := 2
     input₁ := 2
     negated₀ := false
     negated₁ := false }]

-- The compiled fragment reads wires 2 and 3, both produced by the raw prefix.
private def priorWirePrefix : RawCircuit :=
  andCircuit ++ negatedCircuit

private def priorWireFormula : BoolFormula :=
  .disj (.var 2) (.var 3)

private def priorWireCircuit : RawCircuit :=
  priorWirePrefix ++ BoolFormula.compileRaw 4 priorWireFormula

private def formulaBatch : RawCircuit :=
  BoolFormula.compileRawBatch 2
    [.conj (.var 0) (.var 1), .neg (.var 0)]

private def twoOfThree : RawCircuit :=
  Threshold.compileRaw 3 2 fun i : Fin 3 => i.val

#guard RawCircuit.decode? andCircuit.encode = some andCircuit
#guard RawCircuit.decode? andCircuit.encode.dropLast = none
#guard RawCircuit.decode? (andCircuit.encode ++ [false]) = none

#guard evalCode 2 andCircuit.encode [true, true] = some true
#guard evalCode 2 andCircuit.encode [true, false] = some false
#guard evalCode 2 negatedCircuit.encode [false, true] = some true
#guard evalCode 2 sharedCircuit.encode [true, false] = some true
#guard evalCode 2 andCircuit.encode [true] = none
#guard evalCode 2 selfReferentialCircuit.encode [true, false] = none

#guard (BoolFormula.compileRaw 4 priorWireFormula).length = 3
#guard priorWireCircuit.length = 5
#guard RawCircuit.isWellFormed 2 priorWireCircuit = true
#guard priorWireCircuit.eval? [true, true] = some true
#guard priorWireCircuit.eval? [false, true] = some true
#guard priorWireCircuit.eval? [true, false] = some false

#guard formulaBatch.length = 7
#guard RawCircuit.isWellFormed 2 formulaBatch = true
#guard (RawCircuit.evalAux? formulaBatch #[true, false]).bind (fun wires => wires[7]?) =
  some false
#guard (RawCircuit.evalAux? formulaBatch #[false, true]).bind (fun wires => wires[8]?) =
  some true

#guard twoOfThree.length = 15
#guard RawCircuit.isWellFormed 3 twoOfThree = true
#guard twoOfThree.eval? [true, false, true] = some true
#guard twoOfThree.eval? [true, false, false] = some false

-- Positive codes are parameterized by the evaluator's arity rather than
-- carrying a serialized arity stamp of their own.
#guard evalCode 3 andCircuit.encode [true, true, false] = some true

#guard evalFamilyCode [false, true] [] = some true
#guard evalFamilyCode [false, true, false] [] = none
#guard evalFamilyCode (true :: andCircuit.encode) [true, false] = some false
#guard evalFamilyCode (false :: andCircuit.encode) [true, false] = none

#guard evalFamilyPair? (pair [false, true] []) = some true
#guard evalFamilyPair? (pair (true :: andCircuit.encode) [true, false]) = some false
#guard evalFamilyPair? (pair [false, true, false] []) = none
#guard evalFamilyPair? [] = none

end CircuitCode.Validation

end Complexity
