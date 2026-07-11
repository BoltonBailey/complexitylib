import Complexitylib.Circuits.Encoding.Family

/-!
# Encoded-circuit evaluator — executable validation

Small executable checks complement the universal codec and semantic-correctness
theorems. They make the intended malformed-input behavior easy to inspect and
guard against accidental changes to the concrete wire format.

This module is not part of the public import graph. Build it explicitly with
`lake build --wfail Complexitylib.Circuits.Encoding.Validation`.
-/

namespace AONCircuitCode.Validation

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

#guard RawCircuit.decode? andCircuit.encode = some andCircuit
#guard RawCircuit.decode? andCircuit.encode.dropLast = none
#guard RawCircuit.decode? (andCircuit.encode ++ [false]) = none

#guard evalCode 2 andCircuit.encode [true, true] = some true
#guard evalCode 2 andCircuit.encode [true, false] = some false
#guard evalCode 2 negatedCircuit.encode [false, true] = some true
#guard evalCode 2 sharedCircuit.encode [true, false] = some true
#guard evalCode 2 andCircuit.encode [true] = none
#guard evalCode 2 selfReferentialCircuit.encode [true, false] = none

-- Positive codes are parameterized by the evaluator's arity rather than
-- carrying a serialized arity stamp of their own.
#guard evalCode 3 andCircuit.encode [true, true, false] = some true

#guard evalFamilyCode [false, true] [] = some true
#guard evalFamilyCode [false, true, false] [] = none
#guard evalFamilyCode (true :: andCircuit.encode) [true, false] = some false
#guard evalFamilyCode (false :: andCircuit.encode) [true, false] = none

end AONCircuitCode.Validation
