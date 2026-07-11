import Complexitylib.Circuits.Encoding.Defs
import Complexitylib.Circuits.Encoding.Internal

namespace Complexity

/-!
# Encoded fan-in-two circuits

This module exposes the machine-facing representation of
`Basis.andOr2` circuits and its correctness theorems.

## Main definitions

- `AONCircuitCode.RawGate` and `RawCircuit`: proof-free ordered syntax.
- `RawCircuit.WellFormed`: nonempty, strictly backward-pointing gate lists.
- `RawCircuit.encode` / `decode?`: canonical terminated-unary bit codec.
- `RawCircuit.eval?`: array-backed iterative evaluation.
- `AONCircuitCode.encodeCircuit`: serialization of a typed circuit.
- `AONCircuitCode.evalCode`: decode and evaluate with an exact arity check.

## Main results

- `RawCircuit.decode?_eq_some_iff`: exact decoder soundness and completeness.
- `RawCircuit.eval?_isSome_iff`: executable success exactly matches
  well-formedness.
- `AONCircuitCode.evalCode_encodeCircuit`: encoded evaluation agrees with
  `Circuit.eval`.
- `AONCircuitCode.evalCode_encodeCircuit_of_length`: the corresponding
  list-native theorem for machine-facing clients.
- `AONCircuitCode.encodeCircuit_length_le_size`: concrete polynomial bit-length
  bound for the unary encoding.
-/

namespace AONCircuitCode

namespace RawCircuit

/-- Exact decoding succeeds precisely on canonical raw-circuit encodings. -/
theorem decode?_eq_some_iff (bits : List Bool) (circuit : RawCircuit) :
    decode? bits = some circuit ↔ bits = circuit.encode :=
  decode?_eq_some_iff_internal bits circuit

/-- Raw evaluation succeeds precisely for nonempty topologically ordered
circuits at the supplied input arity. -/
theorem eval?_isSome_iff (circuit : RawCircuit) (input : List Bool) :
    (circuit.eval? input).isSome ↔ circuit.WellFormed input.length :=
  eval?_isSome_iff_internal circuit input

end RawCircuit

/-- Decoding and iteratively evaluating the canonical encoding of a typed
fan-in-two circuit returns its typed output. -/
theorem evalCode_encodeCircuit {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (input : BitString N) :
    evalCode N (encodeCircuit c) input.toList = some ((c.eval input) 0) :=
  evalCode_encodeCircuit_internal c input

/-- List-native semantic correctness for an input of the declared arity. -/
theorem evalCode_encodeCircuit_of_length {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (input : List Bool)
    (hinput : input.length = N) :
    evalCode N (encodeCircuit c) input =
      some ((c.eval (BitString.ofList input hinput)) 0) :=
  evalCode_encodeCircuit_of_length_internal c input hinput

/-- In the library's size convention, which counts internal and output gates
but not primary inputs or free negations, unary circuit codes have quadratic
length in the input arity and circuit size. -/
theorem encodeCircuit_length_le_size {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) :
    (encodeCircuit c).length ≤
      1 + c.size * (2 * (N + c.size) + 6) :=
  encodeCircuit_length_le_size_internal c

end AONCircuitCode

end Complexity
