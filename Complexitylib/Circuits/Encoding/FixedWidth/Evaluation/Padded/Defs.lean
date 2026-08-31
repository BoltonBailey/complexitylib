/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Defs

/-!
# Padded fixed-width raw-circuit semantics -- definitions

The ordinary `Description.toRawCircuit` keeps only active slots. Sequential
encoded evaluation computes every bounded slot, including canonical inactive
slots. This module names the corresponding full-length raw circuit.
-/


@[expose] public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace Description

/-- Raw gates for every fixed slot, including canonical inactive padding. -/
def toPaddedRawCircuit {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) : RawCircuit :=
  List.ofFn fun slot : Fin gateBound =>
    (description.slots slot).toRawGate

end Description

end FixedWidth

end CircuitCode

end Complexity
