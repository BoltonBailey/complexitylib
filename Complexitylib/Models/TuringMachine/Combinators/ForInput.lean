/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.ForInput.Defs
import Complexitylib.Models.TuringMachine.Combinators.ForInput.Internal

/-!
# Read-only-input loop combinator

`TM.forInputTM body` advances over a Boolean input symbol and invokes `body`
without copying the input into auxiliary space. For input-preserving bodies,
this iterates exactly once per original symbol. It is the input-fueled
counterpart of the unary-work-register loop `TM.forRegTM`.

## Main result

- `TM.IsTransducer.forInputTM` — input-driven iteration preserves one-way output.
-/

namespace Complexity

namespace TM

/-- Iterating a one-way-output body over the read-only input remains a
one-way-output transducer. -/
theorem IsTransducer.forInputTM {n : ℕ} {body : TM n}
    (hbody : body.IsTransducer) : (forInputTM body).IsTransducer :=
  hbody.forInputTM_internal

end TM

end Complexity
