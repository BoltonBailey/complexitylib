/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Hamming.Code.Defs

/-!
# Boolean repetition codes -- definitions

The repetition encoder writes each of `messageLength` bits into `copies`
coordinates, using the library's canonical `Fin (messageLength * copies)` block
equivalence. It is defined even at zero copies; the code construction later
requires positivity for injectivity.
-/


@[expose] public section

namespace Complexity

namespace BooleanCode

/-- Repeat every input bit in a block of `copies` output coordinates. -/
def repetitionEncode (messageLength copies : ℕ)
    (message : BooleanHamming.Word messageLength) :
    BooleanHamming.Word (messageLength * copies) :=
  (blocksEquiv messageLength copies).symm fun input _ => message input

end BooleanCode

end Complexity
