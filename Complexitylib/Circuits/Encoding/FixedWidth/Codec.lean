/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.Encoding.FixedWidth.Codec.Defs
import Complexitylib.Circuits.Encoding.FixedWidth.Codec.Internal

/-!
# Fixed-width binary circuit-description codec

Gate slots are in exact correspondence with their fixed-width Boolean words.
Bounded descriptions also have an exact codec, except that decoding rejects
the count words whose values exceed the advertised gate bound.
-/


public section

namespace Complexity

namespace CircuitCode

namespace FixedWidth

namespace GateSlot

/-- Decoding the fixed-width code of a gate slot recovers the slot. -/
@[simp] theorem decode_encode {width : Nat} (slot : GateSlot width) :
    decode (encode slot) = slot :=
  decode_encode_internal slot

/-- Encoding any decoded fixed-width gate-slot word recovers the word. -/
@[simp] theorem encode_decode {width : Nat}
    (bits : BitString (3 + (width + width))) :
    encode (decode bits) = bits :=
  encode_decode_internal bits

/-- Fixed-width gate-slot encoding is injective. -/
theorem encode_injective {width : Nat} :
    Function.Injective (@encode width) :=
  encode_injective_internal

/-- Gate slots are in exact correspondence with fixed-width Boolean words. -/
def codecEquiv (width : Nat) :
    GateSlot width ≃ BitString (3 + (width + width)) :=
  codecEquivInternal width

end GateSlot

namespace Description

/-- Encoding places the gate count in the leading count word. -/
@[simp] theorem countBits_encode {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    countBits (encode description) =
      GateSlot.referenceBits (gateCountWidth gateBound)
        description.gateCountNat :=
  countBits_encode_internal description

/-- Encoding places each gate slot in its corresponding fixed-width block. -/
@[simp] theorem slotBits_encode {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound)
    (slot : Fin gateBound) :
    slotBits (encode description) slot =
      GateSlot.encode (description.slots slot) :=
  slotBits_encode_internal description slot

/-- Reading the leading count word of an encoding recovers the gate count. -/
@[simp] theorem countValue_encode {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    countValue (encode description) = description.gateCountNat :=
  countValue_encode_internal description

/-- Encoding and then decoding a bounded description is exact. -/
@[simp] theorem decode?_encode {inputWidth gateBound : Nat}
    (description : Description inputWidth gateBound) :
    decode? (encode description) = some description :=
  decode?_encode_internal description

/-- A successfully decoded description re-encodes to the original word. -/
theorem encode_eq_of_decode?_eq_some
    {inputWidth gateBound : Nat}
    {code : BitString (codeWidth inputWidth gateBound)}
    {description : Description inputWidth gateBound}
    (hdecode : decode? code = some description) :
    encode description = code :=
  encode_eq_of_decode?_eq_some_internal hdecode

/-- Decoding succeeds with a description exactly on that description's
fixed-width code. -/
theorem decode?_eq_some_iff
    {inputWidth gateBound : Nat}
    (code : BitString (codeWidth inputWidth gateBound))
    (description : Description inputWidth gateBound) :
    decode? code = some description ↔ code = encode description := by
  simpa [eq_comm] using decode?_eq_some_iff_internal code description

/-- Fixed-width bounded-description encoding is injective. -/
theorem encode_injective {inputWidth gateBound : Nat} :
    Function.Injective (@encode inputWidth gateBound) :=
  encode_injective_internal

end Description

end FixedWidth

end CircuitCode

end Complexity
