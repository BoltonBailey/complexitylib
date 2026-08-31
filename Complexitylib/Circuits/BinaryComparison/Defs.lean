/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.Encoding.Formula.Defs
public import Complexitylib.Mathlib.NatBits

/-!
# Little-endian binary comparison -- definitions

This module defines unsigned interpretation and comparison for fixed-width
little-endian bit strings, together with a linear-size Boolean formula for the
comparison. The two input words occupy consecutive variable blocks.
-/


@[expose] public section

namespace Complexity

namespace BitString

/-- Interpret a fixed-width bit string as an unsigned little-endian natural. -/
def unsignedValue {width : ℕ} (bits : BitString width) : ℕ :=
  Nat.fromBitsLE bits.toList

/-- Compare two equally wide little-endian words from their most significant
bits downward. -/
def unsignedLE : {width : ℕ} → BitString width → BitString width → Bool
  | 0, _, _ => true
  | width + 1, left, right =>
      let leftHigh := left (Fin.last width)
      let rightHigh := right (Fin.last width)
      (!leftHigh && rightHigh) ||
        ((leftHigh == rightHigh) &&
          unsignedLE (fun i => left i.castSucc)
            (fun i => right i.castSucc))

end BitString

namespace BoolFormula

/-- Embed one Boolean value as a constant formula leaf. -/
def ofBool : Bool → BoolFormula
  | false => .fls
  | true => .tru

/-- Compare two fixed-width vectors of Boolean formulas as little-endian
unsigned words. This general form supports variables, constants, and later
compiled wire layouts without changing the comparator tree. -/
def unsignedLEOf : {width : ℕ} →
    (Fin width → BoolFormula) → (Fin width → BoolFormula) → BoolFormula
  | 0, _, _ => .tru
  | width + 1, left, right =>
      let leftHigh := left (Fin.last width)
      let rightHigh := right (Fin.last width)
      let lessHigh := .conj (.neg leftHigh) rightHigh
      let equalHigh := .disj (.conj leftHigh rightHigh)
        (.conj (.neg leftHigh) (.neg rightHigh))
      .disj lessHigh
        (.conj equalHigh
          (unsignedLEOf (fun i => left i.castSucc)
            (fun i => right i.castSucc)))

/-- Compare a constant left word with a variable block beginning at
`rightBase`. -/
def unsignedLELeftConstant {width : ℕ} (left : BitString width)
    (rightBase : ℕ) : BoolFormula :=
  unsignedLEOf (fun i => ofBool (left i))
    (fun i => .var (rightBase + i.val))

/-- Compare a variable block beginning at `leftBase` with a constant right
word. -/
def unsignedLERightConstant {width : ℕ} (leftBase : ℕ)
    (right : BitString width) : BoolFormula :=
  unsignedLEOf (fun i => .var (leftBase + i.val))
    (fun i => ofBool (right i))

/-- Formula for unsigned comparison of two `width`-bit words beginning at the
given variable bases. -/
def unsignedLEAux : (width leftBase rightBase : ℕ) → BoolFormula
  | 0, _, _ => .tru
  | width + 1, leftBase, rightBase =>
      let leftHigh := .var (leftBase + width)
      let rightHigh := .var (rightBase + width)
      let lessHigh := .conj (.neg leftHigh) rightHigh
      let equalHigh := .disj (.conj leftHigh rightHigh)
        (.conj (.neg leftHigh) (.neg rightHigh))
      .disj lessHigh
        (.conj equalHigh (unsignedLEAux width leftBase rightBase))

/-- Formula comparing the first `width` input variables with the next `width`
variables as unsigned little-endian words. -/
def unsignedLE (width : ℕ) : BoolFormula :=
  unsignedLEAux width 0 width

end BoolFormula

namespace CircuitCode

/-- Raw fan-in-two circuit comparing two consecutive `width`-bit unsigned
little-endian words. -/
def unsignedLERawCircuit (width : ℕ) : RawCircuit :=
  BoolFormula.compileRaw (width + width) (BoolFormula.unsignedLE width)

end CircuitCode

end Complexity
