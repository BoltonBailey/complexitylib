/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BinaryComparison
public import Complexitylib.Circuits.Composition.Defs
public import Complexitylib.Circuits.InputProjection.Defs
public import Complexitylib.Circuits.Multiplexer.Defs

/-!
# Unsigned binary minimum -- definitions

The construction emits the comparator bit beside an unchanged copy of both
input words, then feeds that tuple to the fixed-width multiplexer.
-/


@[expose] public section

namespace Complexity

namespace BitString

/-- Select the word of smaller unsigned value, choosing the left word on ties. -/
def unsignedMin {width : ℕ} (left right : BitString width) : BitString width :=
  if left.unsignedValue ≤ right.unsignedValue then left else right

end BitString

namespace Circuit

/-- Comparator output followed by an unchanged copy of its two input words. -/
noncomputable def unsignedLEWithPayload (width : ℕ) [NeZero width] :
    Circuit Basis.andOr2 (width + width) (1 + (width + width))
      ((CircuitCode.unsignedLERawCircuit width).length - 1) :=
  (unsignedLE width).parallel
    (projectInputs (fun input : Fin (width + width) => input))

/-- Fan-in-two circuit selecting the unsigned minimum of two consecutive words. -/
noncomputable def unsignedMin (width : ℕ) [NeZero width] :
    Circuit Basis.andOr2 (width + width) width
      (((CircuitCode.unsignedLERawCircuit width).length - 1) +
        (1 + (width + width)) + (width + width)) :=
  (multiplexer width).compose (unsignedLEWithPayload width)

end Circuit

end Complexity
