/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.BitString
public import Complexitylib.Circuits.InputSources.Defs
public import Complexitylib.Encoding.Pairing

/-!
# Self-delimiting input-pair circuits -- definitions

This module materializes the library's list-level pairing codec from Boolean
constants and selected primary inputs. The resulting circuit can feed a fixed
serialized query directly into another circuit.
-/


@[expose] public section

namespace Complexity

namespace Circuit

/-- Width of `pair left right` when the two payload widths are fixed. -/
def pairSourceWidth (leftWidth rightWidth : ℕ) : ℕ :=
  2 * leftWidth + 2 + rightWidth

instance (leftWidth rightWidth : ℕ) :
    NeZero (pairSourceWidth leftWidth rightWidth) :=
  ⟨by simp [pairSourceWidth]⟩

/-- Source list for the self-delimiting pair: duplicate the left sources,
write the `01` separator, then copy the right sources verbatim. -/
def pairSourceList {inputWidth leftWidth rightWidth : ℕ}
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth) :
    List (InputSource inputWidth) :=
  (List.ofFn left).flatMap (fun source => [source, source]) ++
    [.constant false, .constant true] ++ List.ofFn right

private theorem length_flatMap_duplicate {α : Type}
    (values : List α) :
    (values.flatMap (fun value => [value, value])).length =
      2 * values.length := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih]; omega

private theorem length_pairSourceList
    {inputWidth leftWidth rightWidth : ℕ}
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth) :
    (pairSourceList left right).length =
      pairSourceWidth leftWidth rightWidth := by
  unfold pairSourceList pairSourceWidth
  rw [List.length_append, List.length_append, length_flatMap_duplicate]
  simp

/-- Fixed-width tuple of input sources spelling one self-delimiting pair. -/
def pairSources {inputWidth leftWidth rightWidth : ℕ}
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth) :
    Fin (pairSourceWidth leftWidth rightWidth) → InputSource inputWidth :=
  fun coordinate => (pairSourceList left right)[coordinate.val]'(by
    rw [length_pairSourceList]
    exact coordinate.isLt)

/-- Zero-internal-gate circuit materializing one self-delimiting pair. -/
def pairInputSources {inputWidth leftWidth rightWidth : ℕ}
    [NeZero inputWidth]
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth) :
    Circuit Basis.andOr2 inputWidth (pairSourceWidth leftWidth rightWidth) 0 :=
  inputSources (pairSources left right)

end Circuit

end Complexity
