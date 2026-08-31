/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputPairing.Defs
import Complexitylib.Circuits.InputSources

/-!
# Self-delimiting input-pair circuits -- proof internals
-/


public section

namespace Complexity

namespace Circuit

private theorem length_flatMap_duplicate {α : Type}
    (values : List α) :
    (values.flatMap (fun value => [value, value])).length =
      2 * values.length := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih]; omega

private theorem length_pairSourceList_internal
    {inputWidth leftWidth rightWidth : ℕ}
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth) :
    (pairSourceList left right).length =
      pairSourceWidth leftWidth rightWidth := by
  unfold pairSourceList pairSourceWidth
  rw [List.length_append, List.length_append, length_flatMap_duplicate]
  simp

private theorem map_flatMap_duplicate {α β : Type}
    (values : List α) (f : α → β) :
    (values.flatMap (fun value => [value, value])).map f =
      (values.map f).flatMap (fun value => [value, value]) := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih]

private theorem map_pairSourceList
    {inputWidth leftWidth rightWidth : ℕ}
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth)
    (input : BitString inputWidth) :
    (pairSourceList left right).map (fun source => source.eval input) =
      pair (BitString.toList (fun i => (left i).eval input))
        (BitString.toList (fun i => (right i).eval input)) := by
  unfold pairSourceList pair Complexity.delimit BitString.toList
  rw [List.map_append, List.map_append, map_flatMap_duplicate,
    List.map_ofFn, List.map_ofFn]
  rfl

theorem eval_pairInputSources_internal
    {inputWidth leftWidth rightWidth : ℕ}
    [NeZero inputWidth]
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth)
    (input : BitString inputWidth) :
    BitString.toList ((pairInputSources left right).eval input) =
      pair (BitString.toList (fun i => (left i).eval input))
        (BitString.toList (fun i => (right i).eval input)) := by
  rw [pairInputSources, eval_inputSources, BitString.toList]
  have hlist :
      List.ofFn
          (fun coordinate => (pairSources left right coordinate).eval input) =
        (pairSourceList left right).map (fun source => source.eval input) := by
    apply List.ext_get
    · simp [length_pairSourceList_internal]
    · intro index hleft hright
      simp [pairSources]
  rw [hlist, map_pairSourceList]

theorem size_pairInputSources_internal
    {inputWidth leftWidth rightWidth : ℕ}
    [NeZero inputWidth]
    (left : Fin leftWidth → InputSource inputWidth)
    (right : Fin rightWidth → InputSource inputWidth) :
    (pairInputSources left right).size =
      pairSourceWidth leftWidth rightWidth := by
  simp [pairInputSources]

end Circuit

end Complexity
