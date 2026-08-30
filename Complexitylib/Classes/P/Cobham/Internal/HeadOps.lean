/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.FPBridge

/-!
# Head-of-list operations in polynomial time

Three small string operations the `FP` toolkit uses constantly: reading the
head symbol (`Cobham.selectHead`), testing for the empty string (`emptyFlag`)
and dropping the first symbol (`dropOne`), each with its evaluation lemmas
and its `FP` membership.
-/

@[expose] public section

namespace Complexity
open Cobham

@[simp] theorem selectHead_cons_true (x y : List Bool) :
    Cobham.selectHead [true] x y = x := by
  rw [Cobham.selectHead]; simp

@[simp] theorem selectHead_cons_false (x y : List Bool) :
    Cobham.selectHead [false] x y = y := by
  rw [Cobham.selectHead]; simp

/-- Is the string empty, as a flag. -/
def emptyFlag (y : List Bool) : List Bool := lenLeFlag [] y

@[simp] theorem emptyFlag_nil : emptyFlag [] = [true] := rfl

theorem emptyFlag_cons (b : Bool) (y : List Bool) : emptyFlag (b :: y) = [false] := by
  rw [emptyFlag, lenLeFlag]
  simp [nonemptyFlag, notBit]

theorem emptyFlagFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => emptyFlag (a z)) ∈ FP :=
  lenLeFlagFn_mem_FP (constFn_mem_FP []) ha

/-- Drop the leading bit. -/
def dropOne (y : List Bool) : List Bool := y.drop 1

theorem dropOneFn_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => dropOne (a z)) ∈ FP := by
  have := dropLenFn_mem_FP (constFn_mem_FP [false]) ha
  simpa [dropOne] using this

end Complexity
