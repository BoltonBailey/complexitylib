/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Init
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Widget.Calc
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Self-delimiting blocks

To concatenate binary strings into a single binary string, each piece must announce its own
end. This file defines the library's single framing operation and its parser:

- `delimit` frames a payload: each payload bit is doubled (`false ↦ [false, false]`,
  `true ↦ [true, true]`) and the block is terminated by the separator `[false, true]`,
  which no run of doubled bits can produce.
- `unpair?` parses one block off the front of the input, returning the payload and the
  remaining suffix (`none` on malformed input). It is named for its role in the pairing
  codec `Complexity.pair` (see `Complexitylib.Encoding.Pairing`), which is
  `pair x y = delimit x ++ y`.

This file deliberately has no dependency on the machine or complexity-class layers, so the
pairing codec can build on it without introducing an import cycle.
-/


@[expose] public section

namespace Complexity

/-- Frame a binary string as a self-delimiting block: each payload bit is doubled
    (`false ↦ [false, false]`, `true ↦ [true, true]`) and the block is terminated by the
    separator `[false, true]`, which no run of doubled bits can produce. -/
def delimit (x : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true]

@[simp] theorem delimit_nil : delimit [] = [false, true] := rfl

@[simp] theorem delimit_cons (b : Bool) (l : List Bool) :
    delimit (b :: l) = b :: b :: delimit l := by
  simp [delimit]

@[simp] theorem delimit_length (l : List Bool) : (delimit l).length = 2 * l.length + 2 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [delimit_cons, List.length_cons, ih]; omega

/-- Parse one self-delimiting block off the front of the input. It scans doubled bits until
    the first separator `[false, true]`, returning the decoded payload together with the
    remaining suffix. Invalid doubled prefixes return `none`. -/
def unpair? : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: true :: y => some ([], y)
  | false :: false :: z =>
      Option.map (fun (xy : List Bool × List Bool) => (false :: xy.1, xy.2)) (unpair? z)
  | true :: true :: z =>
      Option.map (fun (xy : List Bool × List Bool) => (true :: xy.1, xy.2)) (unpair? z)
  | _ => none

/-- `unpair?` reads back the framing written by `delimit`: parsing one block off the front
    of any input recovers the payload and the remaining suffix. -/
@[simp] theorem unpair?_delimit_append (x y : List Bool) :
    unpair? (delimit x ++ y) = some (x, y) := by
  induction x with
  | nil => simp [unpair?]
  | cons b x ih => cases b <;> simp [unpair?, ih]

/-- Soundness of the parser: a successful parse decomposes the input as the parsed payload's
    framing followed by the leftover suffix. -/
theorem eq_delimit_append_of_unpair?_eq_some :
    ∀ {z x y : List Bool}, unpair? z = some (x, y) → z = delimit x ++ y
  | [], _, _, h => by simp [unpair?] at h
  | [b], _, _, h => by cases b <;> simp [unpair?] at h
  | false :: true :: rest, x, y, h => by
    simp only [unpair?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | false :: false :: rest, x, y, h => by
    simp only [unpair?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p₁, p₂⟩, hp, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : false :: p₁ = x ∧ p₂ = y := by simpa [Prod.ext_iff] using heq
    simp only [eq_delimit_append_of_unpair?_eq_some hp, delimit_cons, List.cons_append]
  | true :: true :: rest, x, y, h => by
    simp only [unpair?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p₁, p₂⟩, hp, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : true :: p₁ = x ∧ p₂ = y := by simpa [Prod.ext_iff] using heq
    simp only [eq_delimit_append_of_unpair?_eq_some hp, delimit_cons, List.cons_append]
  | true :: false :: rest, _, _, h => by simp [unpair?] at h

end Complexity
