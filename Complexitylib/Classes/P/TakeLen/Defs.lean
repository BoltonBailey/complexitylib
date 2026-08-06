/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Encoding.Pairing

/-!
# Truncating to the length of a leading block — definition

`takeLen (pair c y) = y.take |c|`: the leading self-delimiting block acts as a
*ruler* and the verbatim suffix is truncated to its length. Carrying a width
bound as a string rather than as a number is what keeps an iterated `FP` step
function polynomial-time — each iteration truncates its state to the ruler, so
no intermediate value can grow beyond it.

## Main definitions

- `Complexity.takeLen` — truncate a pair's suffix to its leading block's length
- `Complexity.takeLen_pair` — its defining equation on genuine pairs
-/


@[expose] public section

namespace Complexity

/-! ## The function computed by the scanner -/

/-- The remaining output of the truncation scanner when `k` payload bits of the
leading block have already been counted and `w` is the unread part of the input:
the suffix truncated to the total ruler length, and nothing at all when the block
framing is broken. -/
def takeLenAux (k : ℕ) (w : List Bool) : List Bool :=
  match unpair? w with
  | some (x, y) => y.take (k + x.length)
  | none => []

/-- Truncate the verbatim suffix of a pair to the length of its leading block. -/
def takeLen (p : List Bool) : List Bool := takeLenAux 0 p

@[simp] theorem takeLenAux_nil (k : ℕ) : takeLenAux k [] = [] := rfl

@[simp] theorem takeLenAux_singleton (k : ℕ) (b : Bool) : takeLenAux k [b] = [] := by
  cases b <;> rfl

/-- Reaching the separator ends the ruler: the suffix is truncated to `k`. -/
@[simp] theorem takeLenAux_sep (k : ℕ) (z : List Bool) :
    takeLenAux k (false :: true :: z) = z.take k := by
  simp [takeLenAux, unpair?]

/-- A doubled payload bit lengthens the ruler by one. -/
theorem takeLenAux_double (k : ℕ) (b : Bool) (z : List Bool) :
    takeLenAux k (b :: b :: z) = takeLenAux (k + 1) z := by
  cases b <;>
    · simp only [takeLenAux, unpair?]
      cases h : unpair? z with
      | none => simp
      | some xy =>
          obtain ⟨x, y⟩ := xy
          simp only [Option.map_some, List.length_cons]
          rw [show k + (x.length + 1) = k + 1 + x.length from by omega]

/-- A broken doubling halts the scan with no output. -/
@[simp] theorem takeLenAux_broken (k : ℕ) (z : List Bool) :
    takeLenAux k (true :: false :: z) = [] := rfl

/-- On a genuine pair the leading block is the ruler. -/
theorem takeLen_pair (c y : List Bool) : takeLen (pair c y) = y.take c.length := by
  simp [takeLen, takeLenAux, pair]

end Complexity
