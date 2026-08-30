/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Mathlib.Data.Nat.Bits
public import Complexitylib.Classes.P.Cobham

/-!
# Bounded binary values

`binValLE` reads a bit list as a binary number capped at a length bound, and
`bitsOfLenLE` is its inverse on the range: the fixed-width binary expansion of a
number. Together they enumerate the `2 ^ n` strings of length `n` by number,
which is how the PCP verifier's coin tosses are indexed.

## Main definitions

- `binValLE`, `bitsOfLenLE` — the value of a bit list, and the bits of a value
- `binValLE_bitsOfLenLE`, `bitsOfLenLE_binValLE` — the two round trips
-/

@[expose] public section

namespace Complexity

/-- The little-endian value of a bitstring. -/
def binValLE : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then 1 else 0) + 2 * binValLE w

/-- The little-endian bitstring of a given length and value. -/
def bitsOfLenLE : ℕ → ℕ → List Bool
  | 0, _ => []
  | ℓ + 1, v => decide (v % 2 = 1) :: bitsOfLenLE ℓ (v / 2)

@[simp] theorem bitsOfLenLE_length (ℓ v : ℕ) : (bitsOfLenLE ℓ v).length = ℓ := by
  induction ℓ generalizing v with
  | zero => rfl
  | succ ℓ ih => simp [bitsOfLenLE, ih]

theorem binValLE_lt (w : List Bool) : binValLE w < 2 ^ w.length := by
  induction w with
  | nil => simp [binValLE]
  | cons b w ih =>
      simp only [binValLE, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

/-- The round trip, one way. -/
theorem bitsOfLenLE_binValLE (w : List Bool) : bitsOfLenLE w.length (binValLE w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      have hmod : binValLE (b :: w) % 2 = if b then 1 else 0 := by
        simp only [binValLE]
        cases b <;> simp [Nat.add_mul_mod_self_left]
      have hdiv : binValLE (b :: w) / 2 = binValLE w := by
        simp only [binValLE]
        cases b <;> simp [Nat.add_mul_div_left]
      simp only [bitsOfLenLE, hmod, hdiv, ih]
      cases b <;> simp

/-- The round trip, the other way. -/
theorem binValLE_bitsOfLenLE : ∀ (ℓ v : ℕ), v < 2 ^ ℓ → binValLE (bitsOfLenLE ℓ v) = v := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro v hv
      simp only [pow_zero] at hv
      simp [bitsOfLenLE, binValLE]
      omega
  | succ ℓ ih =>
      intro v hv
      have hhalf : v / 2 < 2 ^ ℓ := by
        have : (2 : ℕ) ^ (ℓ + 1) = 2 ^ ℓ * 2 := by ring
        omega
      have hdm : 2 * (v / 2) + v % 2 = v := by omega
      simp only [bitsOfLenLE, binValLE, ih _ hhalf]
      by_cases hb : v % 2 = 1
      · simp [hb]
        omega
      · simp [hb]
        omega

/-- **Each bit of the enumeration is a bit of the counter.** The `j`-th entry of the length-`ℓ`
little-endian string for `v` is bit `j` of `v`. This is the form in which the correspondence meets
a tape: whatever encoding a counter tape uses, its `j`-th cell holds this bit — and cells beyond
the counter's own digits read as `false`, which is bit `j` of `v` too. -/
theorem bitsOfLenLE_getElem :
    ∀ (ℓ v j : ℕ) (h : j < ℓ), (bitsOfLenLE ℓ v)[j]'(by simpa using h)
      = decide (v / 2 ^ j % 2 = 1) := by
  intro ℓ
  induction ℓ with
  | zero => intro v j h; omega
  | succ ℓ ih =>
      intro v j h
      cases j with
      | zero => simp [bitsOfLenLE]
      | succ j =>
          have hj : j < ℓ := by omega
          have hstep := ih (v / 2) j hj
          simp only [bitsOfLenLE, List.getElem_cons_succ]
          rw [hstep, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-- **The canonical representation reads back as its value.** -/
theorem binValLE_bits : ∀ n : ℕ, binValLE n.bits = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n, ih with
      | 0, _ => rfl
      | (m + 1), ih =>
          rcases Nat.even_or_odd (m + 1) with ⟨q, hq⟩ | ⟨q, hq⟩
          · have hq0 : q ≠ 0 := by omega
            have h2 : m + 1 = 2 * q := by omega
            rw [h2, Nat.bit0_bits q hq0, binValLE, ih q (by omega)]
            simp
          · have h2 : m + 1 = 2 * q + 1 := by omega
            rw [h2, Nat.bit1_bits q, binValLE, ih q (by omega)]
            simp
            omega

theorem bitsOfLenLE_zero (ℓ : ℕ) : bitsOfLenLE ℓ 0 = List.replicate ℓ false := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih => rw [bitsOfLenLE, ih, List.replicate_succ]; simp

end Complexity
