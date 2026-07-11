/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Lemma

/-!
# Fixed-width binary encodings of natural numbers

Big-endian, fixed-width binary encoding `Nat.toBits` with its exact decoder
`Nat.fromBits` and round-trip lemmas. Values wider than the target width are
truncated modulo `2 ^ w`.

This file lives in `Complexitylib/Mathlib/` because it extends a Mathlib
type in its home (root) namespace — the sanctioned exception to the
`Complexity` root-namespace rule. Its contents are candidates for
upstreaming to Mathlib.
-/

/-- Encode a natural number as a big-endian binary list of exactly `w` bits.
    Numbers larger than `2^w - 1` are truncated (mod 2^w). -/
def Nat.toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, val => (val / 2 ^ w % 2 == 1) :: Nat.toBits w val

theorem Nat.length_toBits : ∀ (w val : ℕ), (Nat.toBits w val).length = w
  | 0, _ => rfl
  | w + 1, val => by simp [Nat.toBits, Nat.length_toBits w]

/-- Decode a big-endian binary list to a natural number. -/
def Nat.fromBits : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) * 2 ^ rest.length + Nat.fromBits rest

/-- Decoded values are bounded by `2 ^ length`. -/
theorem Nat.fromBits_lt_pow_length : ∀ (l : List Bool), Nat.fromBits l < 2 ^ l.length
  | [] => by simp [Nat.fromBits]
  | b :: rest => by
    have ih := Nat.fromBits_lt_pow_length rest
    simp only [Nat.fromBits, List.length_cons, pow_succ]
    rcases b with _ | _ <;> simp <;> omega

/-- `fromBits ∘ toBits w` reduces any input modulo `2 ^ w`. -/
theorem Nat.fromBits_toBits_mod : ∀ (w val : ℕ),
    Nat.fromBits (Nat.toBits w val) = val % 2 ^ w
  | 0, val => by simp [Nat.toBits, Nat.fromBits, Nat.mod_one]
  | w + 1, val => by
    have ih := Nat.fromBits_toBits_mod w val
    simp only [Nat.toBits, Nat.fromBits, Nat.length_toBits, ih]
    have hbit : (val / 2 ^ w) % 2 = if (val / 2 ^ w % 2 == 1) then 1 else 0 := by
      rcases Nat.mod_two_eq_zero_or_one (val / 2 ^ w) with h | h <;> simp [h]
    have hpow : (2 : ℕ) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
    have hkey : val % 2 ^ (w + 1) = (val / 2 ^ w) % 2 * 2 ^ w + val % 2 ^ w := by
      rw [hpow, Nat.mod_mul, Nat.mul_comm (2^w) _, Nat.add_comm]
    rw [hkey, ← hbit]

/-- `Nat.fromBits` is a left inverse of `Nat.toBits` on values below `2 ^ w`. -/
theorem Nat.fromBits_toBits {w val : ℕ} (hv : val < 2 ^ w) :
    Nat.fromBits (Nat.toBits w val) = val := by
  rw [Nat.fromBits_toBits_mod, Nat.mod_eq_of_lt hv]
