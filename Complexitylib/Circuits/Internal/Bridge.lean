/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Internal.CircuitToDescriptor
import Complexitylib.Circuits.Internal.Schnorr

/-! # Internal: Bridge from CircDesc to Circuit Model

This internal module uses the faithful `Circuit`-to-`CircDesc` encoding to
transfer descriptor padding and lower bounds to the typed circuit model.

The public theorems `shannon_lower_bound_circuit` and
`schnorr_lower_bound_circuit` are accessible through
`Complexitylib.Circuits.Shannon` and `Complexitylib.Circuits.Schnorr` respectively.
-/

namespace Complexity

open CircDesc

/-! ## Padding -/

/-- Pad a descriptor to a larger size by appending copy gates.
    Each padded gate is `OR(last_output, last_output)` which copies the
    original output value. -/
def padDesc {N s : Nat} (d : CircDesc N s) (s' : Nat) (hs : 0 < s) (h : s ≤ s') :
    CircDesc N s' := fun i =>
  if hi : i.val < s then
    let slot := d ⟨i.val, hi⟩
    (slot.1,
     (⟨slot.2.1.1.val, by omega⟩, ⟨slot.2.1.2.val, by omega⟩),
     slot.2.2)
  else
    -- Copy gate: OR(last_original_output, last_original_output)
    (false, (⟨N + s - 1, by omega⟩, ⟨N + s - 1, by omega⟩), (false, false))

-- Helper: wireVal agrees on original wires
private theorem wireVal_padDesc_lt {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (x : BitString N) (w : Fin (N + s')) (hw : w.val < N + s) :
    wireVal (padDesc d s' hs h) x w =
      wireVal d x ⟨w.val, hw⟩ := by
  by_cases hwN : w.val < N
  · simp [wireVal, hwN]
  · push Not at hwN
    have hi : w.val - N < s := by omega
    conv_lhs => unfold wireVal
    simp only [show ¬(w.val < N) from by omega, dite_false]
    conv_rhs => unfold wireVal
    simp only [show ¬(w.val < N) from by omega, dite_false]
    -- Both sides look up the gate at index w.val - N
    simp only [padDesc, show (w.val - N) < s from hi, dite_true]
    have hw1 : (d ⟨↑w - N, hi⟩).2.1.1.val < N + s := (d ⟨↑w - N, hi⟩).2.1.1.isLt
    have hw2 : (d ⟨↑w - N, hi⟩).2.1.2.val < N + s := (d ⟨↑w - N, hi⟩).2.1.2.isLt
    congr 1 <;> (congr 1 <;> (first | rfl | (congr 1; split_ifs with hlt <;> (
      first
      | exact wireVal_padDesc_lt d hs h x _ (by first | exact hw1 | exact hw2)
      | rfl))))
  termination_by w.val

-- Helper: padded wire values equal the last original output
private theorem wireVal_padDesc_ge {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (x : BitString N) (w : Fin (N + s')) (hw : N + s ≤ w.val) :
    wireVal (padDesc d s' hs h) x w =
      wireVal d x ⟨N + s - 1, by omega⟩ := by
  conv_lhs => unfold wireVal
  simp only [show ¬(w.val < N) from by omega, dite_false]
  -- The gate at index w.val - N ≥ s, so padDesc gives the copy gate
  simp only [padDesc, show ¬(w.val - N < s) from by omega, dite_false]
  -- Copy gate: OR(N+s-1, N+s-1) with no negation
  simp only [Bool.false_xor, Bool.or_self]
  -- The wire N+s-1 < w, so the guard passes
  simp only [show (N + s - 1 : Nat) < w.val from by omega, ↓reduceIte]
  -- Now we need wireVal (padDesc ...) x ⟨N+s-1, _⟩ = wireVal d x ⟨N+s-1, _⟩
  have hlt : N + s - 1 < N + s := by omega
  exact wireVal_padDesc_lt d hs h x ⟨N + s - 1, by omega⟩ hlt

/-- Padding preserves evaluation. -/
theorem eval_padDesc {N s s' : Nat} (d : CircDesc N s) (hs : 0 < s)
    (h : s ≤ s') (hs' : 0 < s') :
    eval hs' (padDesc d s' hs h) = eval hs d := by
  funext x
  simp only [eval]
  by_cases hsle : N + s ≤ N + s' - 1
  · -- s < s': the last wire is in the padded region
    rw [wireVal_padDesc_ge d hs h x ⟨N + s' - 1, by omega⟩ (by omega)]
  · -- s = s': both point to the same wire
    push Not at hsle
    have : s = s' := by omega
    subst this
    exact wireVal_padDesc_lt d hs h x ⟨N + s - 1, by omega⟩ (by omega)

/-! ## Main Theorems -/

/-- **Shannon lower bound for circuits**: for N ≥ 6, there exists a Boolean
    function on N inputs that cannot be computed by any fan-in-2 AND/OR
    circuit of size at most 2^N/(5N). -/
theorem shannon_lower_bound_circuit (N : Nat) [NeZero N] (hN : 6 ≤ N) :
    ∃ f : BitString N → Bool,
      ∀ G (c : Circuit Basis.andOr2 N 1 G),
        G + 1 ≤ 2 ^ N / (5 * N) →
        (fun x => (c.eval x) 0) ≠ f := by
  obtain ⟨f, hf⟩ := shannon_lower_bound N hN
  exact ⟨f, fun G c hsize habs => by
    have hspos := s_pos N hN
    have hG1 : 0 < G + 1 := Nat.succ_pos G
    let d := circuitToDesc c
    let d' := padDesc d (2 ^ N / (5 * N)) hG1 hsize
    have h1 : eval hspos d' = eval hG1 d := eval_padDesc d hG1 hsize hspos
    have h2 : (fun x => (c.eval x) 0) = eval hG1 d := circuit_eval_eq_eval c
    have h3 : eval hspos d' = f := by rw [h1, ← h2, habs]
    exact hf d' h3⟩

/-- **Schnorr's lower bound for circuits**: any fan-in-2 AND/OR circuit
    computing XOR_N (or its complement) has at least 2(N-1) internal gates,
    i.e., G + 1 (total gates including output) ≥ 2N - 1. -/
theorem schnorr_lower_bound_circuit (N G : Nat) [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (comp : Bool)
    (heval : ∀ x, (c.eval x) 0 = comp.xor (Schnorr.xorBool N x))
    (hN : 1 ≤ N) : G + 2 ≥ 2 * N := by
  have hG1 : 0 < G + 1 := Nat.succ_pos G
  have h := circuit_eval_eq_eval c
  have heval' : ∀ x, eval hG1 (circuitToDesc c) x = comp.xor (Schnorr.xorBool N x) :=
    fun x => (congr_fun h x).symm ▸ heval x
  exact Schnorr.xor_lower_bound_2 N (G + 1) hG1 (circuitToDesc c) comp heval' hN

end Complexity
