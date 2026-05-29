import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics

/-!
# Multi-tape → single-tape simulation

A nondeterministic machine with `k` work tapes can be simulated by one with a
single work tape, preserving the decided language with only polynomial time
overhead (the classic `O(T²)` multi-tape-to-single-tape simulation, here phrased
at the level of "decides the same language in polynomial time").

This is a reusable robustness lemma:

* **Cook–Levin** (`SAT/CookLevin.lean`) uses it so the computation-tableau
  formula only has to track one work tape instead of `k`.
* **Universal machines** are far simpler to construct when they need only
  simulate a single-work-tape machine.
-/

open Complexity

namespace NTM

/-- **Single-tape reduction.** If `N` (with `k` work tapes) decides `L` within a
    polynomial time bound, then some single-work-tape machine `N'` decides the
    same `L` within a polynomial time bound. -/
theorem exists_singleTape_decider {k : ℕ} {L : Language} (N : NTM k)
    {T : ℕ → ℕ} {c : ℕ} (hdec : N.DecidesInTime L T) (hTO : T =O (· ^ c)) :
    ∃ (N' : NTM 1) (T' : ℕ → ℕ) (c' : ℕ), N'.DecidesInTime L T' ∧ T' =O (· ^ c') := by
  sorry

end NTM
