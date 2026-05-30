import Complexitylib.Models.TuringMachine
import Complexitylib.Models.TuringMachine.SingleTape.Internal
import Complexitylib.Asymptotics

/-!
# Multi-tape → single-tape simulation

A nondeterministic machine with `k` work tapes can be simulated by one with a
single work tape, preserving the decided language with only polynomial time
overhead (the classic `O(T²)` multi-tape-to-single-tape simulation).

This is a reusable robustness lemma:

* **Cook–Levin** (`SAT/CookLevin.lean`) uses it so the computation-tableau
  formula only has to track one work tape instead of `k`.
* **Universal machines** are far simpler to construct when they need only
  simulate a single-work-tape machine.

## Decomposition (leaves = `sorry`)

* `singleTapeSim N : NTM 1` — the simulating machine (definition to supply).
* `singleTapeSimTime T` — the `(T + n + 1)²` time overhead.
* `singleTapeSim_allPathsHaltIn`, `singleTapeSim_acceptsInTime_iff` — the two
  behavioural facts (timing + acceptance equivalence).
* `singleTapeSimTime_bigO` — the overhead stays polynomial.

`singleTapeSim_decides` and `exists_singleTape_decider` are assembled from these.
-/

open Complexity

namespace NTM

/-- The single-work-tape machine simulating the `k`-work-tape machine `N`
    (storing the `k` work tapes interleaved on one, with head markers).
    **Definition to be supplied.** -/
noncomputable def singleTapeSim {k : ℕ} (N : NTM k) : NTM 1 := sorry

/-- Time overhead of the single-tape simulation: the classic quadratic blow-up
    (plus a linear term to scan the input region). -/
def singleTapeSimTime (T : ℕ → ℕ) : ℕ → ℕ := fun n => (T n + n + 1) ^ 2

/-- The simulation's time overhead stays polynomial. -/
theorem singleTapeSimTime_bigO {T : ℕ → ℕ} {c : ℕ} (hTO : T =O (· ^ c)) :
    singleTapeSimTime T =O (· ^ (2 * c + 2)) := by
  -- `T n + n + 1` is `O(n^(c+1))`: each summand is.
  have hsum : (fun n => T n + n + 1) =O ((· ^ (c + 1)) : ℕ → ℕ) := by
    have hT : T =O ((· ^ (c + 1)) : ℕ → ℕ) :=
      hTO.trans (BigO.pow_le_pow_right (Nat.le_succ c))
    have hn : (fun n : ℕ => n) =O ((· ^ (c + 1)) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.pow_le_pow_right (j := 1) (k := c + 1) (by omega))
    exact BigO.add (BigO.add hT hn) (BigO.const_le_pow 1 (c + 1))
  -- Squaring stays polynomial: `(n^(c+1))² = n^(2c+2)`.
  have hmul : (fun n => (T n + n + 1) * (T n + n + 1))
      =O (fun n => n ^ (c + 1) * n ^ (c + 1)) := BigO.mul hsum hsum
  have hL : singleTapeSimTime T =O (fun n => (T n + n + 1) * (T n + n + 1)) :=
    BigO.of_le fun n => le_of_eq (by simp [singleTapeSimTime, pow_two])
  have hR : (fun n : ℕ => n ^ (c + 1) * n ^ (c + 1)) =O ((· ^ (2 * c + 2)) : ℕ → ℕ) :=
    BigO.of_le fun n => le_of_eq (by rw [← pow_add]; congr 1; omega)
  exact (hL.trans hmul).trans hR

/-- The simulator halts on all computation paths within the overhead time bound,
    whenever `N` does. -/
theorem singleTapeSim_allPathsHaltIn {k : ℕ} (N : NTM k) {T : ℕ → ℕ}
    (hN : N.AllPathsHaltIn T) :
    (singleTapeSim N).AllPathsHaltIn (singleTapeSimTime T) := by
  sorry

/-- The simulator accepts `x` within the overhead time bound iff `N` accepts `x`
    within its original time bound. -/
theorem singleTapeSim_acceptsInTime_iff {k : ℕ} (N : NTM k) (T : ℕ → ℕ) (x : List Bool) :
    (singleTapeSim N).AcceptsInTime x (singleTapeSimTime T x.length)
      ↔ N.AcceptsInTime x (T x.length) := by
  sorry

/-- The single-tape simulator decides the same language within the overhead time
    bound. -/
theorem singleTapeSim_decides {k : ℕ} {L : Language} (N : NTM k) {T : ℕ → ℕ}
    (hdec : N.DecidesInTime L T) :
    (singleTapeSim N).DecidesInTime L (singleTapeSimTime T) :=
  ⟨singleTapeSim_allPathsHaltIn N hdec.1,
    fun x => (hdec.2 x).trans (singleTapeSim_acceptsInTime_iff N T x).symm⟩

/-- **Single-tape reduction.** If `N` (with `k` work tapes) decides `L` within a
    polynomial time bound, then some single-work-tape machine `N'` decides the
    same `L` within a polynomial time bound. -/
theorem exists_singleTape_decider {k : ℕ} {L : Language} (N : NTM k)
    {T : ℕ → ℕ} {c : ℕ} (hdec : N.DecidesInTime L T) (hTO : T =O (· ^ c)) :
    ∃ (N' : NTM 1) (T' : ℕ → ℕ) (c' : ℕ), N'.DecidesInTime L T' ∧ T' =O (· ^ c') :=
  ⟨singleTapeSim N, singleTapeSimTime T, 2 * c + 2,
    singleTapeSim_decides N hdec, singleTapeSimTime_bigO hTO⟩

end NTM
