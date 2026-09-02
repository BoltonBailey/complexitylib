/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FinalScan

/-!
# Delimiting a scan by a marker register instead of by a counter

⚠️ Unreviewed by Bolton

`Complexity.Scanner.upTo` and `Complexity.Scanner.after` delimit a check by *counting* cells,
and they pay for it in the automaton's state: `upTo w` carries a `Fin (w + 1)`. Where the width
is a constant that is fine, but the code layout's widths grow with the space window, so a check
restricted to a code block has a state space that grows with the input — and a machine built
from such a check is a *family* indexed by the input length, not the single machine that a
complexity class asks for.

This file supplies the counter-free alternative. `Complexity.Scanner.gate` runs a check exactly
on the columns where a designated *marker register* carries a designated symbol, and carries no
state of its own beyond the check's: gating a constant-state check leaves it constant-state. A
marker register whose content is pinned by the machine (rather than guessed) therefore delimits
any range a counter could, at no cost in states.

The results here are about scans alone; putting a pinned marker register into the walk's layout
is a separate step.

## Main definitions

- `Complexity.Scanner.gate` — run a check only on the marked columns

## Main results

- `Complexity.Scanner.gate_emit_run` — a gated check reads exactly the marked range
- `Complexity.Scanner.eq_gate_run` — the equality check, delimited without a counter
- `Complexity.Scanner.gate_sigma_eq` — gating does not touch the state space
-/

@[expose] public section

namespace Complexity

namespace Scanner

variable {j : ℕ}

/-- **A check delimited by a marker.** The check advances only on the columns whose marker
register carries `g`; elsewhere the state stands still. -/
def gate (S : Scanner j) (mk : Fin (j + 1)) (g : Γ) : Scanner j where
  σ := S.σ
  decEqσ := S.decEqσ
  finσ := S.finσ
  start := S.start
  stepR s col := if col mk = g then S.stepR s col else s
  stepL s col := if col mk = g then S.stepL s col else s
  emit := S.emit

/-- **Gating costs no states.** The gated check's state space is the check's own — this is what
`Complexity.Scanner.upTo` cannot say, and the whole point of the construction. -/
theorem gate_sigma_eq (S : Scanner j) (mk : Fin (j + 1)) (g : Γ) : (S.gate mk g).σ = S.σ := rfl

theorem rightOnly_gate {S : Scanner j} (hS : RightOnly S) (mk : Fin (j + 1)) (g : Γ) :
    RightOnly (S.gate mk g) := by
  intro s col
  show (if col mk = g then S.stepL s col else s) = s
  split
  · exact hS s col
  · rfl

/-- **What a gated pass reads.** With the marker on exactly the columns `a + 1 … a + w`, the
gated pass has read precisely the first `min (p - a) w` of them. -/
theorem gate_runR (S : Scanner j) (mk : Fin (j + 1)) (g : Γ)
    (cols : ℕ → Fin (j + 1) → Γ) (a w : ℕ)
    (hlo : ∀ q, 1 ≤ q → q ≤ a → cols q mk ≠ g)
    (hin : ∀ q, a < q → q ≤ a + w → cols q mk = g)
    (hhi : ∀ q, a + w < q → cols q mk ≠ g) :
    ∀ p, (S.gate mk g).runR cols p
      = S.runR (fun q => cols (a + q)) (min (p - a) w) := by
  intro p
  induction p with
  | zero =>
      show S.start = _
      rw [show min (0 - a) w = 0 by omega]
      rfl
  | succ p ih =>
      rw [runR]
      show (if cols (p + 1) mk = g then S.stepR ((S.gate mk g).runR cols p) (cols (p + 1))
        else (S.gate mk g).runR cols p) = _
      by_cases hmark : cols (p + 1) mk = g
      · -- a marked column: it is inside the range, so both sides advance
        have hgt : a < p + 1 := by
          by_contra hle
          exact hlo (p + 1) (by omega) (by omega) hmark
        have hle : p + 1 ≤ a + w := by
          by_contra hgt'
          exact hhi (p + 1) (by omega) hmark
        rw [if_pos hmark, ih, show min (p + 1 - a) w = min (p - a) w + 1 by omega,
          runR, show min (p - a) w + 1 = p + 1 - a by omega,
          show a + (p + 1 - a) = p + 1 by omega]
      · -- an unmarked column: it is outside the range, so neither side advances
        have hout : p + 1 ≤ a ∨ a + w < p + 1 := by
          by_contra hcon
          exact hmark (hin (p + 1) (by omega) (by omega))
        rw [if_neg hmark, ih]
        congr 1
        rcases hout with h | h <;> omega

/-- **A gated check reads exactly the marked range**, the counter-free counterpart of
`Complexity.Scanner.range_emit_run`. -/
theorem gate_emit_run {S : Scanner j} (hS : RightOnly S) (mk : Fin (j + 1)) (g : Γ)
    (cols : ℕ → Fin (j + 1) → Γ) (a w len : ℕ) (hlen : a + w ≤ len)
    (hlo : ∀ q, 1 ≤ q → q ≤ a → cols q mk ≠ g)
    (hin : ∀ q, a < q → q ≤ a + w → cols q mk = g)
    (hhi : ∀ q, a + w < q → cols q mk ≠ g) :
    (S.gate mk g).emit ((S.gate mk g).run cols len)
      = S.emit (S.run (fun q => cols (a + q)) w) := by
  rw [run, runL_of_rightOnly (rightOnly_gate hS mk g), run, runL_of_rightOnly hS,
    gate_runR S mk g cols a w hlo hin hhi len, show min (len - a) w = w by omega]
  rfl

/-- **The equality check, delimited without a counter.** Compare
`Complexity.Scanner.eq_range_run`: the same verdict, from an automaton whose state space is
`Bool` however wide the range is. -/
theorem eq_gate_run (a b mk : Fin (j + 1)) (g : Γ) (cols : ℕ → Fin (j + 1) → Γ)
    (off w len : ℕ) (hlen : off + w ≤ len)
    (hlo : ∀ q, 1 ≤ q → q ≤ off → cols q mk ≠ g)
    (hin : ∀ q, off < q → q ≤ off + w → cols q mk = g)
    (hhi : ∀ q, off + w < q → cols q mk ≠ g) :
    ((eq j a b).gate mk g).emit (((eq j a b).gate mk g).run cols len) = true ↔
      ∀ q, off < q → q ≤ off + w → cols q a = cols q b := by
  rw [gate_emit_run (rightOnly_eq j a b) mk g cols off w len hlen hlo hin hhi]
  show (eq j a b).run (fun q => cols (off + q)) w = true ↔ _
  rw [eq_run]
  constructor
  · intro h q h1 h2
    have := h (q - off) (by omega) (by omega)
    rwa [show off + (q - off) = q by omega] at this
  · intro h q h1 h2
    exact h (off + q) (by omega) (by omega)

/-- The gated equality check really does carry only a bit of state, whatever the range. -/
example (a b mk : Fin (j + 1)) (g : Γ) : ((eq j a b).gate mk g).σ = Bool := rfl

end Scanner

end Complexity
