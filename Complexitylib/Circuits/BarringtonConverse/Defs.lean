/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonFamily
import Mathlib.Data.List.OfFn

/-!
# The converse direction of Barrington's theorem -- definitions

This file defines balanced Boolean formulas for evaluating permutation branching
programs. A depth parameter `d` describes a block of at most `2 ^ d`
instructions. Two half-blocks are composed by existentially selecting their
intermediate state.

It also fixes the semantic family classes used by the nonuniform Barrington
equivalence. They follow the existing Barrington convention: formulas and
programs are evaluated on total assignments `ℕ → Bool`, while the family index
records the input-length parameter controlling depth and program length.
-/

namespace Complexity

namespace BoolFormula

/-- Disjoin a list of Boolean formulas. The empty disjunction is false. -/
def disjoin : List BoolFormula → BoolFormula
  | [] => .fls
  | φ :: fs => .disj φ (disjoin fs)

end BoolFormula

namespace BPInstr

/-- A formula saying that this instruction maps state `x` to state `y`. -/
def reachesFormula {w : ℕ} (ins : BPInstr w) (x y : Fin w) : BoolFormula :=
  if ins.perm0 x = y then
    if ins.perm1 x = y then .tru else .neg (.var ins.var)
  else if ins.perm1 x = y then .var ins.var else .fls

end BPInstr

namespace BP

/-- A balanced formula saying that a program block maps state `x` to state `y`.

At depth zero the formula reads the first instruction, if present. At depth
`d + 1` it splits after `2 ^ d` instructions and disjoins over every possible
intermediate state. Its semantic theorem assumes `p.length ≤ 2 ^ d`. -/
def reachesFormula {w : ℕ} : ℕ → BP w → Fin w → Fin w → BoolFormula
  | 0, [], x, y => if x = y then .tru else .fls
  | 0, ins :: _, x, y => ins.reachesFormula x y
  | d + 1, p, x, y =>
      BoolFormula.disjoin (List.ofFn fun z : Fin w =>
        .conj (reachesFormula d (p.take (2 ^ d)) z y)
          (reachesFormula d (p.drop (2 ^ d)) x z))

/-- The canonical balanced formula deciding whether `p` moves the query point
`x`. Its recursion depth is the least `d` with `p.length ≤ 2 ^ d`. -/
def decisionFormula {w : ℕ} (p : BP w) (x : Fin w) : BoolFormula :=
  .neg (reachesFormula (Nat.clog 2 p.length) p x x)

end BP

/-- A family of width-`w` permutation branching programs. -/
def BPFamily (w : ℕ) := ℕ → BP w

namespace BPFamily

/-- A branching-program family has polynomial length. -/
def PolynomialLength {w : ℕ} (R : BPFamily w) : Prop :=
  ∃ C p, ∀ n, (R n).length ≤ C * (n + 1) ^ p

/-- A branching-program family decides `f` by whether its designated query point
is moved by the evaluated permutation. -/
def Decides {w : ℕ} (R : BPFamily w) (x : ℕ → Fin w)
    (f : ℕ → (ℕ → Bool) → Bool) : Prop :=
  ∀ n α, (BP.eval α (R n) (x n) ≠ x n) ↔ f n α = true

/-- Convert a branching-program family into its balanced decision-formula
family. -/
def toFormulaFamily {w : ℕ} (R : BPFamily w) (x : ℕ → Fin w) : FormulaFamily :=
  fun n => BP.decisionFormula (R n) (x n)

end BPFamily

/-- A formula family computes `f` when it agrees at every family index and on
every total assignment. -/
def FormulaFamily.Computes (F : FormulaFamily)
    (f : ℕ → (ℕ → Bool) → Bool) : Prop :=
  ∀ n α, BoolFormula.eval α (F n) = f n α

/-- Boolean assignment families computed by logarithmic-depth formula families. -/
def FormulaNC1 : Set (ℕ → (ℕ → Bool) → Bool) :=
  {f | ∃ F : FormulaFamily, F.LogDepth ∧ F.Computes f}

/-- Boolean assignment families decided by polynomial-length width-`5`
permutation branching programs. -/
def Width5BP : Set (ℕ → (ℕ → Bool) → Bool) :=
  {f | ∃ (R : BPFamily 5) (x : ℕ → Fin 5), R.PolynomialLength ∧ R.Decides x f}

end Complexity
