/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.BlockScan

/-!
# Checking a register against a known bitstring

⚠️ Unreviewed by Bolton

`Complexity.Scanner.eq` compares two registers and `Complexity.Scanner.isConst` compares a
register against a single symbol. What a construction needs in order to *start* — to pin a
register to a value it has computed outside the machine, such as the code of an initial
configuration — is the comparison against a whole known bitstring, which is
`Complexity.Scanner.bitsEq`.

The scanner carries the position it has reached, saturating at the end of the word, so cells past
the word are not read.

## Main definitions

- `Scanner.bitsEq` — check that a register holds a given list of bits

## Main results

- `Scanner.bitsEq_run` — it accepts exactly when the register holds them
-/

@[expose] public section

namespace Complexity

namespace Scanner

variable {j : ℕ}

/-- **Check that register `a` spells out `l`** in the cells the scan reads. -/
def bitsEq (j : ℕ) (a : Fin (j + 1)) (l : List Bool) : Scanner j :=
  ofRight (Fin (l.length + 1) × Bool) (⟨0, Nat.zero_lt_succ _⟩, true)
    (fun s cols =>
      (⟨min (s.1.val + 1) l.length, by omega⟩,
        s.2 && (if s.1.val < l.length then decide (cols a = Γ.ofBool (l.getD s.1.val false))
          else true)))
    Prod.snd

theorem rightOnly_bitsEq (j : ℕ) (a : Fin (j + 1)) (l : List Bool) :
    RightOnly (bitsEq j a l) :=
  rightOnly_ofRight _ _ _ _

/-- **What the check knows after `p` columns**: how far it has read, and whether every cell so far
agreed. -/
theorem bitsEq_runR (j : ℕ) (a : Fin (j + 1)) (l : List Bool) (cols : ℕ → Fin (j + 1) → Γ) :
    ∀ p : ℕ, ((bitsEq j a l).runR cols p).1.val = min p l.length ∧
      (((bitsEq j a l).runR cols p).2 = true ↔
        ∀ q, q < l.length → q < p → cols (q + 1) a = Γ.ofBool (l.getD q false)) := by
  intro p
  induction p with
  | zero =>
    refine ⟨by simp [runR, bitsEq, ofRight], ?_⟩
    show (true = true) ↔ _
    exact ⟨fun _ q _ hq => absurd hq (by omega), fun _ => rfl⟩
  | succ p ih =>
    obtain ⟨hpos, hval⟩ := ih
    refine ⟨?_, ?_⟩
    · show min (((bitsEq j a l).runR cols p).1.val + 1) l.length = min (p + 1) l.length
      rw [hpos]
      omega
    show (((bitsEq j a l).runR cols p).2 &&
      (if ((bitsEq j a l).runR cols p).1.val < l.length then
        decide (cols (p + 1) a = Γ.ofBool (l.getD ((bitsEq j a l).runR cols p).1.val false))
        else true)) = true ↔ _
    rw [hpos, Bool.and_eq_true, hval]
    by_cases hp : p < l.length
    · have hmin : min p l.length = p := by omega
      rw [hmin, if_pos hp, decide_eq_true_eq]
      constructor
      · rintro ⟨hall, hlast⟩ q hq hq'
        rcases Nat.lt_or_ge q p with h | h
        · exact hall q hq h
        · rw [show q = p by omega]
          exact hlast
      · exact fun h => ⟨fun q hq hq' => h q hq (by omega), h p hp (by omega)⟩
    · have hmin : min p l.length = l.length := by omega
      rw [hmin, if_neg (by omega)]
      constructor
      · rintro ⟨hall, -⟩ q hq _
        exact hall q hq (by omega)
      · exact fun h => ⟨fun q hq hq' => h q hq (by omega), rfl⟩

private theorem getD_eq_getElem_bool (l : List Bool) (q : ℕ) (hq : q < l.length) :
    l.getD q false = l[q] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  rfl

/-- **The check accepts exactly when the register holds the word.** -/
theorem bitsEq_run (j : ℕ) (a : Fin (j + 1)) (l : List Bool) (cols : ℕ → Fin (j + 1) → Γ)
    (len : ℕ) (hlen : l.length ≤ len) :
    (bitsEq j a l).emit ((bitsEq j a l).run cols len) = true ↔ HoldsBits cols 0 a l := by
  rw [run, runL_of_rightOnly (rightOnly_bitsEq j a l)]
  show ((bitsEq j a l).runR cols len).2 = true ↔ _
  rw [(bitsEq_runR j a l cols len).2]
  constructor
  · intro h q hq
    rw [Nat.zero_add, h q hq (by omega), getD_eq_getElem_bool l q hq]
  · intro h q hq _
    have := h q hq
    rw [Nat.zero_add] at this
    rw [this, getD_eq_getElem_bool l q hq]

end Scanner

end Complexity
