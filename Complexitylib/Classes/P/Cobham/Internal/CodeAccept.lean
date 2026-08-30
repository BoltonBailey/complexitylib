/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.CodeRewind

/-!
# Deciding whether a record is accepting

⚠️ Unreviewed by Bolton

A record is accepting when its state field is the halting state and its output
tape holds `1` in cell `1`. The state field is block `0` truncated to the state
code's width, and the verdict cell is read after the rewind of
`Complexitylib.Classes.P.Cobham.Internal.CodeRewind`.

## Main definitions

- `Complexity.verdictSym` — the symbol in cell `1` of a rewound output code
- `Complexity.acceptFlag` — the accepting-record test

## Main results

- `Complexity.verdictSym_rewound` — what the verdict cell reads
- `Complexity.acceptFlagFn_mem_FP` — the test is polynomial-time
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## The verdict cell -/

/-- The symbol in cell `1` of a rewound output code. -/
def verdictSym (R z : List Bool) : List Bool := ((z.drop R.length).drop 2).take 2

/-- **The verdict cell of a rewound output code is cell `1` of the tape.** -/
theorem verdictSym_rewound (W : ℕ) (t : Tape) (hW : 1 ≤ W) :
    verdictSym (blockRuler W) (pairCode W { head := 0, cells := t.cells })
      = symCode (t.cells 1) := by
  rw [verdictSym, drop_pairCode_rewound W t,
    show W + 1 = 1 + 1 + (W - 1) from by omega, cellsCode_add, cellsCode_add]
  simp only [cellsCode_one, List.append_assoc]
  rw [List.drop_left' (by rw [symCode_length]), List.take_left' (by rw [symCode_length])]

/-! ## The test -/

/-- Is the record an accepting halting configuration? -/
def acceptFlag (qcode R ruler u : List Bool) : List Bool :=
  andBit (eqFlag ((blockAt R u 0).take qcode.length) qcode)
    (eqFlag (verdictSym R (rewindCode R ruler (outPair R u))) (symCode Γ.one))

theorem acceptFlag_flag (qcode R ruler u : List Bool) :
    acceptFlag qcode R ruler u = [true] ∨ acceptFlag qcode R ruler u = [false] := by
  rw [acceptFlag]
  rcases eqFlag_flag ((blockAt R u 0).take qcode.length) qcode with h | h <;>
    rcases eqFlag_flag (verdictSym R (rewindCode R ruler (outPair R u)))
      (symCode Γ.one) with h' | h' <;> rw [h, h'] <;> simp [andBit]

/-! ## The test is polynomial-time -/

theorem acceptFlagFn_mem_FP (qcode : List Bool) {Rf rulerf uf : List Bool → List Bool}
    (hR : Rf ∈ FP) (hruler : rulerf ∈ FP) (hu : uf ∈ FP) :
    (fun w => acceptFlag qcode (Rf w) (rulerf w) (uf w)) ∈ FP := by
  have hqc : (fun _ : List Bool => qcode) ∈ FP := constFn_mem_FP qcode
  have hstate : (fun w => (blockAt (Rf w) (uf w) 0).take qcode.length) ∈ FP := by
    refine mem_FP_of_eq (Cobham.takeLenFn_mem_FP hqc (blockAtFn_mem_FP hR hu 0)) fun w => rfl
  have hout : (fun w => outPair (Rf w) (uf w)) ∈ FP := outPairFn_mem_FP hR hu
  have hlen : ∀ w, (outPair (Rf w) (uf w)).length ≤ 2 * (Rf w).length := by
    intro w
    rw [outPair, List.length_append, blockAt, blockAt]
    have h1 := List.length_take_le (Rf w).length ((uf w).drop (3 * (Rf w).length))
    have h2 := List.length_take_le (Rf w).length ((uf w).drop (4 * (Rf w).length))
    omega
  have hrew : (fun w => rewindCode (Rf w) (rulerf w) (outPair (Rf w) (uf w))) ∈ FP :=
    rewindCodeFn_mem_FP hR hruler hout hlen
  have hverd : (fun w => verdictSym (Rf w)
      (rewindCode (Rf w) (rulerf w) (outPair (Rf w) (uf w)))) ∈ FP := by
    refine mem_FP_of_eq (Cobham.takeLenFn_mem_FP (constFn_mem_FP [false, false])
      (dropLenFn_mem_FP (constFn_mem_FP [false, false]) (dropLenFn_mem_FP hR hrew)))
      fun w => rfl
  exact andBitFn_mem_FP (eqFlagFn_mem_FP hstate hqc)
    (eqFlagFn_mem_FP hverd (constFn_mem_FP (symCode Γ.one)))

end Complexity
