/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryBump.Internal

/-!
# The zero-extending increment

⚠️ Unreviewed by Bolton

`TM.binarySuccTM` increments the number a tape holds: a carry running off the end appends a new
high `1`, which is what a numeral needs. `TM.binaryBumpTM` runs the same scan with that one write
changed to a `0`, which increments the *string* a tape holds — one place wider each time it
overflows.

The strings it steps through, from the empty one, are every bitstring in order of length:
`[]`, `0`, `1`, `00`, `10`, `01`, `11`, `000`, … So a machine enumerating the witnesses of a
bounded existential can carry the witness on a tape and advance it with this, instead of decoding
one from a counter.

## Main results

- `TM.binaryBumpTM` — the machine, and `TM.binaryBumpTime` its exact running time
- `TM.binaryBumpTM_reachesIn_frame` — exact execution with a full tape frame
- `TM.binaryBumpTM_hoareTime_frame` — its compositional time contract
- `TM.binaryBumpTM_isTransducer` — the output head never moves left
-/

public section

namespace Complexity

namespace BinaryBump

/-- The exact transition count is at most twice the string's length, plus two. -/
theorem steps_le (bits : List Bool) : steps bits ≤ 2 * bits.length + 2 :=
  steps_le_internal bits

end BinaryBump

namespace TM

variable {n : ℕ}

/-- The exact running time is at most twice the string's length, plus two. -/
theorem binaryBumpTime_le (bits : List Bool) :
    binaryBumpTime bits ≤ 2 * bits.length + 2 :=
  binaryBumpTime_le_internal bits

/-- **The zero-extending increment, executed exactly.** Starting on a rewound bit string,
`binaryBumpTM` halts after exactly `binaryBumpTime bits` transitions with the next string in the
enumeration. Input, output, and every unrelated work tape are preserved exactly. -/
theorem binaryBumpTM_reachesIn_frame (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hbits : (work₀ idx).HasBinaryString bits)
    (hcell0 : (work₀ idx).cells 0 = Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    ∃ c',
      (binaryBumpTM idx).reachesIn (binaryBumpTime bits)
        { state := (binaryBumpTM idx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryBumpTM idx).halted c' ∧
      c'.input = inp₀ ∧
      (∀ i, i ≠ idx → c'.work i = work₀ i) ∧
      (c'.work idx).HasBinaryString (BinaryBump.bump bits) ∧
      (c'.work idx).cells 0 = Γ.start ∧
      c'.output = out₀ :=
  binaryBumpTM_reachesIn_frame_internal idx bits inp₀ work₀ out₀ hbits hcell0 hinp hother hout

/-- Time-bounded compositional form of `TM.binaryBumpTM_reachesIn_frame`. -/
theorem binaryBumpTM_hoareTime_frame (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hbits : (work₀ idx).HasBinaryString bits)
    (hcell0 : (work₀ idx).cells 0 = Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start) :
    (binaryBumpTM idx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (∀ i, i ≠ idx → work i = work₀ i) ∧
        (work idx).HasBinaryString (BinaryBump.bump bits) ∧
        (work idx).cells 0 = Γ.start ∧
        out = out₀)
      (binaryBumpTime bits) :=
  binaryBumpTM_hoareTime_frame_internal idx bits inp₀ work₀ out₀ hbits hcell0 hinp hother hout

/-- `binaryBumpTM` never moves the output head left, so it is safe in one-way-output,
space-bounded compositions. -/
theorem binaryBumpTM_isTransducer (idx : Fin n) : (binaryBumpTM idx).IsTransducer :=
  binaryBumpTM_isTransducer_internal idx

end TM

end Complexity
