/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Models.TuringMachine.Combinators.Internal.RetargetWindow
public import Complexitylib.Models.TuringMachine.Subroutines.CopyOutput
public import Complexitylib.Models.TuringMachine.Subroutines.ResetTapes
public import Complexitylib.Models.TuringMachine.Subroutines.PairEmit
public import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
public import Complexitylib.Models.TuringMachine.Subroutines.BinaryBump
public import Complexitylib.Classes.Containments.Internal.WitnessEnum

/-!
# Parts of the witness-enumerating machine

⚠️ Unreviewed by Bolton

The machine that will witness `polyExistsClass PSPACE ⊆ PSPACE` copies its input onto a work
tape, then loops over witnesses, building `pair x w` and running the matrix machine on it. This
file records the window contracts of the individual parts, obtained from their existing time
contracts by `TM.keepsWindowOn_of_haltsIn` — no new tape analysis is needed for any of them.

## Main results

- `TM.copyInputToOutputTM_keepsWindowOn` — the input-to-output copy stays inside a linear window
- `TM.copyInputToWork_keepsWindow` — and so does its retargeting onto a work tape
- `TM.resetTapes_keepsWindowOn` — the clear-scratch stage keeps a window
- `TM.pairEmitPre`, `TM.pairInputWork_keepsWindowOn` — and so does the pair emitter
- `TM.binarySucc_keepsWindowOn` — and the counter increment
- `bump_eq_bumpLE` — the witness-advancing machine computes the witness enumeration's step
- `TM.binaryBump_keepsWindowOn` — and it keeps a window
-/

@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- **The input-to-output copy keeps a linear window.** Started on its initial configuration it
halts in `|x| + 2` steps, and a head moves at most one cell per step, so nothing travels past
cell `|x| + 2`. -/
theorem copyInputToOutputTM_keepsWindowOn (n : ℕ) (x : List Bool) :
    (copyInputToOutputTM (n := n)).KeepsWindowOn
      (fun c => c = (copyInputToOutputTM (n := n)).initCfg x)
      x.length (0 + (x.length + 2)) := by
  refine keepsWindowOn_of_haltsIn (fun c hc i => ?_) (fun c hc => ?_) (fun c hc => ?_)
    (fun c hc => ?_)
  · subst hc
    exact Nat.le_of_eq rfl
  · subst hc
    exact Nat.zero_le _
  · subst hc
    exact Nat.zero_le _
  · subst hc
    obtain ⟨c', t, hle, hreach, hhalt, -⟩ := copyInputToOutputTM_computesInTime n x
    exact ⟨c', t, hle, hreach, hhalt⟩

/-- **Redirecting that copy onto a work tape keeps a window too.** This is the stage that puts a
copy of the real input where the pair emitter can delimit it. -/
theorem copyInputToWork_keepsWindow (n : ℕ) (x : List Bool) :
    ∀ D, (copyInputToOutputTM (n := n)).retargetOutput.reaches
        ((copyInputToOutputTM (n := n)).retargetCfg
          ((copyInputToOutputTM (n := n)).initCfg x)) D →
      D.WithinDecisionSpace x.length (0 + (x.length + 2) + 1) :=
  retargetOutput_keepsWindow_of_reaches _ _
    (fun c hreach => copyInputToOutputTM_keepsWindowOn n x _ rfl c hreach)


/-- **The clear-scratch stage keeps a window.** `TM.resetTapesTM` blanks its targets regardless of
their contents, in time linear in the wipe height and the number of targets; converting its
halting bound gives the window directly. This is the stage that makes a loop body robust enough
for `TM.seqTM_keepsWindow_of_post`. -/
theorem resetTapes_keepsWindowOn {n : ℕ} (targets : List (Fin n)) (hnodup : targets.Nodup)
    (r : Fin n) (hr : r ∉ targets) (H : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinpSI : Tape.StartInvariant inp₀) (hinpP : Parked inp₀)
    (hout0 : out₀ = (Tape.init []).move Dir3.right)
    (hworkSI : ∀ j, j ≠ r → Tape.StartInvariant (work₀ j))
    (htargetHead : ∀ j, j ∈ targets → (work₀ j).head ≤ H)
    (hworkR : work₀ r = regTape H)
    (hother : ∀ j, j ≠ r → j ∉ targets → Parked (work₀ j))
    {inputLength h₀ : ℕ}
    (hheads : ∀ i, (work₀ i).head ≤ h₀)
    (hinputHead : inp₀.head ≤ inputLength + h₀ + 1)
    (houtputHead : out₀.head ≤ h₀ + 1) :
    (seqTM (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
        (forRegTM (wipeStepTM targets) r)).KeepsWindowOn
      (fun c => c.state = (seqTM (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
          (forRegTM (wipeStepTM targets) r)).qstart ∧
        (c.input = inp₀ ∧ c.work = work₀ ∧ c.output = out₀))
      inputLength (h₀ + (targets.length * (H + 4) + H * 4 + 8)) :=
  keepsWindowOn_of_hoareTime_pinned
    (resetTapes_hoareTime targets hnodup r hr H inp₀ work₀ out₀ hinpSI hinpP hout0 hworkSI
      htargetHead hworkR hother)
    hheads hinputHead houtputHead


/-- The pair emitter's precondition, strengthened with the head bound its own contract omits. -/
def pairEmitPre {n : ℕ} (firstIdx : Fin n) (first second : List Bool) (h₀ : ℕ) :
    TapePred n := fun inp work out =>
  (inp = (Tape.init (second.map Γ.ofBool)).move Dir3.right ∧
    (work firstIdx).head = 1 ∧
    (work firstIdx).HasOutput first ∧
    (∀ i, (work i).StartInvariant ∧ 1 ≤ (work i).head) ∧
    out = (Tape.init []).move Dir3.right) ∧
  (∀ i, (work i).head ≤ h₀)

/-- **The pair emitter keeps a window.** Its own precondition parks the input and output tapes at
cell one but says nothing about how far the other work heads have travelled, so `pairEmitPre`
adds that bound; everything else comes from the emitter's halting time. -/
theorem pairInputWork_keepsWindowOn {n : ℕ} (firstIdx : Fin n) (first second : List Bool)
    (inputLength h₀ : ℕ) :
    (pairInputWorkTM firstIdx).KeepsWindowOn
      (fun c => c.state = (pairInputWorkTM firstIdx).qstart ∧
        pairEmitPre firstIdx first second h₀ c.input c.work c.output)
      inputLength (h₀ + pairInputWorkTime first second) := by
  refine keepsWindowOn_of_hoareTime (pre := pairEmitPre firstIdx first second h₀)
    (post := fun _inp _work out => out.HasOutput (pair first second))
    (fun inp work out hpre =>
      pairInputWorkTM_hoareTime firstIdx first second inp work out hpre.1)
    (fun _ _ _ hpre i => hpre.2 i) (fun inp _ _ hpre => ?_) (fun _ _ out hpre => ?_)
  · rw [hpre.1.1]
    show 0 + 1 ≤ inputLength + h₀ + 1
    omega
  · rw [hpre.1.2.2.2.2]
    show 0 + 1 ≤ h₀ + 1
    omega


/-- **The counter increment keeps a window.** `TM.binarySuccTM` advances the little-endian
counter that carries the witness; its framed contract already pins every tape, so the window
follows from the head bounds and its running time. -/
theorem binarySucc_keepsWindowOn {n : ℕ} (idx : Fin n) (value : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hvalue : (work₀ idx).HasBinaryNat value)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    {inputLength h₀ : ℕ}
    (hwork : ∀ i, (work₀ i).head ≤ h₀)
    (hinputHead : inp₀.head ≤ inputLength + h₀ + 1)
    (houtputHead : out₀.head ≤ h₀ + 1) :
    (binarySuccTM idx).KeepsWindowOn
      (fun c => c.state = (binarySuccTM idx).qstart ∧
        (c.input = inp₀ ∧ c.work = work₀ ∧ c.output = out₀))
      inputLength (h₀ + binarySuccTime value) :=
  keepsWindowOn_of_hoareTime_pinned
    (binarySuccTM_hoareTimeSpace_frame idx value inputLength h₀ inp₀ work₀ out₀ hvalue hinp
      hother hout ⟨hwork, hinputHead⟩).1
    hwork hinputHead houtputHead

/-- **The witness-advancing machine keeps a window.** Like the counter increment beside it, its
framed contract pins every tape, so the window follows from the head bounds and its running
time. -/
theorem binaryBump_keepsWindowOn {n : ℕ} (idx : Fin n) (bits : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hbits : (work₀ idx).HasBinaryString bits)
    (hcell0 : (work₀ idx).cells 0 = Γ.start)
    (hinp : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ idx → (work₀ i).read ≠ Γ.start)
    (hout : out₀.read ≠ Γ.start)
    {inputLength h₀ : ℕ}
    (hwork : ∀ i, (work₀ i).head ≤ h₀)
    (hinputHead : inp₀.head ≤ inputLength + h₀ + 1)
    (houtputHead : out₀.head ≤ h₀ + 1) :
    (binaryBumpTM idx).KeepsWindowOn
      (fun c => c.state = (binaryBumpTM idx).qstart ∧
        (c.input = inp₀ ∧ c.work = work₀ ∧ c.output = out₀))
      inputLength (h₀ + binaryBumpTime bits) :=
  keepsWindowOn_of_hoareTime_pinned
    (binaryBumpTM_hoareTime_frame idx bits inp₀ work₀ out₀ hbits hcell0 hinp hother hout)
    hwork hinputHead houtputHead

end TM

/-- **The witness-advancing machine computes the enumeration's step.** `BinaryBump.bump` is
defined on the tape's bit string and `bumpLE` on the witness the counter denotes; they are the
same function, which is what lets `dropTop_succ` serve as the loop invariant of a machine that
carries its witness on a tape. -/
theorem bump_eq_bumpLE : ∀ w : List Bool, BinaryBump.bump w = bumpLE w
  | [] => rfl
  | false :: _ => rfl
  | true :: w => by rw [BinaryBump.bump, bumpLE, bump_eq_bumpLE w]

end Complexity
