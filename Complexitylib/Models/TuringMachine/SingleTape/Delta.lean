import Complexitylib.Models.TuringMachine.SingleTape.Sim
import Complexitylib.Models.TuringMachine.Combinators

/-!
# Single-tape simulation — transition function (under construction)

The phase transition functions assembled into `singleTapeSim`'s `δ'`. Each
phase function has the full `δ`-output signature
`SimQ k Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3`
(next state, single work write, output write, input dir, single work dir, output
dir — there is no input write, the input tape being read-only).

This file is built phase-by-phase. **GATHER** (the rightward read sweep) is
implemented here; SCATTER/COMMIT/run wiring and the assembled machine follow.
See `docs/A4-SingleTapeSimulation.md`.
-/

namespace NTM.SingleTape

/-- Clamp a direction to be `▷`-safe: a head reading `▷` is forced right
    (`δ_right_of_start`). On non-`▷` cells (the reachable case) it is the
    identity, so it never changes the simulated behaviour. -/
def safeDir (head : Γ) (d : Dir3) : Dir3 := if head = Γ.start then Dir3.right else d

@[simp] theorem safeDir_start (d : Dir3) : safeDir Γ.start d = Dir3.right := rfl

theorem safeDir_right_of_start {head : Γ} {d : Dir3} (h : head = Γ.start) :
    safeDir head d = Dir3.right := by subst h; rfl

/-- The **COMMIT** step applies the simulated `N`-step's deferred input/output
    actions — output write+move, input move — then returns to `run q'` (work head
    idling at cell 1). It accounts for the `▷`-dodge performed at `run`: if the
    original input/output symbol was `▷` that head already moved right, so we
    leave it (idle); otherwise we apply the recorded action, `▷`-clamped. -/
def commitStep {k : ℕ} {Q : Type} (d : CommitData Q) (iHead wH oHead : Γ) :
    SimQ k Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  let (q', oW, oD, iD, iSym, oSym) := d
  let iDir := if iSym = Γ.start then TM.idleDir iHead else safeDir iHead iD
  let oWrite := if oSym = Γ.start then TM.readBackWrite oHead else oW
  let oDir := if oSym = Γ.start then TM.idleDir oHead else safeDir oHead oD
  ( SimQ.run q', (fun _ => TM.readBackWrite wH), oWrite,
    iDir, (fun _ => TM.idleDir wH), oDir )

/-- COMMIT's directions are `▷`-safe (`δ_right_of_start`). -/
theorem commitStep_right_of_start {k : ℕ} {Q : Type} (d : CommitData Q)
    (iHead wH oHead : Γ) :
    (iHead = Γ.start → (commitStep (k := k) d iHead wH oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wH = Γ.start → (commitStep (k := k) d iHead wH oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (commitStep (k := k) d iHead wH oHead).2.2.2.2.2 = Dir3.right) := by
  obtain ⟨q', oW, oD, iD, iSym, oSym⟩ := d
  refine ⟨fun h => ?_, fun _ h => ?_, fun h => ?_⟩
  · simp only [commitStep]
    split
    · exact TM.idleDir_right_of_start h
    · exact safeDir_right_of_start h
  · simp only [commitStep]; exact TM.idleDir_right_of_start h
  · simp only [commitStep]
    split
    · exact TM.idleDir_right_of_start h
    · exact safeDir_right_of_start h

/-- Advance the sweep one cell within the block layout: slot `0 → 1 → 2` within
    a tape's triple, then on to the next tape's slot `0` (wrapping past the last
    tape into the next block's tape `0`). -/
def advanceSweep (k : ℕ) (pos : SweepPos k) : SweepPos k :=
  if pos.2 = 2 then
    -- next tape: `t+1` if still a real tape, else wrap to tape `0` (next block)
    (⟨if pos.1.val + 1 < k then pos.1.val + 1 else 0, by split <;> omega⟩, 0)
  else (pos.1, pos.2 + 1)

/-- One **GATHER** step. The work head sweeps rightward over the encoded region,
    reading each tape's `(sym-hi, sym-lo, head-bit)` triple and recording the
    symbol under a head into `acc`. Slots:

    * `0` (sym-hi): stash the high code cell in `pending`.
    * `1` (sym-lo): decode the symbol (`decSymΓ`) into `pending`.
    * `2` (head-bit): if set (`Γ.one`), this tape's head is here — write the
      decoded symbol into `acc` at this tape.

    Reaching the `□` sentinel ends the sweep: apply `N.δ b` (the one meaningful
    use of the choice `b`) and hand the writes/directions to SCATTER. The work
    head moves right while sweeping and never left except on `□` (≠ `▷`), so the
    work direction is `▷`-safe; input/output stay put via `idleDir` and are
    preserved via `readBackWrite`. -/
def gatherStep {k : ℕ} (N : NTM k) (b : Bool) (d : GatherData k N.Q)
    (iHead wH oHead : Γ) :
    SimQ k N.Q × (Fin 1 → Γw) × Γw × Dir3 × (Fin 1 → Dir3) × Dir3 :=
  let (q, acc, iSym, oSym, pos, rf, pending) := d
  if wH = Γ.blank then
    -- sentinel reached: compute one N-step and rewind leftward to cell 1
    let (q', wW, oW, iD, wD, oD) := N.δ b q iSym acc oSym
    ( SimQ.rewind (q', (fun i => (wW i, wD i)), (oW, oD), iD, iSym, oSym),
      (fun _ => Γw.blank), TM.readBackWrite oHead,
      TM.idleDir iHead, (fun _ => Dir3.left), TM.idleDir oHead )
  else
    let pos' := advanceSweep k pos
    if pos.2 = 0 then
      -- head-bit: record whether this tape's head is here
      ( SimQ.gather (q, acc, iSym, oSym, pos', decide (wH = Γ.one), pending),
        (fun _ => TM.readBackWrite wH), TM.readBackWrite oHead,
        TM.idleDir iHead, (fun _ => Dir3.right), TM.idleDir oHead )
    else if pos.2 = 1 then
      -- sym-hi: stash the high code cell
      ( SimQ.gather (q, acc, iSym, oSym, pos', rf, wH),
        (fun _ => TM.readBackWrite wH), TM.readBackWrite oHead,
        TM.idleDir iHead, (fun _ => Dir3.right), TM.idleDir oHead )
    else
      -- sym-lo: decode the symbol and, if a head is here, record it in `acc`
      let acc' := if rf then
          (if h : pos.1.val < k then Function.update acc ⟨pos.1.val, h⟩ (decSymΓ pending wH)
           else acc)
        else acc
      ( SimQ.gather (q, acc', iSym, oSym, pos', rf, pending),
        (fun _ => TM.readBackWrite wH), TM.readBackWrite oHead,
        TM.idleDir iHead, (fun _ => Dir3.right), TM.idleDir oHead )

/-- The GATHER step's directions are `▷`-safe (`δ_right_of_start`): input and
    output use `idleDir`, and the work head moves left only on the `□` sentinel
    (never on `▷`), moving right in every `▷`-reachable branch. -/
theorem gatherStep_right_of_start {k : ℕ} (N : NTM k) (b : Bool)
    (d : GatherData k N.Q) (iHead wH oHead : Γ) :
    (iHead = Γ.start → (gatherStep N b d iHead wH oHead).2.2.2.1 = Dir3.right) ∧
    (∀ i, wH = Γ.start → (gatherStep N b d iHead wH oHead).2.2.2.2.1 i = Dir3.right) ∧
    (oHead = Γ.start → (gatherStep N b d iHead wH oHead).2.2.2.2.2 = Dir3.right) := by
  obtain ⟨q, acc, iSym, oSym, pos, rf, pending⟩ := d
  refine ⟨fun h => ?_, fun i h => ?_, fun h => ?_⟩
  · simp only [gatherStep]; split_ifs <;> exact TM.idleDir_right_of_start h
  · subst h
    simp only [gatherStep]
    rw [if_neg (by decide : ¬ (Γ.start = Γ.blank))]
    split_ifs <;> rfl
  · simp only [gatherStep]; split_ifs <;> exact TM.idleDir_right_of_start h

end NTM.SingleTape
