import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.ReadCurrent
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Mathlib.Data.Fintype.Prod

/-!
# UTM Extract Output

After the simulation loop terminates, extract the simulated output from the
super-cell encoding and write it to the real output tape.

## Architecture

The machine operates in three phases:

1. **Rewind output**: Scan the output tape left to ▷, then move right to cell 1.
2. **Scan to output symbol**: Move the sim tape head right by a fixed distance
   to reach the hi bit of the output tape's position-1 super-cell. The distance
   is `3*(n+2) + 3*(n+1) + 1` cells from cell 1, computed as: one full super-cell
   width (position 0) + tapes 0..n within position 1 + the head marker.
3. **Read and decode**: Read the 2 symbol cells (hi, lo), decode via
   `SuperCell.cellPairToSym`, write to output cell 1.

## Main results

- `extractOutputTM` — the machine definition
- `extractOutputTM_hoareTime` — HoareTime spec: parametric in `simCfg`
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Distance from sim tape cell 1 to the hi bit of the output tape's
    position-1 super-cell. -/
def extractSkipDist (n : ℕ) : ℕ := 3 * (n + 2) + 3 * (n + 1) + 1

/-- States for the extractOutput machine. -/
inductive ExtractOutputQ (n : ℕ) where
  /-- Rewind output tape left until ▷. -/
  | rewindOut
  /-- Output at ▷, move right one step to cell 1. -/
  | rightOut
  /-- Scan sim tape right, `rem` steps remaining until hi bit. -/
  | scanSim (rem : Fin (extractSkipDist n + 1))
  /-- At hi bit position on sim tape. Read it. -/
  | readHi
  /-- At lo bit position. Remembering hi value. -/
  | readLo (hi : Γ)
  /-- Decode (hi, lo) → symbol, write to output. -/
  | writeOut (hi lo : Γ)
  /-- Halt. -/
  | done
  deriving DecidableEq

private instance : Fintype (ExtractOutputQ n) where
  elems :=
    {.rewindOut, .rightOut, .readHi, .done} ∪
    (Finset.univ.image fun (i : Fin (extractSkipDist n + 1)) =>
      ExtractOutputQ.scanSim i) ∪
    (Finset.univ.image fun (g : Γ) => ExtractOutputQ.readLo g) ∪
    (Finset.univ.image fun (p : Γ × Γ) => ExtractOutputQ.writeOut p.1 p.2)
  complete x := by
    cases x with
    | rewindOut => simp [Finset.mem_union, Finset.mem_insert]
    | rightOut => simp [Finset.mem_union, Finset.mem_insert]
    | readHi => simp [Finset.mem_union, Finset.mem_insert]
    | done => simp [Finset.mem_union, Finset.mem_insert]
    | scanSim i =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; left; right; exact ⟨i, rfl⟩
    | readLo g =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; right; exact ⟨g, rfl⟩
    | writeOut hi lo =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Prod.exists]
      right; exact ⟨hi, lo, rfl⟩

-- ════════════════════════════════════════════════════════════════════════
-- Machine definition
-- ════════════════════════════════════════════════════════════════════════

/-- Extract the simulated output and write it to the real output tape.

    Phase 1: Rewind output tape to ▷, then step right to cell 1.
    Phase 2: Scan sim tape right by `extractSkipDist n` cells to reach the
    output tape's position-1 hi bit.
    Phase 3: Read hi and lo bits, decode, write to output cell 1. -/
def extractOutputTM : TM 4 where
  Q := ExtractOutputQ n
  qstart := .rewindOut
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rewindOut =>
      if oHead = Γ.start then
        -- At ▷, move right to cell 1
        (.rightOut,
         fun _ => .blank, .blank,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
      else
        -- Move output left
        (.rewindOut,
         fun _ => .blank, readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), moveLeftDir oHead)
    | .rightOut =>
      -- Output is now at cell 1. Start scanning sim tape.
      (.scanSim ⟨extractSkipDist n, by omega⟩,
       fun i => if i = utmSimTape then readBackWrite (wHeads utmSimTape) else .blank,
       readBackWrite oHead,
       idleDir iHead,
       fun i => if i = utmSimTape then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    | .scanSim rem =>
      if h : rem.val = 0 then
        -- Arrived at hi bit. Read it.
        (.readHi,
         fun i => if i = utmSimTape then readBackWrite (wHeads utmSimTape) else .blank,
         .blank,
         idleDir iHead,
         fun i => if i = utmSimTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Keep scanning right on sim tape
        (.scanSim ⟨rem.val - 1, by omega⟩,
         fun i => if i = utmSimTape then readBackWrite (wHeads utmSimTape) else .blank,
         .blank,
         idleDir iHead,
         fun i => if i = utmSimTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .readHi =>
      -- At hi bit cell. Remember it, advance to lo bit.
      (.readLo (wHeads utmSimTape),
       fun i => if i = utmSimTape then readBackWrite (wHeads utmSimTape) else .blank,
       .blank,
       idleDir iHead,
       fun i => if i = utmSimTape then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    | .readLo hi =>
      -- At lo bit cell. Decode (hi, lo) and prepare to write.
      (.writeOut hi (wHeads utmSimTape),
       fun _ => .blank, .blank,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .writeOut hi lo =>
      -- Write the decoded symbol to output cell 1.
      let (scrHi, scrLo) := transcodePair hi lo
      (.done,
       fun _ => .blank, scrHi,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    have hros := fun (h : iHead = Γ.start) => idleDir_right_of_start h
    have hrosW := fun (i : Fin 4) (h : wHeads i = Γ.start) => idleDir_right_of_start h
    have hrosO := fun (h : oHead = Γ.start) => idleDir_right_of_start h
    have simRos : ∀ i, wHeads i = Γ.start →
        (if i = utmSimTape then Dir3.right else idleDir (wHeads i)) = Dir3.right := by
      intro i hi; split <;> [rfl; exact idleDir_right_of_start hi]
    match state with
    | .rewindOut =>
      dsimp only []; split
      · exact ⟨hros, fun _ => hrosW _, fun _ => rfl⟩
      · exact ⟨hros, fun _ => hrosW _, fun h => by subst h; rfl⟩
    | .rightOut =>
      dsimp only []
      exact ⟨hros, simRos, hrosO⟩
    | .scanSim rem =>
      dsimp only []; split
      · exact ⟨hros, simRos, hrosO⟩
      · exact ⟨hros, simRos, hrosO⟩
    | .readHi =>
      dsimp only []
      exact ⟨hros, simRos, hrosO⟩
    | .readLo _ =>
      exact ⟨hros, fun _ => hrosW _, hrosO⟩
    | .writeOut _ _ =>
      exact ⟨hros, fun _ => hrosW _, hrosO⟩
    | .done =>
      exact ⟨hros, fun _ => hrosW _, hrosO⟩

-- ════════════════════════════════════════════════════════════════════════
-- HoareTime specification
-- ════════════════════════════════════════════════════════════════════════

/-- HoareTime specification for `extractOutputTM`.

    Parametric in `simCfg`. The postcondition says the real output cell 1
    matches the simulated output cell 1.

    **Pre**: Sim tape encodes `simCfg`; sim tape head at 1; output tape WF.
    **Post**: Real output cell 1 = `simCfg.output.cells 1`. -/
theorem extractOutputTM_hoareTime {Q : Type} [Fintype Q] [DecidableEq Q]
    (simCfg : Cfg n Q) (B : ℕ) :
    (extractOutputTM (n := n)).HoareTime
      (fun _inp work out =>
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        out.head ≤ B)
      (fun _inp _work out =>
        out.cells 1 = simCfg.output.cells 1)
      (B + extractSkipDist n + 5) := by
  sorry

end TM
