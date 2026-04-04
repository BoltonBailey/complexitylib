import Complexitylib.Models.TuringMachine.UTM.UTM

/-!
# UTM Composition Test

Historical scratch file that documented composition gaps between sub-machine
Hoare specs. These gaps have since been resolved in `SimLoop.lean`, which
successfully chains the full loop iteration proof.

The examples below are retained as documentation of the interface requirements
between sub-machines.
-/

namespace TM

variable {n : ℕ}

/-! ## Gap 1: lookup postcondition is missing state/sim tape preservation

The lookup machine only modifies desc tape (tape 0) and scratch tape (tape 3).
It does NOT touch state tape (tape 1) or sim tape (tape 2).
But its postcondition doesn't say this.
-/

/-- What lookup's postcondition SHOULD include (in addition to current exports). -/
example (tm : TM n) (k : ℕ) (hk : k = @Fintype.card tm.Q tm.finQ)
    (desc : List Bool) (hdesc : desc = TMEncoding.encodeTM tm)
    (simCfg : Cfg n tm.Q) (q : Fin k)
    (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) :
    -- After readCurrent, we have stateOnTapeAt and superCellsCorrect.
    -- After lookup, we need them for applyTransition.
    -- But lookup's postcondition drops them.
    let e := tm.stateEquivK hk
    True → -- placeholder for: "given readCurrent postcondition ∧ lookup postcondition"
    -- We need but cannot derive:
    --   stateOnTapeAt k (e simCfg.state) (work utmStateTape)   ← GAP
    --   superCellsCorrect simCfg (work utmSimTape)             ← GAP
    --   (work utmStateTape).head = 1                           ← GAP
    --   (work utmSimTape).head = 1                             ← GAP
    True := by
  trivial

/-! ## Gap 2: applyTransition postcondition is missing inp/out preservation

The applyTransition machine only modifies work tapes (state, sim, scratch).
It does NOT touch the UTM input tape or output tape.
But its postcondition doesn't mention inp/out at all.
-/

/-- What applyTransition's postcondition SHOULD include for checkHalt composition. -/
example : True →
    -- After applyTransition, checkHalt needs:
    --   out.cells 0 = Γ.start                                 ← GAP (inp/out preserved)
    --   ∀ j ≥ 1, out.cells j ≠ Γ.start                       ← GAP
    --   out.head ≤ B                                          ← GAP
    --   inp.cells 0 = Γ.start                                 ← GAP
    --   ∀ j ≥ 1, inp.cells j ≠ Γ.start                       ← GAP
    --   inp.head ≥ 1                                          ← GAP
    --   ∀ i, (work i).head ≥ 1                                ← GAP (only desc/state/sim = 1)
    --   out.head ≥ 1                                          ← GAP
    True := by
  trivial

/-! ## Gap 3: checkHalt postcondition is missing sim tape + scratch + inp conditions

The checkHalt machine (seqTM skipToQhaltTM compareWriteTM) only modifies
desc tape (for scanning) and output tape (for writing the result). It preserves
sim tape, scratch tape, and inp tape. But the postcondition doesn't say this.
-/

/-- What checkHalt's postcondition SHOULD include for the next loop iteration. -/
example : True →
    -- For the next iteration's readCurrent, we need:
    --   superCellsCorrect simCfg' (work utmSimTape)           ← GAP
    --   (work utmSimTape).head = 1                            ← GAP
    --   (work utmScratchTape).head = 1                        ← GAP (scratch rewound?)
    --   ∀ j ≥ 1, (work utmScratchTape).cells j = Γ.blank     ← GAP (scratch cleared?)
    --   inp.read ≠ Γ.start ∧ inp.head ≥ 1                    ← GAP
    --   out.read ≠ Γ.start ∧ out.head ≥ 1                    ← partially (out.head = 1)
    True := by
  trivial

/-! ## Scratch tape clearing

There's an additional composition issue: readCurrent requires the scratch tape
to be blank (cells ≥ 1 = Γ.blank). But after lookup + applyTransition, the
scratch tape has the transition output data written on it. The scratch tape
needs to be CLEARED before the next readCurrent.

Does applyTransition clear the scratch tape? Looking at its postcondition:
it doesn't mention scratch tape contents at all. The applyTransition machine
has a "clear scratch" phase, but we need to verify this is exported.
-/

/-! ## The head-0 issue

Independently of the composition gaps, `applyTransitionTM_hoare_proof`
requires `(∀ i, (simCfg.work i).head ≥ 1) ∧ simCfg.output.head ≥ 1`.

But `initCfg x` has all heads at 0 (`initTape` uses `head := 0`).

The TM structure has `δ_right_of_start` which forces right-movement when
reading ▷ (at position 0). This means after the first step, heads are ≥ 1.
But heads can revisit position 0 (by moving left from 1), and when they do,
applyTransition corrupts the super-cell encoding at position 0 because it
writes the δ-returned symbol there (but Tape.write at head 0 is a no-op
for the actual simulated tape, so cells[0] stays ▷).

Options:
1. Change `initTape` to `head := 1` (model change, many files affected)
2. Add hypothesis to theorems (heads always ≥ 1)
3. Weaken superCellsCorrect to ignore position 0
-/

end TM
