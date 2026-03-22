import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# UTM Apply Transition

Applies the decoded transition to the simulated state and tapes:
1. Update the state tape (write new one-hot encoding)
2. Update the simulation tape (write new symbols, move head markers)

## Main results

- `applyTransitionTM` — the machine definition
- `applyTransitionTM_hoareTime` — HoareTime spec: advances SimInvariant by one step
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Apply transition machine (placeholder)
-- ════════════════════════════════════════════════════════════════════════

/-- Apply the decoded transition to the UTM's work tapes.
    Reads transition output from scratch. Updates state tape (new one-hot)
    and sim tape (new symbols + moved head markers). -/
noncomputable def applyTransitionTM : TM 4 := writeTM .blank

/-- HoareTime specification for `applyTransitionTM`.

    Parametric in `simCfg` (the pre-step configuration). Requires that
    `simCfg.state ≠ tm.qhalt` (so `tm.step` produces `some`).

    The postcondition advances the simulation invariant: state and sim tapes
    now encode `tm.step simCfg`. All heads returned to cell 1.

    **Pre**: State + sim tapes encode `simCfg`; scratch has transition output
    matching `tm.δ`; desc tape valid.
    **Post**: State + sim tapes encode the stepped config; desc preserved;
    heads at 1. -/
theorem applyTransitionTM_hoareTime (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (desc : List Bool)
    (simCfg : Cfg n tm.Q) (B : ℕ)
    (hNotHalted : simCfg.state ≠ tm.qhalt) :
    let e := tm.stateEquivK hk
    let iHead := simCfg.input.read
    let wHeads := fun i => (simCfg.work i).read
    let oHead := simCfg.output.read
    let (q', wW, oW, iD, wD, oD) := tm.δ simCfg.state iHead wHeads oHead
    applyTransitionTM.HoareTime
      (fun _inp work _out =>
        stateOnTapeAt k (e simCfg.state) (work utmStateTape) ∧
        superCellsCorrect simCfg (work utmSimTape) ∧
        scratchHasTransOutput k n (e q') wW oW iD wD oD (work utmScratchTape) ∧
        descOnTape desc (work utmDescTape) ∧
        WorkTapesWF work)
      (fun _inp work _out =>
        -- The stepped configuration
        let simCfg' : Cfg n tm.Q :=
          ⟨q', simCfg.input.move iD,
           fun i => (simCfg.work i).writeAndMove (wW i).toΓ (wD i),
           simCfg.output.writeAndMove oW.toΓ oD⟩
        stateOnTapeAt k (e q') (work utmStateTape) ∧
        superCellsCorrect simCfg' (work utmSimTape) ∧
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        (work utmStateTape).head = 1 ∧
        (work utmSimTape).head = 1 ∧
        WorkTapesWF work)
      B := by
  sorry

end TM
