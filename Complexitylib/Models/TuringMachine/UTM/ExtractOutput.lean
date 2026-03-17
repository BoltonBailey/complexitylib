import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# UTM Extract Output

After the simulation loop terminates, extract the simulated output from the
super-cell encoding and write it to the real output tape.

## Main results

- `extractOutputTM` — the machine definition
- `extractOutputTM_hoareTime` — HoareTime spec: parametric in `simCfg`
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Extract output machine (placeholder)
-- ════════════════════════════════════════════════════════════════════════

/-- Extract the simulated output and write it to the real output tape.
    Scans the sim tape to the output tape's position-1 super-cell, decodes
    the 2-bit symbol, and writes it to real output cell 1. -/
noncomputable def extractOutputTM : TM 4 := writeTM .blank

/-- HoareTime specification for `extractOutputTM`.

    Parametric in `simCfg`. The postcondition says the real output cell 1
    matches the simulated output cell 1.

    **Pre**: Sim tape encodes `simCfg`; output tape is WF.
    **Post**: Real output cell 1 = `simCfg.output.cells 1`. -/
theorem extractOutputTM_hoareTime {Q : Type} [Fintype Q] [DecidableEq Q]
    (simCfg : Cfg n Q) (B : ℕ) :
    extractOutputTM.HoareTime
      (fun _inp work out =>
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        out.head ≤ B)
      (fun _inp _work out =>
        out.cells 1 = simCfg.output.cells 1)
      (B + 3 * (n + 2) + 5) := by
  sorry

end TM
