import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Init.Defs
import Complexitylib.Models.TuringMachine.UTM.ReadCurrent
import Complexitylib.Models.TuringMachine.UTM.Lookup
import Complexitylib.Models.TuringMachine.UTM.ApplyTransition
import Complexitylib.Models.TuringMachine.UTM.CheckHalt
import Complexitylib.Models.TuringMachine.UTM.ExtractOutput

/-!
# UTM Machine Definitions

Defines the Universal Turing Machine and its components as concrete `TM` values.
These definitions are separated from the correctness proofs to allow the proof
internals (SimLoop) to import them without circular dependencies.

## Main definitions

- `utmSimStepTM` — one simulation step (readCurrent ; lookup ; applyTransition)
- `utmTM` — the full UTM (init ; loop(simStep, checkHalt) ; extractOutput)
- `utmInitCfg` — the UTM's initial configuration with encoded input
-/

namespace TM

variable {n : ℕ}

/-- The simulation step machine performs one step of the simulated TM.
    Composed as: readCurrentTM ; lookupTM ; applyTransitionTM.
    Parametric in `k` (number of states of the simulated TM). -/
noncomputable def utmSimStepTM (k : ℕ) : TM 4 :=
  seqTM (readCurrentTM (n := n)) (seqTM (lookupTM (n := n) k) (applyTransitionTM (n := n) k))

/-- The Universal Turing Machine.
    Architecture: initTM ; loop(simStepTM, checkHaltTM) ; extractOutputTM.
    Parametric in `k` (number of states of the simulated TM). -/
noncomputable def utmTM (k : ℕ) : TM 4 :=
  seqTM initTM
    (seqTM (loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM)
      (extractOutputTM (n := n)))

/-- The UTM's initial configuration with input `⟨M, x⟩` encoded as `List Γ`.
    Uses `initTape` directly since `encodeUTMInput` returns `List Γ`
    (not `List Bool`), which already includes the blank separator. -/
noncomputable def utmInitCfg (tm : TM n) (k : ℕ) (x : List Bool) :
    Cfg 4 (utmTM (n := n) k).Q :=
  { state := (utmTM (n := n) k).qstart,
    input := initTape (encodeUTMInput tm x),
    work := fun _ => initTape [],
    output := initTape [] }

end TM
