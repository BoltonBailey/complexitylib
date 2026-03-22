import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# UTM Transition Lookup

Linear-scan lookup of the matching transition entry in the encoded
description on work tape 0.

## Main results

- `lookupTM` — the lookup machine definition
- `lookupTM_hoareTime` — HoareTime spec: parametric in state and symbols
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Lookup machine (placeholder)
-- ════════════════════════════════════════════════════════════════════════

/-- Scan the description tape for a matching transition entry.
    Compares each entry's input pattern against the scratch tape,
    then copies the matching entry's output to scratch. -/
noncomputable def lookupTM : TM 4 := writeTM .blank

/-- HoareTime specification for `lookupTM`.

    Parametric in the current state `q` and head symbols. The postcondition
    provides the transition output for `tm.δ(e.symm q, iHead, wHeads, oHead)`.

    The key correctness property: the self-describing transition table is
    guaranteed to contain an entry for every valid (state, symbols) tuple,
    so the linear scan always finds a match.

    **Pre**: Desc tape valid + head at 1; scratch has input pattern.
    **Post**: Desc tape preserved; scratch has transition output from δ. -/
theorem lookupTM_hoareTime (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ) (desc : List Bool)
    (q : Fin k) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ) (B : ℕ) :
    let e := tm.stateEquivK hk
    lookupTM.HoareTime
      (fun _inp work _out =>
        descOnTape desc (work utmDescTape) ∧
        (work utmDescTape).head = 1 ∧
        scratchHasInputPattern k n q iHead wHeads oHead (work utmScratchTape) ∧
        WorkTapesWF work)
      (fun _inp work _out =>
        let (q', wW, oW, iD, wD, oD) := tm.δ (e.symm q) iHead wHeads oHead
        descOnTape desc (work utmDescTape) ∧
        scratchHasTransOutput k n (e q') wW oW iD wD oD (work utmScratchTape) ∧
        (work utmDescTape).head = 1 ∧
        WorkTapesWF work)
      B := by
  sorry

end TM
