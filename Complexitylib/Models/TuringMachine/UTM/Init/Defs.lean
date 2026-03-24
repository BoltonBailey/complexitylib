import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# UTM Initialization Machine — Definition

Extracted to break the import cycle between `Init.lean` (surface) and
`InitInternal.lean` (proofs).
-/

namespace TM

variable {n : ℕ}

/-- The initialization machine. Parses `⟨M, x⟩` from the input tape and
    sets up the 4 work tapes to satisfy the simulation invariant for
    `tm.initCfg x`.

    Architecture:
    ```
    initTM =
      seqTM (copyInputToWorkTM 0)        -- A: copy desc to work tape 0
        (seqTM (rewindWorkTM 0)           -- rewind desc tape to cell 1
          (seqTM setupStateTM             -- B: parse header, copy qstart→tape 1, n→tape 3
            (seqTM (rewindWorkTM 3)       -- rewind scratch tape to cell 1
              (seqTM setupSimTM           -- C: write super-cells, copy x to sim tape
                (seqTM (rewindWorkTM 0)   -- D: rewind all 4 work tapes
                  (seqTM (rewindWorkTM 1)
                    (seqTM (rewindWorkTM 2)
                      (rewindWorkTM 3))))))))
    ```

    Phase A copies the TM description from input to work tape 0, stopping at
    the `Γ.blank` separator. Phase B parses the header (k, n), copies qstart
    to the state tape, and writes n to scratch. The scratch rewind brings
    scratch head back to cell 1 (from n+1 after Phase B). Phase C sets up the
    simulation tape super-cells and copies x. Phase D rewinds all work tape
    heads to cell 1. -/
def initTM : TM 4 :=
  seqTM (copyInputToWorkTM (0 : Fin 4))
    (seqTM (rewindWorkTM (0 : Fin 4))
      (seqTM setupStateTM
        (seqTM (rewindWorkTM (3 : Fin 4))
          (seqTM setupSimTM
            (seqTM (rewindWorkTM (0 : Fin 4))
              (seqTM (rewindWorkTM (1 : Fin 4))
                (seqTM (rewindWorkTM (2 : Fin 4))
                  (rewindWorkTM (3 : Fin 4)))))))))

end TM
