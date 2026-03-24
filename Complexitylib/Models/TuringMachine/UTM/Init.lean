import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs

/-!
# UTM Initialization Machine

Parses the encoded input `⟨M, x⟩` and sets up the UTM's 4 work tapes to
satisfy the simulation invariant `SimInvariant` for the initial configuration
of M on x.

## Main results

- `initTM` — the initialization machine definition
- `initTM_hoareTime` — HoareTime spec: from encoded input to SimInvariant
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Initialization machine (placeholder)
-- ════════════════════════════════════════════════════════════════════════

/-- The initialization machine. Parses `⟨M, x⟩` from the input tape and
    sets up the 4 work tapes to satisfy the simulation invariant for
    `tm.initCfg x`.

    Architecture:
    ```
    initTM =
      seqTM (copyInputToWorkTM 0)        -- A: copy desc to work tape 0
        (seqTM (rewindWorkTM 0)           -- rewind desc tape to cell 1
          (seqTM setupStateTM             -- B: parse header, copy qstart→tape 1, n→tape 3
            (seqTM setupSimTM             -- C: write super-cells, copy x to sim tape
              (seqTM (rewindWorkTM 0)     -- D: rewind all 4 work tapes
                (seqTM (rewindWorkTM 1)
                  (seqTM (rewindWorkTM 2)
                    (rewindWorkTM 3)))))))
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

/-- HoareTime specification for `initTM`.

    **Precondition**: Input tape contains encoded `⟨M, x⟩` via `encodeUTMInput`.
    All tapes start in their initial configuration.

    **Postcondition**: Work tapes satisfy `SimInvariant` for the initial
    configuration `tm.initCfg x`.

    The postcondition is `SimInvariant`, which existentially quantifies
    over `simCfg`. The witness is `tm.initCfg x`. -/
theorem initTM_hoareTime (tm : TM n) (k : ℕ)
    (x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ) :
    let desc := TMEncoding.encodeTM tm
    ∃ B, initTM.HoareTime
      (fun inp work out =>
        inp = initTape (encodeUTMInput tm x) ∧
        work = (fun _ => initTape []) ∧
        out = initTape [])
      (SimInvariant tm k hk desc)
      B := by
  sorry

end TM
