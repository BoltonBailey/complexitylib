import Complexitylib.Models.TuringMachine.UTM.Init.Defs
import Complexitylib.Models.TuringMachine.UTM.InitInternal

/-!
# UTM Initialization Machine

Parses the encoded input `⟨M, x⟩` and sets up the UTM's 4 work tapes to
satisfy the simulation invariant `SimInvariant` for the initial configuration
of M on x.

## Main results

- `initTM` — the initialization machine definition (in `Init.Defs`)
- `initTM_hoareTime_exact` — exact HoareTime spec for the initialized encoding
- `initTM_hoareTime` — HoareTime spec: from encoded input to SimInvariant
-/

namespace TM

variable {n : ℕ}

/-- HoareTime specification for `initTM`.

    **Precondition**: Input tape contains encoded `⟨M, x⟩` via `encodeUTMInput`.
    All tapes start in their initial configuration.

    **Postcondition**: The work tapes contain the exact initialized encoding
    of `tm.initCfg x`, the work heads are rewound to cell 1, the scratch tail
    past cell `n + 1` is blank, and the input/output well-formedness facts are
    preserved via `InitEnvelope`. -/
theorem initTM_hoareTime_exact (tm : TM n) (k : ℕ)
    (x : List Bool)
    (hk : k = @Fintype.card tm.Q tm.finQ) :
    let desc := TMEncoding.encodeTM tm
    ∃ B, initTM.HoareTime
      (fun inp work out =>
        inp = initTape (encodeUTMInput tm x) ∧
        work = (fun _ => initTape []) ∧
        out = initTape [])
      (fun inp work out =>
        InitEnvelope inp work out ∧
        descOnTape desc (work utmDescTape) ∧
        stateOnTapeAt k (tm.stateEquivK hk tm.qstart) (work utmStateTape) ∧
        superCellsCorrect (tm.initCfg x) (work utmSimTape) ∧
        (∀ i, (work i).head = 1) ∧
        (∀ j, j ≥ n + 1 → (work utmScratchTape).cells j = Γ.blank))
      B :=
  initTM_hoareTime_exact' tm k x hk

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
      B :=
  initTM_hoareTime' tm k x hk

end TM
