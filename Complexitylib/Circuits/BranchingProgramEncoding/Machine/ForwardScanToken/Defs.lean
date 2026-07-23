/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScan.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken.Defs

/-!
# Token decoding for the forward postfix scan -- definitions

This layer connects complete formula-token decoding to the numeric forward
scan controller. The source cursor is shared between both phases, while every
other decoder and scan register is structurally distinct.
-/

namespace Complexity

namespace BPCode

namespace Machine

/-- Sixteen distinct controller roles used by one decoded forward-scan step.

Roles zero through eight are the complete token decoder. Role zero is also the
scan cursor. Roles nine through fifteen are the remaining seven scan roles. -/
structure ForwardScanTokenLayout (controllerTapes : ℕ) where
  /-- Injective assignment of logical roles to controller tapes. -/
  roles : Fin 16 ↪ Fin controllerTapes

/-- Restrict the combined layout to the complete nine-role token decoder. -/
def ForwardScanTokenLayout.tokenLayout
    (layout : ForwardScanTokenLayout controllerTapes) :
    TM.OutputProbeDecodeTokenLayout controllerTapes where
  roles :=
    { toFun := fun i => layout.roles ⟨i.val, by omega⟩
      inj' := by
        intro i j hij
        have hroles := congrArg Fin.val (layout.roles.injective hij)
        exact Fin.ext (by simpa using hroles) }

/-- Map the shared cursor and seven private scan roles into controller space. -/
def ForwardScanTokenLayout.scanControllerRole
    (layout : ForwardScanTokenLayout controllerTapes) (i : Fin 8) :
    Fin controllerTapes :=
  layout.roles
    ⟨if i.val = 0 then 0 else i.val + 8, by
      split <;> omega⟩

/-- Restrict the combined layout to the eight physical work tapes used by the
numeric scan. The logical controller roles are embedded after the output-probe
machine's private middle block. -/
def ForwardScanTokenLayout.scanLayout (n : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    ForwardScanLayout
      (0 + TM.outputProbeControllerTapes n + controllerTapes) where
  roles :=
    { toFun := fun i => TM.outputProbeIndexedControllerIdx n
        (layout.scanControllerRole i)
      inj' := by
        intro i j hij
        have hphysical := congrArg Fin.val hij
        have hcontroller : layout.scanControllerRole i =
            layout.scanControllerRole j := by
          apply Fin.ext
          simp only [TM.outputProbeIndexedControllerIdx] at hphysical
          omega
        have hroles := congrArg Fin.val (layout.roles.injective hcontroller)
        apply Fin.ext
        by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;>
          simp [hi, hj] at hroles <;>
          omega }

/-- Literal controller work family after normalizing a completed variable
decoder for the next token. -/
def forwardScanVarResetWork (n : ℕ) {controllerTapes : ℕ}
    (layout : ForwardScanTokenLayout controllerTapes)
    (work : Fin (0 + TM.outputProbeControllerTapes n + controllerTapes) →
      Tape) :
    Fin (0 + TM.outputProbeControllerTapes n + controllerTapes) → Tape :=
  let token := layout.tokenLayout
  Function.update
    (Function.update
      (Function.update work
        (TM.outputProbeIndexedControllerIdx n token.natLayout.valueIdx)
        ((Tape.init []).move Dir3.right))
      (TM.outputProbeIndexedControllerIdx n token.natLayout.activeIdx)
      ((Tape.init ((1 : ℕ).bits.map Γ.ofBool)).move Dir3.right))
    (TM.outputProbeIndexedControllerIdx n token.natLayout.loopIdx)
    ((Tape.init []).move Dir3.right)

/-- Clear the decoded variable value, restore the active flag to one, and
clear the completed bounded-loop counter. -/
def forwardScanVarResetTM (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    TM (0 + TM.outputProbeControllerTapes n + controllerTapes) :=
  let token := layout.tokenLayout
  TM.seqTM
    (TM.clearWorkTM
      (TM.outputProbeIndexedControllerIdx n token.natLayout.valueIdx))
    (TM.seqTM
      (TM.binarySuccTM
        (TM.outputProbeIndexedControllerIdx n token.natLayout.activeIdx))
      (TM.clearWorkTM
        (TM.outputProbeIndexedControllerIdx n token.natLayout.loopIdx)))

/-- Exact runtime of variable-decoder normalization. -/
def forwardScanVarResetTime (value fuel : ℕ) : ℕ :=
  TM.clearWorkTimeBound value.bits.length + 1 +
    (TM.binarySuccTime 0 + 1 + TM.clearWorkTimeBound fuel.bits.length)

/-- Decode a terminated-unary variable payload, normalize its private decoder
registers, and apply the leaf update to the forward scan. -/
def forwardScanVarTokenStepTM (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    TM (0 + TM.outputProbeControllerTapes n + controllerTapes) :=
  let token := layout.tokenLayout
  TM.seqTM
    (TM.outputProbeDecodeNatTM tm controllerTapes token.natLayout.cursorIdx
      token.natLayout.scratchIdx token.natLayout.valueIdx
      token.natLayout.activeIdx token.natLayout.loopIdx
      token.natLayout.fuelIdx)
    (TM.seqTM (forwardScanVarResetTM n controllerTapes layout)
      (forwardScanTokenStepTM (layout.scanLayout n) 0))

/-- Decode one complete formula token and apply its postfix arity update.
Invalid tags are a no-op; promised canonical formula codes never select that
branch. -/
def forwardScanDecodedTokenTM (tm : TM n) (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    TM (0 + TM.outputProbeControllerTapes n + controllerTapes) :=
  TM.outputProbeDecodeTokenTM tm controllerTapes layout.tokenLayout
    (forwardScanVarTokenStepTM tm controllerTapes layout)
    (forwardScanTokenStepTM (layout.scanLayout n) 0)
    (forwardScanTokenStepTM (layout.scanLayout n) 0)
    (forwardScanTokenStepTM (layout.scanLayout n) 1)
    (forwardScanTokenStepTM (layout.scanLayout n) 2)
    (forwardScanTokenStepTM (layout.scanLayout n) 2)
    TM.skipTM

end Machine

end BPCode

end Complexity
