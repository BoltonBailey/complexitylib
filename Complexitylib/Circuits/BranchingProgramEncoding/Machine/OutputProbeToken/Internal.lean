/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.OutputProbeToken.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken

/-!
# Barrington leaf emission after output-probe token decoding -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

private theorem latchFramePost_transition
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) :
    ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false inp work out →
        outputProbeLatchFramePost tm controllerTapes outerExtras input output
          extras false (transitionInput inp)
          (fun i => transitionTape (work i)) (transitionTape out) := by
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  rw [hinput.transitionInput_eq_self]
  have hworkTransition : (fun i => transitionTape (work i)) = work := by
    funext i
    exact (hwork i).transitionTape_eq_self
  rw [hworkTransition, hout.transitionTape_eq_self]
  exact hpost

theorem outputProbeDecodeVarInstrTM_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (output : Tape) (ys : List Bool)
    (houtput : OutAcc ys output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTokenLayout controllerTapes)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (cursor : ℕ) (tag₀ tag₁ tag₂ : Bool)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx))
        |>.HasBinaryNat 0)
    (htag₀Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₀Idx))
        |>.HasBinaryNat 0)
    (htag₁Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₁Idx))
        |>.HasBinaryNat 0)
    (htag₂Zero :
      (outerExtras
        (outputProbeDecodeTagBitIdx n layout.tagLayout.tag₂Idx))
        |>.HasBinaryNat 0)
    (hvalue :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx))
        |>.HasBinaryNat 0)
    (hactive :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.activeIdx))
        |>.HasBinaryNat 1)
    (hloop :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.loopIdx))
        |>.HasBinaryNat 0)
    (fuelValue : ℕ)
    (hfuel :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.natLayout.fuelIdx))
        |>.HasBinaryNat fuelValue)
    (hqueryValid : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).active = true →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).cursor <
          (f input).length)
    (hqueryLimit : ∀ value, value < fuelValue →
      (outputProbeDecodeNatStateAt (f input)
        (outputProbeDecodeTokenVarInitial cursor) value).active = true →
      outputProbeCaptureSpace (max 1 (space input.length))
        ((outputProbeDecodeNatStateAt (f input)
          (outputProbeDecodeTokenVarInitial cursor) value).cursor + 1) ≤
            cleanupLimit)
    (target : Equiv.Perm (Fin 5)) :
    let finalState := outputProbeDecodeNatStateAt (f input)
      (outputProbeDecodeTokenVarInitial cursor) fuelValue
    let finalOuter := outputProbeDecodeNatLoopOuterExtras n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
        tag₀ tag₁ tag₂)
      finalState fuelValue
    ∃ bodyTime : ℕ → ℕ,
      (outputProbeDecodeVarInstrTM tm controllerTapes layout target).HoareTime
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
            tag₀ tag₁ tag₂)
          input output extras false)
        (EmitPred
          (outputProbeLatchFrameCfg tm controllerTapes finalOuter input output
            extras false).input
          (outputProbeLatchFrameCfg tm controllerTapes finalOuter input output
            extras false).work
          (ys ++ Instr.encode ⟨finalState.value, 1, target⟩))
        (outputProbeDecodeVarInstrTime bodyTime fuelValue finalState.value) := by
  dsimp only
  let after := outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras
    cursor tag₀ tag₁ tag₂
  let finalState := outputProbeDecodeNatStateAt (f input)
    (outputProbeDecodeTokenVarInitial cursor) fuelValue
  let finalOuter := outputProbeDecodeNatLoopOuterExtras n
    layout.natLayout.cursorIdx layout.natLayout.valueIdx
    layout.natLayout.activeIdx layout.natLayout.loopIdx after finalState
    fuelValue
  obtain ⟨bodyTime, hdecode⟩ :=
    hcomp.outputProbeDecodeTokenVar_hoareTime input output houtput.parked extras
      hextras hcleanupCounter cleanupLimit hcleanupLimit controllerTapes layout
      outerExtras houter cursor tag₀ tag₁ tag₂ hscratch htag₀Zero
      htag₁Zero htag₂Zero hvalue hactive hloop fuelValue hfuel
      hqueryValid hqueryLimit
  have hafter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (after i) := by
    exact outputProbeDecodeTokenOuterExtrasAfter_parked n layout outerExtras
      houter cursor tag₀ tag₁ tag₂ htag₀Zero htag₁Zero htag₂Zero
  have hfinal : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (finalOuter i) := by
    exact outputProbeDecodeNatLoopOuterExtras_parked n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx after hafter
      finalState fuelValue
  have hscratchAfter :
      (after (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeTokenOuterExtrasAfter n layout outerExtras cursor
      tag₀ tag₁ tag₂ (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0
    rw [outputProbeDecodeTokenOuterExtrasAfter_other n layout outerExtras
      cursor tag₀ tag₁ tag₂ layout.natLayout.scratchIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))]
    exact hscratch
  have hscratchFinal :
      (finalOuter (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0 := by
    change (outputProbeDecodeNatLoopOuterExtras n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx after finalState
      fuelValue (outputProbeIndexedControllerIdx n
        layout.natLayout.scratchIdx)).HasBinaryNat 0
    rw [outputProbeDecodeNatLoopOuterExtras_other n
      layout.natLayout.cursorIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      layout.natLayout.scratchIdx
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide))
      (layout.roles.injective.ne (by decide)) after finalState fuelValue]
    exact hscratchAfter
  have hvalueFinal :
      (finalOuter (outputProbeIndexedControllerIdx n
        layout.natLayout.valueIdx)).HasBinaryNat finalState.value := by
    simpa [finalOuter, outputProbeDecodeNatLoopOuterExtras,
      outputProbeDecodeNatValueIdx] using
      outputProbeDecodeNatStateOuterExtras_value n
        layout.natLayout.cursorIdx layout.natLayout.valueIdx
        layout.natLayout.activeIdx
        (layout.roles.injective.ne (by decide))
        (Function.update after
          (outputProbeIndexedControllerIdx n layout.natLayout.loopIdx)
          (outputProbeCounterTape fuelValue)) finalState
  have hemit := emitInstrTM_latchFrame_hoareTime tm controllerTapes
    layout.natLayout.scratchIdx layout.natLayout.valueIdx
    (layout.roles.injective.ne (by decide)) finalState.value 1 target
    finalOuter input output extras ys hextras hfinal houtput hscratchFinal
    hvalueFinal
  have htransition := latchFramePost_transition tm controllerTapes finalOuter
    input output extras hextras hfinal houtput.parked
  have hrun := seqTM_hoareTime
    (outputProbeDecodeNatTM tm controllerTapes layout.natLayout.cursorIdx
      layout.natLayout.scratchIdx layout.natLayout.valueIdx
      layout.natLayout.activeIdx layout.natLayout.loopIdx
      layout.natLayout.fuelIdx)
    (emitInstrTM
      (outputProbeIndexedControllerIdx n layout.natLayout.scratchIdx)
      (outputProbeIndexedControllerIdx n layout.natLayout.valueIdx) 1 target)
    hdecode htransition hemit
  refine ⟨bodyTime, ?_⟩
  simpa [outputProbeDecodeVarInstrTM, emitVarInstrTM,
    outputProbeDecodeVarInstrTime, after, finalState, finalOuter] using hrun

end Machine

end BPCode

end Complexity
