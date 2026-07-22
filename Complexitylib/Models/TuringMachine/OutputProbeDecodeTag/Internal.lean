/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.OutputProbeDecodeTag.Defs
import Complexitylib.Models.TuringMachine.OutputProbeCountOnes
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Decoding fixed formula-token tags through output probes -- internals
-/

namespace Complexity

namespace TM

private theorem outputProbeDecodeTagSkipTM_isTransducer_internal {n : ℕ} :
    (skipTM (n := n)).IsTransducer := by
  intro state _iHead _wHeads oHead
  cases state <;> cases oHead <;> simp [skipTM, idleDir]

theorem outputProbeDecodeTag?_ofList_internal (bits : List Bool)
    (cursor : ℕ) :
    outputProbeDecodeTag? (FormulaCode.BitOracle.ofList bits) cursor = (do
      let tag₀ ← bits[cursor]?
      let tag₁ ← bits[cursor + 1]?
      let tag₂ ← bits[cursor + 2]?
      let tag ← outputProbeTokenTag? tag₀ tag₁ tag₂
      some (tag, cursor + 3)) := by
  rfl

theorem outputProbeDecodeTag?_fixed_token_internal
    (query : FormulaCode.BitOracle) (cursor bitFuel : ℕ)
    (tag : OutputProbeTokenTag) (nextCursor : ℕ)
    (hdecode : outputProbeDecodeTag? query cursor =
      some (tag, nextCursor)) :
    match tag with
    | .var => True
    | .tru => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.tru, nextCursor)
    | .fls => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.fls, nextCursor)
    | .neg => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.neg, nextCursor)
    | .conj => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.conj, nextCursor)
    | .disj => FormulaCode.BitOracle.decodeTokenAt? query bitFuel cursor =
        some (.disj, nextCursor) := by
  cases tag <;> simp only
  all_goals
    unfold outputProbeDecodeTag? at hdecode
    generalize htag₀ : query cursor = tag₀ at hdecode ⊢
    cases tag₀ with
    | none => simp at hdecode
    | some tag₀ =>
        generalize htag₁ : query (cursor + 1) = tag₁ at hdecode ⊢
        cases tag₁ with
        | none => simp at hdecode
        | some tag₁ =>
            generalize htag₂ : query (cursor + 2) = tag₂ at hdecode ⊢
            cases tag₂ with
            | none => simp at hdecode
            | some tag₂ =>
                cases tag₀ <;> cases tag₁ <;> cases tag₂ <;>
                  simp_all [outputProbeTokenTag?,
                    FormulaCode.BitOracle.decodeTokenAt?]

private theorem outputProbeDecodeTagCounterTape_parked_internal
    (value : ℕ) : Parked (outputProbeCounterTape value) := by
  have h : (outputProbeCounterTape value).HasBinaryNat value := by
    simpa [outputProbeCounterTape] using
      Tape.init_move_right_hasBinaryNat value
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem outputProbeDecodeTagUpdateOuter_parked_internal
    (n : ℕ) {controllerTapes : ℕ}
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (idx : Fin controllerTapes) (value : ℕ) :
    ∀ i, ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
      Parked (Function.update outerExtras
        (outputProbeIndexedControllerIdx n idx)
        (outputProbeCounterTape value) i) := by
  intro i hi
  by_cases heq : i = outputProbeIndexedControllerIdx n idx
  · subst i
    rw [Function.update_self]
    exact outputProbeDecodeTagCounterTape_parked_internal value
  · rw [Function.update_of_ne heq]
    exact houter i hi

private theorem outputProbeDecodeTagSucc_hoareTime_internal
    (tm : TM n) (controllerTapes : ℕ)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (input : List Bool) (output : Tape)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (houtput : Parked output) (idx : Fin controllerTapes) (value : ℕ)
    (hvalue :
      (outerExtras (outputProbeIndexedControllerIdx n idx)).HasBinaryNat
        value) :
    (binarySuccTM
      (outputProbeIndexedControllerIdx n idx)).HoareTime
      (outputProbeLatchFramePost tm controllerTapes outerExtras input output
        extras false)
      (outputProbeLatchFramePost tm controllerTapes
        (Function.update outerExtras
          (outputProbeIndexedControllerIdx n idx)
          (outputProbeCounterTape (value + 1)))
        input output extras false)
      (binarySuccTime value) := by
  let physical := outputProbeIndexedControllerIdx n idx
  let nextTape := outputProbeCounterTape (value + 1)
  intro inp work out hpost
  obtain ⟨hinput, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
    controllerTapes outerExtras input output extras false hextras houter
    houtput inp work out hpost
  have htarget : (work physical).HasBinaryNat value := by
    rw [outputProbeLatchFramePost_controller tm controllerTapes outerExtras
      input output extras false inp work out hpost idx]
    exact hvalue
  obtain ⟨done, hreach, hhalt, hinputDone, hotherDone, htargetDone,
      houtputDone⟩ :=
    binarySuccTM_reachesIn_frame physical value inp work out htarget
      hinput.read_ne_start (fun i _ => (hwork i).read_ne_start)
      hout.read_ne_start
  have hworkDone : done.work = Function.update work physical nextTape := by
    funext i
    by_cases hi : i = physical
    · subst i
      rw [Function.update_self]
      exact htargetDone.eq_init_move_right
    · rw [Function.update_of_ne hi]
      exact hotherDone i hi
  refine ⟨done, binarySuccTime value, le_rfl, hreach, hhalt, ?_⟩
  rw [hinputDone, hworkDone, houtputDone]
  simpa [physical, nextTape] using
    outputProbeLatchFramePost_updateController tm controllerTapes outerExtras
      input output extras false inp work out hpost idx nextTape

theorem ComputesInSpace.outputProbeDecodeTagBitTM_hoareTime_internal
    {tm : TM n} {f : List Bool → List Bool} {space : ℕ → ℕ}
    (hcomp : tm.ComputesInSpace f space)
    (input : List Bool) (cursor : ℕ)
    (hcursorBound : cursor < (f input).length)
    (output : Tape) (houtput : Parked output)
    (extras : Fin (outputProbeControllerTapes n) → Tape)
    (hextras : ∀ i, ¬placeWorkInMiddle 0 (n + 2) i → Parked (extras i))
    (hcleanupCounter :
      (extras (outputProbeCleanupCounterIdx n)).HasBinaryNat 0)
    (cleanupLimit : ℕ)
    (hcleanupLimit :
      (extras (outputProbeCleanupLimitIdx n)).HasBinaryNat cleanupLimit)
    (hlimit : outputProbeCaptureSpace (max 1 (space input.length))
      (cursor + 1) ≤ cleanupLimit)
    (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes)
    (hcursorScratch : layout.cursorIdx ≠ layout.scratchIdx)
    (hcursorBit : layout.cursorIdx ≠ bitIdx)
    (outerExtras : Fin (0 + outputProbeControllerTapes n +
      controllerTapes) → Tape)
    (houter : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (outerExtras i))
    (hcursor :
      (outerExtras (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        cursor)
    (hscratch :
      (outerExtras
        (outputProbeIndexedControllerIdx n layout.scratchIdx)).HasBinaryNat
          0)
    (hbit :
      (outerExtras (outputProbeDecodeTagBitIdx n bitIdx)).HasBinaryNat 0) :
    ∃ (bodyBound : ℕ)
      (pre : TapePred
        (0 + outputProbeControllerTapes n + controllerTapes)),
      pre
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).input
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).work
        (outputProbeLatchFrameCfg tm controllerTapes outerExtras input output
          extras false).output ∧
      (outputProbeDecodeTagBitTM tm controllerTapes layout bitIdx).HoareTime
        pre
        (outputProbeLatchFramePost tm controllerTapes
          (outputProbeDecodeTagBitOuterExtrasAfter n layout bitIdx outerExtras
            cursor ((f input)[cursor]'hcursorBound))
          input output extras false)
        (bodyBound + 1 + binarySuccTime cursor) := by
  let bit := (f input)[cursor]'hcursorBound
  let afterBit := outputProbeCountOnesOuterExtrasAfter n bitIdx outerExtras 0
    bit
  obtain ⟨bodyBound, pre, hpre, hbody⟩ :=
    hcomp.outputProbeCountOnesBodyTM_hoareTime input cursor hcursorBound output
      houtput extras hextras hcleanupCounter cleanupLimit hcleanupLimit hlimit
      controllerTapes outerExtras houter layout.cursorIdx layout.scratchIdx
      bitIdx hcursorScratch hcursor hscratch 0 hbit
  have hafterParked : ∀ i,
      ¬placeWorkInMiddle 0 (outputProbeControllerTapes n) i →
        Parked (afterBit i) := by
    by_cases hbitValue : bit
    · simpa [afterBit, outputProbeCountOnesOuterExtrasAfter, hbitValue] using
        outputProbeDecodeTagUpdateOuter_parked_internal n outerExtras houter
          bitIdx 1
    · simpa [afterBit, outputProbeCountOnesOuterExtrasAfter, hbitValue] using
        houter
  have hcursorAfter :
      (afterBit (outputProbeDecodeTagCursorIdx n layout)).HasBinaryNat
        cursor := by
    have hphysical : outputProbeDecodeTagCursorIdx n layout ≠
        outputProbeIndexedControllerIdx n bitIdx := by
      intro heq
      exact hcursorBit (outputProbeIndexedControllerIdx_injective n heq)
    by_cases hbitValue : bit
    · simpa [afterBit, outputProbeCountOnesOuterExtrasAfter, hbitValue,
        hphysical] using hcursor
    · simpa [afterBit, outputProbeCountOnesOuterExtrasAfter, hbitValue] using
        hcursor
  have hsucc := outputProbeDecodeTagSucc_hoareTime_internal tm
    controllerTapes afterBit input output extras hextras hafterParked houtput
    layout.cursorIdx cursor hcursorAfter
  have htransition : ∀ inp work out,
      outputProbeLatchFramePost tm controllerTapes afterBit input output
          extras false inp work out →
        outputProbeLatchFramePost tm controllerTapes afterBit input output
          extras false (transitionInput inp)
          (fun i => transitionTape (work i)) (transitionTape out) := by
    intro inp work out hpost
    obtain ⟨hinp, hwork, hout⟩ := outputProbeLatchFramePost_parked tm
      controllerTapes afterBit input output extras false hextras hafterParked
      houtput inp work out hpost
    rw [hinp.transitionInput_eq_self]
    have hworkTransition : (fun i => transitionTape (work i)) = work := by
      funext i
      exact (hwork i).transitionTape_eq_self
    rw [hworkTransition, hout.transitionTape_eq_self]
    exact hpost
  refine ⟨bodyBound, pre, hpre, ?_⟩
  simpa [outputProbeDecodeTagBitTM,
    outputProbeDecodeTagBitOuterExtrasAfter, afterBit, bit,
    outputProbeDecodeTagCursorIdx] using
    seqTM_hoareTime
      (outputProbeCountOnesBodyTM tm controllerTapes layout.cursorIdx
        layout.scratchIdx bitIdx)
      (binarySuccTM (outputProbeDecodeTagCursorIdx n layout))
      hbody htransition hsucc

theorem outputProbeDecodeTagBitTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes)
    (bitIdx : Fin controllerTapes) :
    (outputProbeDecodeTagBitTM tm controllerTapes layout
      bitIdx).IsTransducer := by
  apply IsTransducer.seqTM
  · apply IsTransducer.outputProbeIndexedResetDispatchTM
    · exact outputProbeDecodeTagSkipTM_isTransducer_internal
    · exact binarySuccTM_isTransducer _
  · exact binarySuccTM_isTransducer _

theorem outputProbeDecodeTagTM_isTransducer_internal
    (tm : TM n) (controllerTapes : ℕ)
    (layout : OutputProbeDecodeTagLayout controllerTapes) :
    (outputProbeDecodeTagTM tm controllerTapes layout).IsTransducer := by
  apply IsTransducer.seqTM
  · exact outputProbeDecodeTagBitTM_isTransducer_internal tm controllerTapes
      layout layout.tag₀Idx
  · apply IsTransducer.seqTM
    · exact outputProbeDecodeTagBitTM_isTransducer_internal tm controllerTapes
        layout layout.tag₁Idx
    · exact outputProbeDecodeTagBitTM_isTransducer_internal tm controllerTapes
        layout layout.tag₂Idx

end TM

end Complexity
