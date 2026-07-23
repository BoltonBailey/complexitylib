/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScan
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScanToken.Defs
import Complexitylib.Models.TuringMachine.OutputProbeDecodeToken
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Token decoding for the forward postfix scan -- proof internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

theorem ForwardScanTokenLayout.scanLayout_cursorIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).cursorIdx =
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.tagLayout.cursorIdx := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_heightIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).heightIdx =
      outputProbeIndexedControllerIdx n (layout.roles 9) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_tokenCountIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).tokenCountIdx =
      outputProbeIndexedControllerIdx n (layout.roles 10) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_lastOneCountIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).lastOneCountIdx =
      outputProbeIndexedControllerIdx n (layout.roles 11) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_lastOneCursorIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).lastOneCursorIdx =
      outputProbeIndexedControllerIdx n (layout.roles 12) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_oneIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).oneIdx =
      outputProbeIndexedControllerIdx n (layout.roles 13) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_resultIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).resultIdx =
      outputProbeIndexedControllerIdx n (layout.roles 14) := by
  rfl

@[simp]
theorem ForwardScanTokenLayout.scanLayout_copyScratchIdx_internal
    (layout : ForwardScanTokenLayout controllerTapes) :
    (layout.scanLayout n).copyScratchIdx =
      outputProbeIndexedControllerIdx n (layout.roles 15) := by
  rfl

private theorem ForwardScanTokenLayout.scanRole_ne_tokenRole
    (layout : ForwardScanTokenLayout controllerTapes) (n : ℕ)
    (i : Fin 8) (j : Fin 9) (hj : 5 ≤ j.val) :
    (layout.scanLayout n).roles i ≠
      outputProbeIndexedControllerIdx n (layout.tokenLayout.roles j) := by
  intro heq
  have hcontroller : layout.scanControllerRole i =
      layout.tokenLayout.roles j :=
    outputProbeIndexedControllerIdx_injective n heq
  have hcombined :
      layout.roles
          ⟨if i.val = 0 then 0 else i.val + 8, by split <;> omega⟩ =
        layout.roles ⟨j.val, by omega⟩ := by
    simpa only [ForwardScanTokenLayout.scanControllerRole,
      ForwardScanTokenLayout.tokenLayout] using hcontroller
  have hindices :
      (⟨if i.val = 0 then 0 else i.val + 8, by split <;> omega⟩ : Fin 16) =
        ⟨j.val, by omega⟩ :=
    layout.roles.injective hcombined
  have hroles : (if i.val = 0 then 0 else i.val + 8) = j.val :=
    congrArg Fin.val hindices
  by_cases hi : i.val = 0
  · simp [hi] at hroles
    omega
  · simp [hi] at hroles
    omega

theorem forwardScanVarResetWork_scanRole_internal (n : ℕ)
    {controllerTapes : ℕ}
    (layout : ForwardScanTokenLayout controllerTapes)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (i : Fin 8) :
    forwardScanVarResetWork n layout work ((layout.scanLayout n).roles i) =
      work ((layout.scanLayout n).roles i) := by
  have hvalue := layout.scanRole_ne_tokenRole n i 5 (by decide)
  have hactive := layout.scanRole_ne_tokenRole n i 6 (by decide)
  have hloop := layout.scanRole_ne_tokenRole n i 7 (by decide)
  have hvalue' : (layout.scanLayout n).roles i ≠
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.valueIdx := by
    simpa only [OutputProbeDecodeTokenLayout.natLayout_valueIdx] using hvalue
  have hactive' : (layout.scanLayout n).roles i ≠
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.activeIdx := by
    simpa only [OutputProbeDecodeTokenLayout.natLayout_activeIdx] using hactive
  have hloop' : (layout.scanLayout n).roles i ≠
      outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.loopIdx := by
    simpa only [OutputProbeDecodeTokenLayout.natLayout_loopIdx] using hloop
  simp only [forwardScanVarResetWork, Function.update_of_ne hvalue',
    Function.update_of_ne hactive', Function.update_of_ne hloop']

theorem ForwardScanFrame.forwardScanVarResetWork_internal
    (layout : ForwardScanTokenLayout controllerTapes)
    (cursor height tokenCount lastOneCount lastOneCursor : ℕ)
    (work : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (hframe : ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor work) :
    ForwardScanFrame (layout.scanLayout n) cursor height tokenCount
      lastOneCount lastOneCursor (forwardScanVarResetWork n layout work) := by
  rcases hframe with ⟨hcursor, hheight, hcount, hlastCount, hlastCursor,
    hone, hresult, hscratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ForwardScanLayout.cursorIdx,
      forwardScanVarResetWork_scanRole_internal] using hcursor
  · simpa only [ForwardScanLayout.heightIdx,
      forwardScanVarResetWork_scanRole_internal] using hheight
  · simpa only [ForwardScanLayout.tokenCountIdx,
      forwardScanVarResetWork_scanRole_internal] using hcount
  · simpa only [ForwardScanLayout.lastOneCountIdx,
      forwardScanVarResetWork_scanRole_internal] using hlastCount
  · simpa only [ForwardScanLayout.lastOneCursorIdx,
      forwardScanVarResetWork_scanRole_internal] using hlastCursor
  · simpa only [ForwardScanLayout.oneIdx,
      forwardScanVarResetWork_scanRole_internal] using hone
  · simpa only [ForwardScanLayout.resultIdx,
      forwardScanVarResetWork_scanRole_internal] using hresult
  · simpa only [ForwardScanLayout.copyScratchIdx,
      forwardScanVarResetWork_scanRole_internal] using hscratch

private theorem parked_of_hasBinaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

theorem forwardScanVarResetTM_hoareTime_internal (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes)
    (value fuel : ℕ)
    (inp₀ : Tape)
    (work₀ : Fin (0 + outputProbeControllerTapes n + controllerTapes) →
      Tape)
    (out₀ : Tape)
    (hvalue :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.valueIdx)).HasBinaryNat value)
    (hactive :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.activeIdx)).HasBinaryNat 0)
    (hloop :
      (work₀ (outputProbeIndexedControllerIdx n
        layout.tokenLayout.natLayout.loopIdx)).HasBinaryNat fuel)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanVarResetTM n controllerTapes layout).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = forwardScanVarResetWork n layout work₀ ∧
        out = out₀)
      (forwardScanVarResetTime value fuel) := by
  let token := layout.tokenLayout
  let valueIdx := outputProbeIndexedControllerIdx n token.natLayout.valueIdx
  let activeIdx := outputProbeIndexedControllerIdx n token.natLayout.activeIdx
  let loopIdx := outputProbeIndexedControllerIdx n token.natLayout.loopIdx
  have hvalueActive : valueIdx ≠ activeIdx := by
    apply (outputProbeIndexedControllerIdx_injective n).ne
    rw [OutputProbeDecodeTokenLayout.natLayout_valueIdx,
      OutputProbeDecodeTokenLayout.natLayout_activeIdx]
    exact token.roles.injective.ne (by decide)
  have hvalueLoop : valueIdx ≠ loopIdx := by
    apply (outputProbeIndexedControllerIdx_injective n).ne
    rw [OutputProbeDecodeTokenLayout.natLayout_valueIdx,
      OutputProbeDecodeTokenLayout.natLayout_loopIdx]
    exact token.roles.injective.ne (by decide)
  have hactiveLoop : activeIdx ≠ loopIdx := by
    apply (outputProbeIndexedControllerIdx_injective n).ne
    rw [OutputProbeDecodeTokenLayout.natLayout_activeIdx,
      OutputProbeDecodeTokenLayout.natLayout_loopIdx]
    exact token.roles.injective.ne (by decide)
  let work₁ := Function.update work₀ valueIdx
    ((Tape.init []).move Dir3.right)
  have hclearValue := clearWorkTM_hoareTime_frame valueIdx value.bits inp₀
    work₀ out₀ hvalue.eq_init_move_right hinput (fun i _ => hwork i)
    houtput
  have hclearValue' : (clearWorkTM valueIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      (clearWorkTimeBound value.bits.length) := by
    simpa [work₁] using hclearValue
  have hwork₁ : ∀ i, Parked (work₁ i) := by
    intro i
    by_cases hi : i = valueIdx
    · subst i
      simp only [work₁, Function.update_self]
      exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat 0)
    simpa only [work₁, Function.update_of_ne hi] using hwork i
  have hactive₁ : (work₁ activeIdx).HasBinaryNat 0 := by
    simpa only [work₁, Function.update_of_ne hvalueActive.symm] using hactive
  let work₂ := Function.update work₁ activeIdx
    ((Tape.init ((1 : ℕ).bits.map Γ.ofBool)).move Dir3.right)
  have hsucc := binarySuccTM_hoareTime_frame activeIdx 0 inp₀ work₁ out₀
    hactive₁ hinput.read_ne_start (fun i hi => (hwork₁ i).read_ne_start)
    houtput.read_ne_start
  have hsucc' : (binarySuccTM activeIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      (binarySuccTime 0) := by
    refine hsucc.strengthen_post (fun inp work out hpost => ?_)
    rcases hpost with ⟨rfl, hother, hone, rfl⟩
    refine ⟨rfl, ?_, rfl⟩
    apply funext
    intro i
    by_cases hi : i = activeIdx
    · subst i
      simp only [work₂, Function.update_self]
      exact hone.eq_init_move_right
    simpa only [work₂, Function.update_of_ne hi] using hother i hi
  have hwork₂ : ∀ i, Parked (work₂ i) := by
    intro i
    by_cases hi : i = activeIdx
    · subst i
      simp only [work₂, Function.update_self]
      exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat 1)
    simpa only [work₂, Function.update_of_ne hi] using hwork₁ i
  have hloop₂ : (work₂ loopIdx).HasBinaryNat fuel := by
    simp only [work₂, Function.update_of_ne hactiveLoop.symm]
    simpa only [work₁, Function.update_of_ne hvalueLoop.symm] using hloop
  let work₃ := Function.update work₂ loopIdx
    ((Tape.init []).move Dir3.right)
  have hclearLoop := clearWorkTM_hoareTime_frame loopIdx fuel.bits inp₀ work₂
    out₀ hloop₂.eq_init_move_right hinput (fun i _ => hwork₂ i) houtput
  have hclearLoop' : (clearWorkTM loopIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₃ ∧ out = out₀)
      (clearWorkTimeBound fuel.bits.length) := by
    simpa [work₃] using hclearLoop
  have htransition₁ : ∀ inp work out,
      (inp = inp₀ ∧ work = work₁ ∧ out = out₀) →
      (transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₁ ∧
        transitionTape out = out₀) := by
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact ⟨hinput.transitionInput_eq_self,
      funext fun i => (hwork₁ i).transitionTape_eq_self,
      houtput.transitionTape_eq_self⟩
  have htransition₂ : ∀ inp work out,
      (inp = inp₀ ∧ work = work₂ ∧ out = out₀) →
      (transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₂ ∧
        transitionTape out = out₀) := by
    rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact ⟨hinput.transitionInput_eq_self,
      funext fun i => (hwork₂ i).transitionTape_eq_self,
      houtput.transitionTape_eq_self⟩
  have htail := seqTM_hoareTime (binarySuccTM activeIdx)
    (clearWorkTM loopIdx) hsucc' htransition₂ hclearLoop'
  unfold forwardScanVarResetTM forwardScanVarResetTime
  simpa [token, valueIdx, activeIdx, loopIdx, work₁, work₂, work₃,
    forwardScanVarResetWork] using
      seqTM_hoareTime (clearWorkTM valueIdx)
        (seqTM (binarySuccTM activeIdx) (clearWorkTM loopIdx))
        hclearValue' htransition₁ htail

theorem forwardScanVarResetTM_isTransducer_internal (n controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarResetTM n controllerTapes layout).IsTransducer := by
  unfold forwardScanVarResetTM
  exact (clearWorkTM_isTransducer _).seqTM
    ((binarySuccTM_isTransducer _).seqTM (clearWorkTM_isTransducer _))

theorem forwardScanVarTokenStepTM_isTransducer_internal (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanVarTokenStepTM tm controllerTapes layout).IsTransducer := by
  unfold forwardScanVarTokenStepTM
  exact (outputProbeDecodeNatTM_isTransducer tm controllerTapes _ _ _ _ _ _).seqTM
    ((forwardScanVarResetTM_isTransducer_internal n controllerTapes
      layout).seqTM (forwardScanTokenStepTM_isTransducer _ 0))

theorem forwardScanDecodedTokenTM_isTransducer_internal (tm : TM n)
    (controllerTapes : ℕ)
    (layout : ForwardScanTokenLayout controllerTapes) :
    (forwardScanDecodedTokenTM tm controllerTapes layout).IsTransducer := by
  unfold forwardScanDecodedTokenTM
  exact (forwardScanVarTokenStepTM_isTransducer_internal tm controllerTapes
    layout).outputProbeDecodeTokenTM
      (forwardScanTokenStepTM_isTransducer _ 0)
      (forwardScanTokenStepTM_isTransducer _ 0)
      (forwardScanTokenStepTM_isTransducer _ 1)
      (forwardScanTokenStepTM_isTransducer _ 2)
      (forwardScanTokenStepTM_isTransducer _ 2)
      (by
        intro phase iHead wHeads oHead
        cases phase <;> simp only [skipTM, idleDir] <;> split <;> decide)
      layout.tokenLayout

end Machine

end BPCode

end Complexity
