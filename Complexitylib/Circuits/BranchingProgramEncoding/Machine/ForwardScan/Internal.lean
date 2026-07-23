/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.ForwardScan.Defs
import Complexitylib.Models.TuringMachine.Combinators.WorkSymbolBranch
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy
import Complexitylib.Models.TuringMachine.Subroutines.BinaryEq
import Complexitylib.Models.TuringMachine.Subroutines.BinaryPred
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Forward postfix scan controller -- proof internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

private theorem skipTM_isTransducer {n : ℕ} : (skipTM : TM n).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase <;> simp only [skipTM, idleDir] <;> split <;> decide

private theorem forwardScanRole_ne (layout : ForwardScanLayout n)
    (i j : Fin 8) (hij : i ≠ j) : layout.roles i ≠ layout.roles j :=
  layout.roles.injective.ne hij

private theorem parked_of_hasBinaryNat {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t :=
  ⟨by rw [h.2.1], h.2.hasBinaryContent.cells_ne_start⟩

private theorem natBits_eq_one_iff (value : ℕ) :
    value.bits = (1 : ℕ).bits ↔ value = 1 := by
  constructor
  · intro hbits
    have hodd : value.bodd = true := by
      rw [Nat.bodd_eq_bits_head, hbits]
      rfl
    have hdivBits : value.div2.bits = [] := by
      rw [Nat.div2_bits_eq_tail, hbits]
      rfl
    have hdiv : value.div2 = 0 := by
      apply Nat.size_eq_zero.mp
      rw [← Nat.size_eq_bits_len, hdivBits]
      rfl
    rw [← Nat.bit_bodd_div2 value, hodd, hdiv]
    rfl
  · rintro rfl
    rfl

theorem forwardScanCopyBoundaryTM_hoareTime_internal
    (layout : ForwardScanLayout n)
    (tokenCount cursor lastOneCount lastOneCursor : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hcount : (work₀ layout.tokenCountIdx).HasBinaryNat tokenCount)
    (hcursor : (work₀ layout.cursorIdx).HasBinaryNat cursor)
    (hlastCount :
      (work₀ layout.lastOneCountIdx).HasBinaryNat lastOneCount)
    (hlastCursor :
      (work₀ layout.lastOneCursorIdx).HasBinaryNat lastOneCursor)
    (hscratch : (work₀ layout.copyScratchIdx).HasBinaryNat 0)
    (hresult : (work₀ layout.resultIdx).HasBinaryString [true])
    (hresultStart : (work₀ layout.resultIdx).cells 0 = Γ.start)
    (hinput : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanCopyBoundaryTM layout).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = forwardScanBoundaryWork layout work₀ tokenCount cursor ∧
        out = out₀)
      (forwardScanRecordBoundaryTime true tokenCount cursor lastOneCount
        lastOneCursor) := by
  have hcountLast : layout.tokenCountIdx ≠ layout.lastOneCountIdx := by
    unfold ForwardScanLayout.tokenCountIdx ForwardScanLayout.lastOneCountIdx
    exact forwardScanRole_ne layout 2 3 (by decide)
  have hcountScratch : layout.tokenCountIdx ≠ layout.copyScratchIdx := by
    unfold ForwardScanLayout.tokenCountIdx ForwardScanLayout.copyScratchIdx
    exact forwardScanRole_ne layout 2 7 (by decide)
  have hlastScratch : layout.lastOneCountIdx ≠
      layout.copyScratchIdx := by
    unfold ForwardScanLayout.lastOneCountIdx
      ForwardScanLayout.copyScratchIdx
    exact forwardScanRole_ne layout 3 7 (by decide)
  let work₁ := Function.update work₀ layout.lastOneCountIdx
    ((Tape.init (tokenCount.bits.map Γ.ofBool)).move Dir3.right)
  have hcopyCount := binaryCopyIntoTM_hoareTime_frame
    layout.tokenCountIdx layout.lastOneCountIdx layout.copyScratchIdx
    hcountLast hcountScratch hlastScratch tokenCount lastOneCount inp₀ work₀
    out₀ hcount hlastCount hscratch hinput
    (fun i _ _ _ => hwork i) houtput
  have hcopyCount' :
      (binaryCopyIntoTM layout.tokenCountIdx layout.lastOneCountIdx
        layout.copyScratchIdx).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
        (binaryCopyTime tokenCount lastOneCount) := by
    simpa [work₁] using hcopyCount
  have hcursorLast : layout.cursorIdx ≠ layout.lastOneCursorIdx := by
    unfold ForwardScanLayout.cursorIdx ForwardScanLayout.lastOneCursorIdx
    exact forwardScanRole_ne layout 0 4 (by decide)
  have hcursorScratch : layout.cursorIdx ≠ layout.copyScratchIdx := by
    unfold ForwardScanLayout.cursorIdx ForwardScanLayout.copyScratchIdx
    exact forwardScanRole_ne layout 0 7 (by decide)
  have hlastCursorScratch : layout.lastOneCursorIdx ≠
      layout.copyScratchIdx := by
    unfold ForwardScanLayout.lastOneCursorIdx
      ForwardScanLayout.copyScratchIdx
    exact forwardScanRole_ne layout 4 7 (by decide)
  have hlastCountCursor : layout.lastOneCountIdx ≠ layout.cursorIdx := by
    unfold ForwardScanLayout.lastOneCountIdx ForwardScanLayout.cursorIdx
    exact forwardScanRole_ne layout 3 0 (by decide)
  have hlastCountLastCursor : layout.lastOneCountIdx ≠
      layout.lastOneCursorIdx := by
    unfold ForwardScanLayout.lastOneCountIdx
      ForwardScanLayout.lastOneCursorIdx
    exact forwardScanRole_ne layout 3 4 (by decide)
  have hlastCountResult : layout.lastOneCountIdx ≠ layout.resultIdx := by
    unfold ForwardScanLayout.lastOneCountIdx ForwardScanLayout.resultIdx
    exact forwardScanRole_ne layout 3 6 (by decide)
  have hwork₁ : ∀ i, Parked (work₁ i) := by
    intro i
    by_cases hi : i = layout.lastOneCountIdx
    · subst i
      simp only [work₁, Function.update_self]
      exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat tokenCount)
    simpa only [work₁, Function.update_of_ne hi] using hwork i
  have hcursor₁ : (work₁ layout.cursorIdx).HasBinaryNat cursor := by
    simpa only [work₁, Function.update_of_ne hlastCountCursor.symm] using
      hcursor
  have hlastCursor₁ :
      (work₁ layout.lastOneCursorIdx).HasBinaryNat lastOneCursor := by
    simpa only [work₁, Function.update_of_ne hlastCountLastCursor.symm] using
      hlastCursor
  have hscratch₁ : (work₁ layout.copyScratchIdx).HasBinaryNat 0 := by
    simpa only [work₁, Function.update_of_ne hlastScratch.symm] using hscratch
  let work₂ := Function.update work₁ layout.lastOneCursorIdx
    ((Tape.init (cursor.bits.map Γ.ofBool)).move Dir3.right)
  have hcopyCursor := binaryCopyIntoTM_hoareTime_frame layout.cursorIdx
    layout.lastOneCursorIdx layout.copyScratchIdx hcursorLast hcursorScratch
    hlastCursorScratch cursor lastOneCursor inp₀ work₁ out₀ hcursor₁
    hlastCursor₁ hscratch₁ hinput (fun i _ _ _ => hwork₁ i) houtput
  have hcopyCursor' :
      (binaryCopyIntoTM layout.cursorIdx layout.lastOneCursorIdx
        layout.copyScratchIdx).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = work₁ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ work = work₂ ∧ out = out₀)
        (binaryCopyTime cursor lastOneCursor) := by
    simpa [work₂] using hcopyCursor
  have hlastCursorResult : layout.lastOneCursorIdx ≠ layout.resultIdx := by
    unfold ForwardScanLayout.lastOneCursorIdx ForwardScanLayout.resultIdx
    exact forwardScanRole_ne layout 4 6 (by decide)
  have hwork₂ : ∀ i, Parked (work₂ i) := by
    intro i
    by_cases hi : i = layout.lastOneCursorIdx
    · subst i
      simp only [work₂, Function.update_self]
      exact parked_of_hasBinaryNat (Tape.init_move_right_hasBinaryNat cursor)
    simpa only [work₂, Function.update_of_ne hi] using hwork₁ i
  have hresult₂ : work₂ layout.resultIdx =
      (Tape.init ([true].map Γ.ofBool)).move Dir3.right := by
    simpa only [work₂, Function.update_of_ne hlastCursorResult.symm,
      work₁, Function.update_of_ne hlastCountResult.symm] using
      Tape.eq_init_move_right_of_hasBinaryString hresult hresultStart
  let work₃ := Function.update work₂ layout.resultIdx
    ((Tape.init []).move Dir3.right)
  have hclear := clearWorkTM_hoareTime_frame layout.resultIdx [true] inp₀
    work₂ out₀ hresult₂ hinput (fun i _ => hwork₂ i) houtput
  have hclear' : (clearWorkTM layout.resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₂ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = work₃ ∧ out = out₀)
      (clearWorkTimeBound 1) := by
    simpa [work₃] using hclear
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
  have htail := seqTM_hoareTime
    (binaryCopyIntoTM layout.cursorIdx layout.lastOneCursorIdx
      layout.copyScratchIdx)
    (clearWorkTM layout.resultIdx) hcopyCursor' htransition₂ hclear'
  unfold forwardScanCopyBoundaryTM forwardScanRecordBoundaryTime
  simpa [work₁, work₂, work₃, forwardScanBoundaryWork] using
    seqTM_hoareTime
      (binaryCopyIntoTM layout.tokenCountIdx layout.lastOneCountIdx
        layout.copyScratchIdx)
      (seqTM
        (binaryCopyIntoTM layout.cursorIdx layout.lastOneCursorIdx
          layout.copyScratchIdx)
        (clearWorkTM layout.resultIdx))
      hcopyCount' htransition₁ htail

theorem forwardScanHeightTM_hoareTime_internal
    (layout : ForwardScanLayout n) (arity height : ℕ)
    (harity : arity ≤ 2) (hpositive : arity = 2 → 1 ≤ height)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hheight : (work₀ layout.heightIdx).HasBinaryNat height)
    (hinput : Parked inp₀)
    (hother : ∀ i, i ≠ layout.heightIdx → Parked (work₀ i))
    (houtput : Parked out₀) :
    (forwardScanHeightTM layout arity).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ layout.heightIdx
          ((Tape.init ((height + 1 - arity).bits.map Γ.ofBool)).move
            Dir3.right) ∧
        out = out₀)
      (forwardScanHeightTime arity height) := by
  cases arity with
  | zero =>
      have hrun := binarySuccTM_hoareTime_frame layout.heightIdx height inp₀
        work₀ out₀ hheight hinput.read_ne_start
        (fun i hi => (hother i hi).read_ne_start) houtput.read_ne_start
      apply hrun.consequence (fun _ _ _ h => h) (fun inp work out h => ?_)
        (by simp [forwardScanHeightTime])
      rcases h with ⟨hinp, hwork, htarget, hout⟩
      refine ⟨hinp, ?_, hout⟩
      funext i
      by_cases hi : i = layout.heightIdx
      · subst i
        rw [Function.update_self]
        exact htarget.eq_init_move_right
      rw [Function.update_of_ne hi]
      exact hwork i hi
  | succ arity =>
      cases arity with
      | zero =>
          have hrun := skipTM_hoareTime_frame inp₀ work₀ out₀ hinput
            (fun i => by
              by_cases hi : i = layout.heightIdx
              · subst i
                exact ⟨by rw [hheight.2.1],
                  hheight.2.hasBinaryContent.cells_ne_start⟩
              · exact hother i hi)
            houtput
          apply hrun.consequence (fun _ _ _ h => h)
            (fun inp work out h => ?_) (by simp [forwardScanHeightTime])
          rcases h with ⟨hinp, hwork, hout⟩
          refine ⟨hinp, ?_, hout⟩
          rw [hwork]
          funext i
          by_cases hi : i = layout.heightIdx
          · subst i
            rw [Function.update_self]
            simpa using hheight.eq_init_move_right
          rw [Function.update_of_ne hi]
      | succ arity =>
          have harityZero : arity = 0 := by omega
          subst arity
          have hheightPos : 1 ≤ height := hpositive rfl
          have hheightEq : height - 1 + 1 = height := by omega
          have hrun := binaryPredTM_hoareTime_frame layout.heightIdx
            (height - 1) inp₀ work₀ out₀ (by
              simpa [hheightEq] using hheight) hinput.read_ne_start
            (fun i hi => (hother i hi).read_ne_start)
            houtput.read_ne_start
          apply hrun.consequence (fun _ _ _ h => h)
            (fun inp work out h => ?_)
            (by simp [forwardScanHeightTime])
          rcases h with ⟨hinp, hwork, htarget, hout⟩
          refine ⟨hinp, ?_, hout⟩
          funext i
          by_cases hi : i = layout.heightIdx
          · subst i
            rw [Function.update_self]
            convert htarget.eq_init_move_right using 1
          rw [Function.update_of_ne hi]
          exact hwork i hi

theorem forwardScanHeightTM_isTransducer_internal
    (layout : ForwardScanLayout n) (arity : ℕ) :
    (forwardScanHeightTM layout arity).IsTransducer := by
  cases arity with
  | zero => exact binarySuccTM_isTransducer layout.heightIdx
  | succ arity =>
      cases arity with
      | zero => exact skipTM_isTransducer
      | succ _ => exact binaryPredTM_isTransducer layout.heightIdx

theorem forwardScanCopyBoundaryTM_isTransducer_internal
    (layout : ForwardScanLayout n) :
    (forwardScanCopyBoundaryTM layout).IsTransducer := by
  unfold forwardScanCopyBoundaryTM
  exact
    (binaryCopyIntoTM_isTransducer layout.tokenCountIdx
      layout.lastOneCountIdx layout.copyScratchIdx).seqTM
      ((binaryCopyIntoTM_isTransducer layout.cursorIdx
        layout.lastOneCursorIdx layout.copyScratchIdx).seqTM
        (clearWorkTM_isTransducer layout.resultIdx))

theorem forwardScanRecordBoundaryTM_isTransducer_internal
    (layout : ForwardScanLayout n) :
    (forwardScanRecordBoundaryTM layout).IsTransducer := by
  unfold forwardScanRecordBoundaryTM
  exact (forwardScanCopyBoundaryTM_isTransducer_internal layout)
    |>.branchWorkSymbolTM (clearWorkTM_isTransducer layout.resultIdx)

theorem forwardScanAfterHeightTM_isTransducer_internal
    (layout : ForwardScanLayout n) :
    (forwardScanAfterHeightTM layout).IsTransducer := by
  unfold forwardScanAfterHeightTM
  exact (binarySuccTM_isTransducer layout.tokenCountIdx).seqTM
    ((binaryEqRewindTM_isTransducer layout.heightIdx layout.oneIdx
      layout.resultIdx).seqTM
      (forwardScanRecordBoundaryTM_isTransducer_internal layout))

theorem forwardScanTokenStepTM_isTransducer_internal
    (layout : ForwardScanLayout n) (arity : ℕ) :
    (forwardScanTokenStepTM layout arity).IsTransducer := by
  unfold forwardScanTokenStepTM
  exact (forwardScanHeightTM_isTransducer_internal layout arity).seqTM
    (forwardScanAfterHeightTM_isTransducer_internal layout)

end Machine

end BPCode

end Complexity
