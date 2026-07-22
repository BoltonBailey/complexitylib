/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BranchingProgramEncoding.Machine.SlotPosition.Defs
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Subroutines.BinaryFor

/-!
# Barrington slot positioning -- internals
-/

namespace Complexity

namespace BPCode

namespace Machine

open TM

private theorem moveSlotRightWork_apply
    (sourceIdx : Fin n) (work : Fin n → Tape)
    (hwork : ∀ i, (work i).read ≠ Γ.start) (i : Fin n) :
    (fun j =>
      (work j).writeAndMove (TM.readBackWrite (work j).read)
        (if j = sourceIdx then Dir3.right else TM.idleDir (work j).read)) i =
      moveSlotRightWork sourceIdx work i := by
  by_cases his : i = sourceIdx
  · subst i
    simp only [moveSlotRightWork, Function.update_self, ↓reduceIte]
    exact TM.writeAndMove_readBack (work sourceIdx) (hwork sourceIdx)
      Dir3.right
  · simp only [moveSlotRightWork, Function.update_of_ne his, if_neg his]
    simpa [TM.idleDir, hwork i, Tape.move] using
      TM.writeAndMove_readBack (work i) (hwork i) Dir3.stay

private theorem moveSlotRightTM_step
    (sourceIdx : Fin n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (moveSlotRightTM sourceIdx).step
      { state := (moveSlotRightTM sourceIdx).qstart
        input := inp₀
        work := work₀
        output := out₀ } =
      some
        { state := (moveSlotRightTM sourceIdx).qhalt
          input := inp₀
          work := moveSlotRightWork sourceIdx work₀
          output := out₀ } := by
  rw [TM.step, if_neg (by simp [moveSlotRightTM])]
  simp only [moveSlotRightTM]
  refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  · dsimp only
    exact TM.transitionInput_eq_self hinput
  · dsimp only
    funext i
    exact moveSlotRightWork_apply sourceIdx work₀ hwork i
  · dsimp only
    exact TM.transitionTape_eq_self houtput

theorem moveSlotRightTM_hoareTime_internal
    (sourceIdx : Fin n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (moveSlotRightTM sourceIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = moveSlotRightWork sourceIdx work₀ ∧ out = out₀)
      1 := by
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  rw [hinp, hworkEq, hout]
  have hstep := moveSlotRightTM_step sourceIdx inp₀ work₀ out₀ hinput hwork
    houtput
  exact ⟨_, 1, le_rfl, .step hstep .zero, rfl, rfl, rfl, rfl⟩

private theorem advanceSlotDigitTM_step
    (sourceIdx : Fin n) (phase next : AdvanceSlotDigitPhase)
    (hphase : phase = .first ∧ next = .second ∨
      phase = .second ∧ next = .done)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (advanceSlotDigitTM sourceIdx).step
      { state := phase, input := inp₀, work := work₀, output := out₀ } =
      some
        { state := next
          input := inp₀
          work := moveSlotRightWork sourceIdx work₀
          output := out₀ } := by
  rcases hphase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [TM.step, if_neg (by simp [advanceSlotDigitTM])] <;>
    simp only [advanceSlotDigitTM] <;>
    refine congrArg some (Cfg.ext rfl ?_ ?_ ?_)
  all_goals dsimp only
  · exact TM.transitionInput_eq_self hinput
  · funext i
    exact moveSlotRightWork_apply sourceIdx work₀ hwork i
  · exact TM.transitionTape_eq_self houtput
  · exact TM.transitionInput_eq_self hinput
  · funext i
    exact moveSlotRightWork_apply sourceIdx work₀ hwork i
  · exact TM.transitionTape_eq_self houtput

theorem advanceSlotDigitTM_hoareTime_internal
    (sourceIdx : Fin n) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsourceNext : ((work₀ sourceIdx).move Dir3.right).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (advanceSlotDigitTM sourceIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = moveSlotRightWork sourceIdx (moveSlotRightWork sourceIdx work₀) ∧
        out = out₀)
      2 := by
  intro inp work out hpre
  obtain ⟨hinp, hworkEq, hout⟩ := hpre
  rw [hinp, hworkEq, hout]
  let work₁ := moveSlotRightWork sourceIdx work₀
  have hwork₁source : work₁ sourceIdx =
      (work₀ sourceIdx).move Dir3.right := by
    simp [work₁, moveSlotRightWork]
  have hwork₁ : ∀ i, (work₁ i).read ≠ Γ.start := by
    intro i
    by_cases his : i = sourceIdx
    · subst i
      rw [hwork₁source]
      exact hsourceNext
    · simp [work₁, moveSlotRightWork, his]
      exact hwork i
  have hfirst := advanceSlotDigitTM_step sourceIdx .first .second
    (Or.inl ⟨rfl, rfl⟩) inp₀ work₀ out₀ hinput hwork houtput
  have hsecond := advanceSlotDigitTM_step sourceIdx .second .done
    (Or.inr ⟨rfl, rfl⟩) inp₀ work₁ out₀ hinput hwork₁ houtput
  let final : Cfg n (advanceSlotDigitTM sourceIdx).Q :=
    { state := .done
      input := inp₀
      work := moveSlotRightWork sourceIdx (moveSlotRightWork sourceIdx work₀)
      output := out₀ }
  refine ⟨final, 2, le_rfl, .step hfirst (.step ?_ .zero), ?_, ?_⟩
  · simpa [work₁] using hsecond
  · rfl
  · exact ⟨rfl, rfl, rfl⟩

theorem moveSlotRightTM_hoareTimeSpace_internal
    (sourceIdx : Fin n) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (moveSlotRightTM sourceIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } : Cfg n (moveSlotRightTM sourceIdx).Q)
        |>.WithinAuxSpace inputLength initialSpace) :
    (moveSlotRightTM sourceIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧ work = moveSlotRightWork sourceIdx work₀ ∧ out = out₀)
      1 inputLength (initialSpace + 1) := by
  apply (moveSlotRightTM_hoareTime_internal sourceIdx inp₀ work₀ out₀ hinput
    hwork houtput).toHoareTimeSpace
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  exact hinitial

theorem advanceSlotDigitTM_hoareTimeSpace_internal
    (sourceIdx : Fin n) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinput : inp₀.read ≠ Γ.start)
    (hsourceNext : ((work₀ sourceIdx).move Dir3.right).read ≠ Γ.start)
    (hwork : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (advanceSlotDigitTM sourceIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } : Cfg n (advanceSlotDigitTM sourceIdx).Q)
        |>.WithinAuxSpace inputLength initialSpace) :
    (advanceSlotDigitTM sourceIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = moveSlotRightWork sourceIdx (moveSlotRightWork sourceIdx work₀) ∧
        out = out₀)
      2 inputLength (initialSpace + 2) := by
  apply (advanceSlotDigitTM_hoareTime_internal sourceIdx inp₀ work₀ out₀ hinput
    hsourceNext hwork houtput).toHoareTimeSpace
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  exact hinitial

theorem moveSlotRightTM_isTransducer_internal (sourceIdx : Fin n) :
    (moveSlotRightTM sourceIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase <;> cases oHead <;>
    simp [moveSlotRightTM, TM.allIdle, TM.idleDir]

theorem advanceSlotDigitTM_isTransducer_internal (sourceIdx : Fin n) :
    (advanceSlotDigitTM sourceIdx).IsTransducer := by
  intro phase iHead wHeads oHead
  cases phase <;> cases oHead <;>
    simp [advanceSlotDigitTM, TM.allIdle, TM.idleDir]

theorem positionSlotTM_isTransducer_internal
    (sourceIdx counterIdx limitIdx : Fin n) :
    (positionSlotTM sourceIdx counterIdx limitIdx).IsTransducer := by
  exact ((advanceSlotDigitTM_isTransducer_internal sourceIdx).binaryForTM
    counterIdx limitIdx).seqTM
      (moveSlotRightTM_isTransducer_internal sourceIdx)

end Machine

end BPCode

end Complexity
