/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.Encoding.Machine.Defs

/-!
# Streaming serialized-circuit evaluator core

This file defines the finite controller that evaluates an already-staged
tagged circuit code. The code tape is parsed once from left to right. The wire
tape begins with the primary input and receives one appended Boolean value per
gate. Unary references walk that memo tape directly, while the third work tape
stores and consumes the declared unary gate count.

The local `TapeAction` layer packages the one-sided-tape safety obligation with
each head action. Consequently `evalFamilyCoreTM` satisfies
`TM.δ_right_of_start` structurally rather than through a large case proof.
-/

namespace Complexity

namespace CircuitCode

namespace Machine

/-- One tape-head action together with its left-end safety proof. -/
structure TapeAction (head : Γ) where
  /-- Writable symbol emitted at the current head. -/
  write : Γw
  /-- Direction taken after the write. -/
  dir : Dir3
  /-- The action moves right whenever it reads the left-end marker. -/
  rightOfStart : head = Γ.start → dir = Dir3.right

namespace TapeAction

/-- Preserve the scanned cell and keep an off-marker head stationary. -/
def preserve (head : Γ) : TapeAction head where
  write := TM.readBackWrite head
  dir := TM.idleDir head
  rightOfStart := TM.idleDir_right_of_start

/-- Preserve the scanned cell and move right. -/
def moveRight (head : Γ) : TapeAction head where
  write := TM.readBackWrite head
  dir := .right
  rightOfStart := fun _ => rfl

/-- Preserve the scanned cell and move left, bouncing right at `▷`. -/
def moveLeft (head : Γ) : TapeAction head where
  write := TM.readBackWrite head
  dir := TM.moveLeftDir head
  rightOfStart := by
    intro h
    simp [TM.moveLeftDir, h]

/-- Write a symbol and move right. -/
def writeRight (head : Γ) (symbol : Γw) : TapeAction head where
  write := symbol
  dir := .right
  rightOfStart := fun _ => rfl

/-- Write a symbol and keep an off-marker head stationary. -/
def writeStay (head : Γ) (symbol : Γw) : TapeAction head where
  write := symbol
  dir := TM.idleDir head
  rightOfStart := TM.idleDir_right_of_start

end TapeAction

/-- Finite phases of the fused tagged-code parser and memoized evaluator. -/
inductive CorePhase where
  | rewindCode
  | rewindWires
  | familyTag
  | emptyAnswer
  | emptyEnd (answer : Bool)
  | count
  | rewindCounter
  | gateCheck (sawGate : Bool)
  | gateOp
  | gateNeg0 (op : Bool)
  | gateNeg1 (op negated0 : Bool)
  | rewindRef0 (op negated0 negated1 : Bool)
  | ref0 (op negated0 negated1 : Bool)
  | rewindRef1 (op negated1 value0 : Bool)
  | ref1 (op negated1 value0 : Bool)
  | seekAppend (value : Bool)
  | done
  deriving DecidableEq, Fintype, Repr

/-- Named actions for the three evaluator work tapes and the output tape. -/
structure CoreAction (wHeads : Fin workTapeCount → Γ) (oHead : Γ) where
  /-- Controller phase entered after this action. -/
  next : CorePhase
  /-- Action for the serialized-code tape. -/
  code : TapeAction (wHeads codeIdx)
  /-- Action for the input-and-memo wire tape. -/
  wires : TapeAction (wHeads wiresIdx)
  /-- Action for the unary gate-counter tape. -/
  counter : TapeAction (wHeads counterIdx)
  /-- Action for the Boolean verdict output tape. -/
  output : TapeAction oHead

namespace CoreAction

/-- A frame-preserving action that changes only the controller phase. -/
def preserve (next : CorePhase) (wHeads : Fin workTapeCount → Γ)
    (oHead : Γ) : CoreAction wHeads oHead where
  next := next
  code := TapeAction.preserve _
  wires := TapeAction.preserve _
  counter := TapeAction.preserve _
  output := TapeAction.preserve _

/-- Project the writable symbol for a named work tape. -/
def workWrite {wHeads : Fin workTapeCount → Γ} {oHead : Γ}
    (action : CoreAction wHeads oHead) (i : Fin workTapeCount) : Γw :=
  if i = codeIdx then action.code.write
  else if i = wiresIdx then action.wires.write
  else action.counter.write

/-- Project the direction for a named work tape. -/
def workDir {wHeads : Fin workTapeCount → Γ} {oHead : Γ}
    (action : CoreAction wHeads oHead) (i : Fin workTapeCount) : Dir3 :=
  if i = codeIdx then action.code.dir
  else if i = wiresIdx then action.wires.dir
  else action.counter.dir

/-- Every projected work action moves right when its head reads `▷`. -/
theorem workDir_rightOfStart {wHeads : Fin workTapeCount → Γ} {oHead : Γ}
    (action : CoreAction wHeads oHead) :
    ∀ i, wHeads i = Γ.start → action.workDir i = Dir3.right := by
  intro i hi
  by_cases hcode : i = codeIdx
  · subst i
    simpa [workDir] using action.code.rightOfStart hi
  by_cases hwires : i = wiresIdx
  · subst i
    simpa [workDir, hcode] using action.wires.rightOfStart hi
  have hne0 : i.val ≠ 0 := by
    intro hval
    apply hcode
    apply Fin.ext
    exact hval
  have hne1 : i.val ≠ 1 := by
    intro hval
    apply hwires
    apply Fin.ext
    exact hval
  have hcounter : i = counterIdx := by
    apply Fin.ext
    change i.val = 2
    have hi : i.val < 3 := by
      exact i.isLt
    omega
  subst i
  simpa [workDir, codeIdx, wiresIdx, counterIdx] using
    action.counter.rightOfStart hi

end CoreAction

/-- Boolean AND/OR selected by the serialized operation bit. -/
def evalOpBit (op value0 value1 : Bool) : Bool :=
  if op then value0 && value1 else value0 || value1

private def rejectAction (wHeads : Fin workTapeCount → Γ) (oHead : Γ) :
    CoreAction wHeads oHead :=
  { CoreAction.preserve .done wHeads oHead with
    output := TapeAction.writeStay oHead .zero }

private def finishAction (answer : Bool) (wHeads : Fin workTapeCount → Γ)
    (oHead : Γ) : CoreAction wHeads oHead :=
  { CoreAction.preserve .done wHeads oHead with
    output := TapeAction.writeStay oHead (Γw.ofBool answer) }

private def moveCodeRightAction (next : CorePhase)
    (wHeads : Fin workTapeCount → Γ) (oHead : Γ) :
    CoreAction wHeads oHead :=
  { CoreAction.preserve next wHeads oHead with
    code := TapeAction.moveRight _ }

private def moveWiresRightAction (next : CorePhase)
    (wHeads : Fin workTapeCount → Γ) (oHead : Γ) :
    CoreAction wHeads oHead :=
  { CoreAction.preserve next wHeads oHead with
    wires := TapeAction.moveRight _ }

private def readCodeBitAction (next : Bool → CorePhase)
    (wHeads : Fin workTapeCount → Γ) (oHead : Γ) :
    CoreAction wHeads oHead :=
  match wHeads codeIdx with
  | .zero => moveCodeRightAction (next false) wHeads oHead
  | .one => moveCodeRightAction (next true) wHeads oHead
  | _ => rejectAction wHeads oHead

/-- One finite-control action of the streaming evaluator. -/
def coreAction (phase : CorePhase) (wHeads : Fin workTapeCount → Γ)
    (oHead : Γ) : CoreAction wHeads oHead :=
  let codeHead := wHeads codeIdx
  let wiresHead := wHeads wiresIdx
  let counterHead := wHeads counterIdx
  match phase with
  | .rewindCode =>
      if codeHead = Γ.start then
        { CoreAction.preserve .rewindWires wHeads oHead with
          code := TapeAction.moveRight codeHead }
      else
        { CoreAction.preserve .rewindCode wHeads oHead with
          code := TapeAction.moveLeft codeHead }
  | .rewindWires =>
      if wiresHead = Γ.start then
        moveWiresRightAction .familyTag wHeads oHead
      else
        { CoreAction.preserve .rewindWires wHeads oHead with
          wires := TapeAction.moveLeft wiresHead }
  | .familyTag =>
      match wiresHead, codeHead with
      | .blank, .zero => moveCodeRightAction .emptyAnswer wHeads oHead
      | .zero, .one => moveCodeRightAction .count wHeads oHead
      | .one, .one => moveCodeRightAction .count wHeads oHead
      | _, _ => rejectAction wHeads oHead
  | .emptyAnswer => readCodeBitAction .emptyEnd wHeads oHead
  | .emptyEnd answer =>
      if codeHead = Γ.blank then finishAction answer wHeads oHead
      else rejectAction wHeads oHead
  | .count =>
      match codeHead with
      | .one =>
          { CoreAction.preserve .count wHeads oHead with
            code := TapeAction.moveRight codeHead
            counter := TapeAction.writeRight counterHead .one }
      | .zero => moveCodeRightAction .rewindCounter wHeads oHead
      | _ => rejectAction wHeads oHead
  | .rewindCounter =>
      if counterHead = Γ.start then
        { CoreAction.preserve (.gateCheck false) wHeads oHead with
          counter := TapeAction.moveRight counterHead }
      else
        { CoreAction.preserve .rewindCounter wHeads oHead with
          counter := TapeAction.moveLeft counterHead }
  | .gateCheck sawGate =>
      match counterHead with
      | .one =>
          { CoreAction.preserve .gateOp wHeads oHead with
            counter := TapeAction.writeRight counterHead .blank }
      | .blank =>
          if sawGate && codeHead = Γ.blank then
            CoreAction.preserve .done wHeads oHead
          else
            rejectAction wHeads oHead
      | _ => rejectAction wHeads oHead
  | .gateOp => readCodeBitAction .gateNeg0 wHeads oHead
  | .gateNeg0 op => readCodeBitAction (.gateNeg1 op) wHeads oHead
  | .gateNeg1 op negated0 =>
      readCodeBitAction (.rewindRef0 op negated0) wHeads oHead
  | .rewindRef0 op negated0 negated1 =>
      if wiresHead = Γ.start then
        { CoreAction.preserve (.ref0 op negated0 negated1) wHeads oHead with
          wires := TapeAction.moveRight wiresHead }
      else
        { CoreAction.preserve (.rewindRef0 op negated0 negated1) wHeads oHead with
          wires := TapeAction.moveLeft wiresHead }
  | .ref0 op negated0 negated1 =>
      match codeHead, wiresHead with
      | .one, .zero =>
          { CoreAction.preserve (.ref0 op negated0 negated1) wHeads oHead with
            code := TapeAction.moveRight codeHead
            wires := TapeAction.moveRight wiresHead }
      | .one, .one =>
          { CoreAction.preserve (.ref0 op negated0 negated1) wHeads oHead with
            code := TapeAction.moveRight codeHead
            wires := TapeAction.moveRight wiresHead }
      | .zero, .zero =>
          moveCodeRightAction (.rewindRef1 op negated1 (negated0.xor false))
            wHeads oHead
      | .zero, .one =>
          moveCodeRightAction (.rewindRef1 op negated1 (negated0.xor true))
            wHeads oHead
      | _, _ => rejectAction wHeads oHead
  | .rewindRef1 op negated1 value0 =>
      if wiresHead = Γ.start then
        { CoreAction.preserve (.ref1 op negated1 value0) wHeads oHead with
          wires := TapeAction.moveRight wiresHead }
      else
        { CoreAction.preserve (.rewindRef1 op negated1 value0) wHeads oHead with
          wires := TapeAction.moveLeft wiresHead }
  | .ref1 op negated1 value0 =>
      match codeHead, wiresHead with
      | .one, .zero =>
          { CoreAction.preserve (.ref1 op negated1 value0) wHeads oHead with
            code := TapeAction.moveRight codeHead
            wires := TapeAction.moveRight wiresHead }
      | .one, .one =>
          { CoreAction.preserve (.ref1 op negated1 value0) wHeads oHead with
            code := TapeAction.moveRight codeHead
            wires := TapeAction.moveRight wiresHead }
      | .zero, .zero =>
          moveCodeRightAction
            (.seekAppend (evalOpBit op value0 (negated1.xor false))) wHeads oHead
      | .zero, .one =>
          moveCodeRightAction
            (.seekAppend (evalOpBit op value0 (negated1.xor true))) wHeads oHead
      | _, _ => rejectAction wHeads oHead
  | .seekAppend value =>
      match wiresHead with
      | .zero => moveWiresRightAction (.seekAppend value) wHeads oHead
      | .one => moveWiresRightAction (.seekAppend value) wHeads oHead
      | .blank =>
          { CoreAction.preserve (.gateCheck true) wHeads oHead with
            wires := TapeAction.writeRight wiresHead (Γw.ofBool value)
            output := TapeAction.writeStay oHead (Γw.ofBool value) }
      | .start => rejectAction wHeads oHead
  | .done => CoreAction.preserve .done wHeads oHead

/-- Streaming evaluator for a valid outer pair after `validPairStageTM`.

The core itself remains total: malformed tagged codes and invalid references
write zero and halt. -/
def evalFamilyCoreTM : TM workTapeCount where
  Q := CorePhase
  qstart := .rewindCode
  qhalt := .done
  δ := fun phase iHead wHeads oHead =>
    let action := coreAction phase wHeads oHead
    (action.next, action.workWrite, action.output.write,
      TM.idleDir iHead, action.workDir, action.output.dir)
  δ_right_of_start := by
    intro phase iHead wHeads oHead
    let action := coreAction phase wHeads oHead
    exact ⟨TM.idleDir_right_of_start, action.workDir_rightOfStart,
      action.output.rightOfStart⟩

/-- Total serialized-family evaluator: validate and stage the outer pair, then
run the streaming core only on the valid branch. -/
def evalFamilyTM : TM workTapeCount :=
  evalFamilyTMWith evalFamilyCoreTM

end Machine

end CircuitCode

end Complexity
