/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.ForInput.Defs
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Read-only-input loop combinator — proof internals

This module supplies the exact body-simulation embedding and the structural
one-way-output proof for `TM.forInputTM`.
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Embed a body configuration into the body phase of `forInputTM`. -/
def forInputBodyWrap (body : TM n) (c : Cfg n body.Q) :
    Cfg n (forInputTM body).Q :=
  { state := .inr c.state
    input := c.input
    work := c.work
    output := c.output }

/-- Every nonhalting body step is simulated exactly by one `forInputTM` step. -/
theorem forInputTM_body_step_internal (body : TM n)
    {c c' : Cfg n body.Q} (hstep : body.step c = some c') :
    (forInputTM body).step (forInputBodyWrap body c) =
      some (forInputBodyWrap body c') := by
  have hne : c.state ≠ body.qhalt := state_ne_qhalt_of_step hstep
  rw [TM.step, if_neg (by simp [forInputBodyWrap, forInputTM])]
  simp only [forInputBodyWrap, forInputTM, hne, ↓reduceIte]
  rw [TM.step, if_neg hne] at hstep
  revert hstep
  generalize body.δ c.state c.input.read (fun i => (c.work i).read) c.output.read = action
  obtain ⟨q', workWrites, outputWrite, inputDir, workDirs, outputDir⟩ := action
  intro hstep
  cases Option.some.inj hstep
  rfl

/-- Exact body runs lift through the body phase of `forInputTM`. -/
theorem forInputTM_body_reachesIn_internal (body : TM n)
    {t : ℕ} {c c' : Cfg n body.Q} (hreach : body.reachesIn t c c') :
    (forInputTM body).reachesIn t
      (forInputBodyWrap body c) (forInputBodyWrap body c') :=
  reachesIn_map (forInputBodyWrap body)
    (fun _ _ => forInputTM_body_step_internal body) hreach

/-- On a Boolean input symbol, the driver advances the read-only input and
enters the body while preserving every off-start work and output tape. -/
theorem forInputTM_step_scan_bit_internal (body : TM n)
    (c : Cfg n (forInputTM body).Q)
    (hstate : c.state = .inl .scan)
    (hstart : c.input.read ≠ Γ.start) (hblank : c.input.read ≠ Γ.blank)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (forInputTM body).step c = some
      { state := .inr body.qstart
        input := c.input.move Dir3.right
        work := c.work
        output := c.output } := by
  rw [TM.step, if_neg (by rw [hstate]; simp [forInputTM])]
  simp only [forInputTM, hstate, hstart, hblank, allReadBack, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    rw [writeAndMove_readBack _ (hwork i), idleDir, if_neg (hwork i)]
    rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, if_neg houtput]
    rfl

/-- At the first input blank, the driver halts while preserving all off-start
tapes exactly. -/
theorem forInputTM_step_scan_blank_internal (body : TM n)
    (c : Cfg n (forInputTM body).Q)
    (hstate : c.state = .inl .scan) (hblank : c.input.read = Γ.blank)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (forInputTM body).step c = some
      { state := .inl .done
        input := c.input
        work := c.work
        output := c.output } := by
  have hstart : c.input.read ≠ Γ.start := by rw [hblank]; decide
  rw [TM.step, if_neg (by rw [hstate]; simp [forInputTM])]
  simp only [forInputTM, hstate, hblank, allReadBack, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · simp [idleDir, Tape.move]
  · funext i
    rw [writeAndMove_readBack _ (hwork i), idleDir, if_neg (hwork i)]
    rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, if_neg houtput]
    rfl

/-- A halted body takes one preserving seam step back to the input scanner. -/
theorem forInputTM_step_body_halt_internal (body : TM n)
    (c : Cfg n body.Q) (hhalt : body.halted c)
    (hinput : c.input.read ≠ Γ.start)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (houtput : c.output.read ≠ Γ.start) :
    (forInputTM body).step (forInputBodyWrap body c) = some
      { state := .inl .scan
        input := c.input
        work := c.work
        output := c.output } := by
  rw [TM.step, if_neg (by simp [forInputBodyWrap, forInputTM])]
  simp only [forInputBodyWrap, forInputTM, hhalt, allReadBack, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_eq_self hinput
  · funext i
    rw [writeAndMove_readBack _ (hwork i), idleDir, if_neg (hwork i)]
    rfl
  · rw [writeAndMove_readBack _ houtput, idleDir, if_neg houtput]
    rfl

/-- A read-only-input loop preserves the body's one-way-output discipline. -/
theorem IsTransducer.forInputTM_internal {body : TM n}
    (hbody : body.IsTransducer) : (forInputTM body).IsTransducer := by
  intro state iHead wHeads oHead
  cases state with
  | inl phase =>
      cases phase <;> cases iHead <;> cases oHead <;>
        simp [forInputTM, allIdle, allReadBack, idleDir]
  | inr q =>
      by_cases hq : q = body.qhalt
      · cases oHead <;> simp [forInputTM, hq, allReadBack, idleDir]
      · simpa [forInputTM, hq] using hbody q iHead wHeads oHead

end TM

end Complexity
