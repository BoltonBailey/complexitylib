/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
import Complexitylib.SAT.Tseitin.Machine.Defs

/-!
# Execution of the Tseitin syntax-validation machine

This file proves the first execution layer for the concrete reduction machine.
Starting from the standard initial configuration, `validationTM` performs one
left-end-marker bounce, scans one input bit per step, and uses one final step
to write its verdict. Thus it halts in exactly `|z| + 2` steps.

The proof follows the generic scanner invariant while additionally tracking
all work tapes. They are bumped to cell one on the first step and then remain
literally unchanged throughout the scan.

## Main results

- `validationTM_reachesIn_internal` — exact execution from `initCfg`
- `validationTM_hoareTime_internal` — compositional `HoareTime` interface
-/

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Machine

private def validationStartedCfg (z : List Bool) :
    Cfg n (validationTM (n := n)).Q :=
  { state := .scan .initial
    input := ⟨1, (Tape.init (z.map Γ.ofBool)).cells⟩
    work := fun _ => ⟨1, (Tape.init []).cells⟩
    output := ⟨1, (Tape.init []).cells⟩ }

/-- The initial left-end-marker bounce enters the scan state and parks every
tape head at cell one without changing any cells. -/
private theorem validationTM_step_init (z : List Bool) :
    (validationTM (n := n)).step ((validationTM (n := n)).initCfg z) =
      some (validationStartedCfg (n := n) z) := by
  rfl

/-- One nonblank, non-start input bit advances the input head, updates the
finite scan state, and preserves every work and output tape. -/
private theorem validationTM_step_scan
    (c : Cfg n (validationTM (n := n)).Q) (state : ValidationState)
    (hst : c.state = .scan state)
    (hiStart : c.input.read ≠ Γ.start) (hiBlank : c.input.read ≠ Γ.blank)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output) :
    ∃ c', (validationTM (n := n)).step c = some c' ∧
      c'.state = .scan (state.step (decide (c.input.read = Γ.one))) ∧
      c'.input.head = c.input.head + 1 ∧ c'.input.cells = c.input.cells ∧
      c'.work = c.work ∧ c'.output = c.output := by
  simp only [TM.step, hst, validationTM, reduceCtorEq, ↓reduceIte, hiStart, hiBlank]
  refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · simp [Tape.move]
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · exact hout.writeAndMove_readBack_idle

/-- The blank-input transition writes the finite-state verdict and halts,
preserving the input and every work tape. -/
private theorem validationTM_step_halt
    (c : Cfg n (validationTM (n := n)).Q) (state : ValidationState)
    (hst : c.state = .scan state)
    (hiStart : c.input.read ≠ Γ.start) (hiBlank : c.input.read = Γ.blank)
    (hwork : ∀ i, TM.Parked (c.work i)) (hout : TM.Parked c.output)
    (hoHead : c.output.head = 1) :
    ∃ c', (validationTM (n := n)).step c = some c' ∧
      (validationTM (n := n)).halted c' ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output.head = 1 ∧
      c'.output.cells 1 =
        (if state.accepts then Γw.one else Γw.zero).toΓ := by
  simp only [TM.step, hst, validationTM, reduceCtorEq, ↓reduceIte, hiStart,
    if_pos hiBlank]
  have hoMove : TM.idleDir c.output.read = Dir3.stay := by
    simp [TM.idleDir, hout.read_ne_start]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [hiBlank, TM.idleDir, Tape.move]
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · simp [Tape.writeAndMove, hoMove, Tape.move, Tape.write_head, hoHead]
  · have hOne : (1 : ℕ) ≠ 0 := by omega
    simp [Tape.writeAndMove, hoMove, Tape.move, Tape.write, hoHead, hOne]

/-- Scanner invariant. With `m` bits remaining and the input head at `k+1`,
the validator halts after exactly `m+1` more steps. -/
private theorem validationTM_scan
    (z : List Bool) (m k : ℕ) (hLength : z.length = k + m)
    (state : ValidationState) (c : Cfg n (validationTM (n := n)).Q)
    (hst : c.state = .scan state)
    (hiCells : c.input.cells = (Tape.init (z.map Γ.ofBool)).cells)
    (hiHead : c.input.head = k + 1)
    (hwork : ∀ i, TM.Parked (c.work i))
    (hout : TM.Parked c.output) (hoHead : c.output.head = 1) :
    ∃ c', (validationTM (n := n)).reachesIn (m + 1) c c' ∧
      (validationTM (n := n)).halted c' ∧
      c'.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      c'.input.head = z.length + 1 ∧ c'.work = c.work ∧
      c'.output.head = 1 ∧
      c'.output.cells 1 =
        (if ((z.drop k).foldl ValidationState.step state).accepts
          then Γw.one else Γw.zero).toΓ := by
  induction m generalizing k state c with
  | zero =>
      have hk : k = z.length := by omega
      have hiBlank : c.input.read = Γ.blank := by
        rw [Tape.read, hiHead, hiCells]
        exact Tape.init_ofBool_cells_ge z k (by omega)
      have hiStart : c.input.read ≠ Γ.start := by
        rw [hiBlank]
        decide
      obtain ⟨c', hstep, hhalt, hiEq, hwEq, hoHead', hoCell⟩ :=
        validationTM_step_halt c state hst hiStart hiBlank hwork hout hoHead
      refine ⟨c', .step hstep .zero, hhalt, ?_, ?_, hwEq, hoHead', ?_⟩
      · rw [hiEq]
        exact hiCells
      · rw [hiEq, hiHead, hk]
      · have hDrop : z.drop k = [] := by simp [hk]
        simpa [hDrop] using hoCell
  | succ m ih =>
      have hk : k < z.length := by omega
      have hiRead : c.input.read = Γ.ofBool (z[k]'hk) := by
        rw [Tape.read, hiHead, hiCells]
        exact Tape.init_ofBool_cells_lt z k hk
      have hiStart : c.input.read ≠ Γ.start := by
        rw [hiRead]
        exact Γ.ofBool_ne_start _
      have hiBlank : c.input.read ≠ Γ.blank := by
        rw [hiRead]
        exact Γ.ofBool_ne_blank _
      obtain ⟨c₁, hstep, hst₁, hiHead₁, hiCells₁, hwEq₁, hoEq₁⟩ :=
        validationTM_step_scan c state hst hiStart hiBlank hwork hout
      have hbit : decide (c.input.read = Γ.one) = z[k]'hk := by
        rw [hiRead]
        cases z[k]'hk <;> simp [Γ.ofBool]
      rw [hbit] at hst₁
      have hLength₁ : z.length = (k + 1) + m := by omega
      have hiCells₁' : c₁.input.cells = (Tape.init (z.map Γ.ofBool)).cells := by
        rw [hiCells₁]
        exact hiCells
      have hiHead₁' : c₁.input.head = (k + 1) + 1 := by
        rw [hiHead₁, hiHead]
      have hwork₁ : ∀ i, TM.Parked (c₁.work i) := by
        rw [hwEq₁]
        exact hwork
      have hout₁ : TM.Parked c₁.output := by
        rw [hoEq₁]
        exact hout
      have hoHead₁ : c₁.output.head = 1 := by
        rw [hoEq₁]
        exact hoHead
      obtain ⟨c', hreach, hhalt, hiCells', hiHead', hwEq', hoHead', hoCell⟩ :=
        ih (k + 1) hLength₁ (state.step (z[k]'hk)) c₁ hst₁
          hiCells₁' hiHead₁' hwork₁ hout₁ hoHead₁
      refine ⟨c', .step hstep hreach, hhalt, hiCells', hiHead', ?_, hoHead', ?_⟩
      · rw [hwEq', hwEq₁]
      · have hDrop : z.drop k = (z[k]'hk) :: z.drop (k + 1) :=
          List.drop_eq_getElem_cons hk
        rw [hoCell, hDrop, List.foldl_cons]

/-- **Exact validation execution.** Starting from `initCfg z`, the machine
halts in exactly `|z|+2` steps, preserves the input cells and all work cells,
and writes the Boolean `validEncoding z` to output cell one. -/
theorem validationTM_reachesIn_internal (z : List Bool) :
    ∃ c', (validationTM (n := n)).reachesIn (z.length + 2)
        ((validationTM (n := n)).initCfg z) c' ∧
      (validationTM (n := n)).halted c' ∧
      c'.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      c'.input.head = z.length + 1 ∧
      c'.work = (fun _ => ⟨1, (Tape.init []).cells⟩) ∧
      c'.output.head = 1 ∧
      c'.output.cells 1 = if validEncoding z then Γ.one else Γ.zero := by
  have hstep := validationTM_step_init (n := n) z
  have hwork : ∀ i, TM.Parked ((validationStartedCfg (n := n) z).work i) :=
    fun _ => TM.reg_zero_init_bumped.parked
  have hout : TM.Parked (validationStartedCfg (n := n) z).output :=
    TM.outAcc_nil_init.parked
  obtain ⟨c', hreach, hhalt, hiCells, hiHead, hwEq, hoHead, hoCell⟩ :=
    validationTM_scan z z.length 0 (by omega) .initial
      (validationStartedCfg (n := n) z) rfl rfl rfl hwork hout rfl
  refine ⟨c', .step hstep hreach, hhalt, hiCells, hiHead, ?_, hoHead, ?_⟩
  · simpa [validationStartedCfg] using hwEq
  · cases haccept : (z.foldl ValidationState.step ValidationState.initial).accepts <;>
      simp [validEncoding, haccept] at hoCell ⊢
    · exact hoCell
    · exact hoCell

/-- Hoare interface for the exact initial-tape execution theorem. -/
theorem validationTM_hoareTime_internal (z : List Bool) :
    (validationTM (n := n)).HoareTime
      (fun inp work out =>
        inp = Tape.init (z.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
        inp.head = z.length + 1 ∧
        work = (fun _ => ⟨1, (Tape.init []).cells⟩) ∧
        out.head = 1 ∧
        out.cells 1 = if validEncoding z then Γ.one else Γ.zero)
      (z.length + 2) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  obtain ⟨c', hreach, hhalt, hiCells, hiHead, hwork, hoHead, hoCell⟩ :=
    validationTM_reachesIn_internal (n := n) z
  exact ⟨c', z.length + 2, le_rfl, hreach, hhalt,
    hiCells, hiHead, hwork, hoHead, hoCell⟩

end Machine

end ThreeSAT

end SAT

end Complexity
