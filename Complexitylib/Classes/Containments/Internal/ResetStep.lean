/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FamStep
public import Complexitylib.Models.TuringMachine.Subroutines.ResetBinary

/-!
# Putting the tapes back between walks

⚠️ Unreviewed by Bolton

A loop that walks once per candidate has to undo what the last walk did: the machine's own input
head has followed the simulated one, and the walk's step counter has counted up to the round
index. Neither is a scan register, so both are restored by ordinary subroutines — and this file
says that `Complexity.WalkTapes`, the frame every stage needs, survives them.

## Main results

- `walkTapes_rewind` — rewinding the input head keeps the frame
- `walkTapes_reset` — clearing an auxiliary counter keeps it too
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-! ## The guess protocol for the tape-restoring subroutines

These are ordinary subroutines that never look at the guess tape. The lemmas belong upstream with
the machines themselves; they are here because this is where the need for them arose. -/

theorem TM.guessProtocol_rewindInputTM {k : ℕ} :
    TM.GuessProtocol (TM.rewindInputTM (n := k + 1)) (fun _ => false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq iHead wHeads oHead
    cases q with
    | moveLeft => by_cases hi : iHead = Γ.start <;> simp [TM.rewindInputTM, hi]
    | moveRight => simp [TM.rewindInputTM]
    | done => exact absurd rfl hq
  · intro q hq iHead wHeads oHead hg
    cases q with
    | moveLeft => by_cases hi : iHead = Γ.start <;> simp [TM.rewindInputTM, hi, idleDir, hg]
    | moveRight => simp [TM.rewindInputTM, idleDir, hg]
    | done => exact absurd rfl hq
  · intro q hq _ iHead ww oHead g g'
    cases q with
    | moveLeft =>
      by_cases hi : iHead = Γ.start <;>
        simp [TM.rewindInputTM, TM.visible, hi, Fin.snoc_castSucc]
    | moveRight => simp [TM.rewindInputTM, TM.visible, Fin.snoc_castSucc]
    | done => exact absurd rfl hq

theorem TM.guessProtocol_rewindWorkTM {k : ℕ} (idx : Fin (k + 1)) (hidx : idx ≠ Fin.last k) :
    TM.GuessProtocol (TM.rewindWorkTM idx) (fun _ => false) := by
  have hne : Fin.last k ≠ idx := fun h => hidx h.symm
  refine ⟨?_, ?_, ?_⟩
  · intro q hq iHead wHeads oHead
    cases q with
    | moveLeft => by_cases hi : wHeads idx = Γ.start <;> simp [TM.rewindWorkTM, hi]
    | moveRight => simp [TM.rewindWorkTM]
    | done => exact absurd rfl hq
  · intro q hq iHead wHeads oHead hg
    cases q with
    | moveLeft =>
      by_cases hi : wHeads idx = Γ.start <;> simp [TM.rewindWorkTM, hi, hne, idleDir, hg]
    | moveRight => simp [TM.rewindWorkTM, idleDir, hg]
    | done => exact absurd rfl hq
  · intro q hq _ iHead ww oHead g g'
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hidx
    cases q with
    | moveLeft =>
      by_cases hi : ww j = Γ.start <;>
        simp [TM.rewindWorkTM, TM.visible, hi, Fin.snoc_castSucc]
    | moveRight => simp [TM.rewindWorkTM, TM.visible, Fin.snoc_castSucc]
    | done => exact absurd rfl hq

theorem TM.guessProtocol_blankWorkTM {k : ℕ} (idx : Fin (k + 1)) (hidx : idx ≠ Fin.last k) :
    TM.GuessProtocol (TM.blankWorkTM idx) (fun _ => false) := by
  have hne : Fin.last k ≠ idx := fun h => hidx h.symm
  refine ⟨?_, ?_, ?_⟩
  · intro q hq iHead wHeads oHead
    cases q with
    | scanning => by_cases hi : wHeads idx = Γ.blank <;> simp [TM.blankWorkTM, hi, hne]
    | done => exact absurd rfl hq
  · intro q hq iHead wHeads oHead hg
    cases q with
    | scanning =>
      by_cases hi : wHeads idx = Γ.blank <;> simp [TM.blankWorkTM, hi, hne, idleDir, hg]
    | done => exact absurd rfl hq
  · intro q hq _ iHead ww oHead g g'
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hidx
    cases q with
    | scanning =>
      by_cases hi : ww j = Γ.blank <;>
        simp [TM.blankWorkTM, TM.visible, hi, Fin.snoc_castSucc]
    | done => exact absurd rfl hq

theorem TM.guessProtocol_clearWorkTM {k : ℕ} (idx : Fin (k + 1)) (hidx : idx ≠ Fin.last k) :
    TM.GuessProtocol (TM.clearWorkTM idx)
      (TM.seqAdv (fun _ => false) (fun _ => false)) :=
  TM.guessProtocol_seqTM (TM.guessProtocol_blankWorkTM idx hidx)
    (TM.guessProtocol_rewindWorkTM idx hidx)

theorem TM.guessProtocol_resetBinaryWorkTM {k : ℕ} (idx : Fin (k + 1))
    (hidx : idx ≠ Fin.last k) :
    TM.GuessProtocol (TM.resetBinaryWorkTM idx)
      (TM.seqAdv (fun _ => false) (TM.seqAdv (fun _ => false) (fun _ => false))) :=
  TM.guessProtocol_seqTM (TM.guessProtocol_rewindWorkTM idx hidx)
    (TM.guessProtocol_clearWorkTM idx hidx)

/-- **Rewinding the input head keeps the frame**, and touches nothing else. -/
theorem walkTapes_rewind (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s : ℕ) (cc : Fin r) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (Binp : ℕ) :
    (TM.rewindInputTM (n := jj + 2 + r + 1)).HoareTime
      (fun inp work out =>
        WalkTapes (r := r) x L g s cc Wa Wt inp work out ∧ inp.head ≤ Binp)
      (fun inp work out =>
        WalkTapes (r := r) x L g s cc Wa Wt inp work out ∧ inp.head = 1)
      (Binp + 2) := by
  refine (TM.rewindInputTM_hoareTime_frame (n := jj + 2 + r + 1) Binp
    (P := fun inp work out => WalkTapes (r := r) x L g s cc Wa Wt inp work out)
    (fun inp work out inp' work' out' hP hcells hhead hwork hout => ?_)).consequence
    (fun inp work out h => ?_) (fun inp work out h => ⟨h.2, h.1⟩) le_rfl
  · subst hwork
    subst hout
    exact ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, by rw [hcells]; exact hP.2.2.2.2.2.1,
      by rw [hhead], hP.2.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2.2.2.1,
      hP.2.2.2.2.2.2.2.2.2.2⟩
  · obtain ⟨htapes, hle⟩ := h
    refine ⟨?_, fun q hq => ?_, hle, ?_, ?_, fun i => ?_, htapes⟩
    · rw [show inp.cells 0 = (Tape.init (x.map Γ.ofBool)).cells 0 from
        congrFun htapes.2.2.2.2.2.1 0]
      exact Tape.init_cells_zero _
    · rw [show inp.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
        congrFun htapes.2.2.2.2.2.1 q]
      exact Tape.init_ofBool_cells_ne_start x q hq
    · exact htapes.2.2.2.2.2.2.2.1.read_ne_start htapes.2.2.2.2.2.2.2.2.1
    · exact htapes.2.2.2.2.2.2.2.2.1
    · exact ⟨(htapes.2.1 i).read_ne_start (htapes.2.2.1 i), htapes.2.2.1 i⟩

/-- **And it leaves the work and output tapes exactly as they were.** -/
theorem rewind_tapes_eq (Binp : ℕ) {n : ℕ} (inp₀ out₀ : Tape) (W₀ : Fin n → Tape)
    (hcell0 : inp₀.cells 0 = Γ.start) (hns : ∀ j, j ≥ 1 → inp₀.cells j ≠ Γ.start)
    (hle : inp₀.head ≤ Binp) (hout : out₀.read ≠ Γ.start) (houth : out₀.head ≥ 1)
    (hwork : ∀ i, (W₀ i).read ≠ Γ.start ∧ (W₀ i).head ≥ 1) :
    ∃ (c : Cfg n (TM.rewindInputTM (n := n)).Q) (t : ℕ), t ≤ Binp + 2 ∧
      (TM.rewindInputTM (n := n)).reachesIn t
        ⟨(TM.rewindInputTM (n := n)).qstart, inp₀, W₀, out₀⟩ c ∧
      (TM.rewindInputTM (n := n)).halted c ∧
      c.input.head = 1 ∧ c.input.cells = inp₀.cells ∧ c.work = W₀ ∧ c.output = out₀ := by
  have h := TM.rewindInputTM_hoareTime_frame (n := n) Binp
    (P := fun inp work out => inp.cells = inp₀.cells ∧ work = W₀ ∧ out = out₀)
    (fun inp work out inp' work' out' hP hcells hhead hwork' hout' => by
      exact ⟨by rw [hcells]; exact hP.1, by rw [hwork']; exact hP.2.1,
        by rw [hout']; exact hP.2.2⟩)
    inp₀ W₀ out₀ ⟨hcell0, hns, hle, hout, houth, hwork, rfl, rfl, rfl⟩
  obtain ⟨c, t, htle, hreach, hhalt, hh, hcells, hwork', hout'⟩ := h
  exact ⟨c, t, htle, hreach, hhalt, hh, hcells, hwork', hout'⟩

/-- **Clearing an auxiliary counter keeps the frame.** The counter is not a scan register, so the
stages that follow see the same registers; only the record of the auxiliary tapes moves on. -/
theorem walkTapes_reset (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (g : ℕ → Bool) (s : ℕ) (cc c : Fin r) (hc : c ≠ cc) (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ)
    (bits : List Bool) (headBound : ℕ) (inp₀ out₀ : Tape) (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀)
    (hbits : (W₀ (auxIdx jj c)).HasBinaryContent bits)
    (hhead : (W₀ (auxIdx jj c)).head ≤ headBound) :
    (TM.resetBinaryWorkTM (auxIdx jj c)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₀ ∧ out = out₀)
      (fun inp work out =>
        WalkTapes (r := r) x L g s cc
          (Function.update Wa c ((Tape.init []).move Dir3.right)) Wt inp work out ∧
        inp = inp₀ ∧ out = out₀ ∧
        work = Function.update W₀ (auxIdx jj c) ((Tape.init []).move Dir3.right))
      (TM.resetBinaryWorkTime headBound bits.length) := by
  have hSI : ((Tape.init ([] : List Γ)).move Dir3.right).StartInvariant := by
    refine ⟨?_, fun q hq => ?_⟩
    · rw [Tape.move_cells]
      exact Tape.init_cells_zero ([] : List Γ)
    · rw [Tape.move_cells]
      exact Tape.init_ofBool_cells_ne_start [] q hq
  have hhead1 : ((Tape.init ([] : List Γ)).move Dir3.right).head = 1 := rfl
  refine (TM.resetBinaryWorkTM_hoareTime_frame (auxIdx jj c) bits headBound inp₀ W₀ out₀
    hbits (htapes.2.1 (auxIdx jj c)).1 ⟨htapes.2.2.1 (auxIdx jj c), hhead⟩
    ⟨htapes.2.2.2.2.2.2.1, fun q hq => ?_⟩
    (fun i _ => ⟨htapes.2.2.1 i, fun q hq => (htapes.2.1 i).2 q hq⟩)
    ⟨htapes.2.2.2.2.2.2.2.2.1, fun q hq => htapes.2.2.2.2.2.2.2.1.2 q hq⟩).consequence
    (fun inp work out h => h) (fun inp work out h => ⟨?_, h.1, h.2.2, h.2.1⟩) le_rfl
  · rw [show inp₀.cells q = (Tape.init (x.map Γ.ofBool)).cells q from
      congrFun htapes.2.2.2.2.2.1 q]
    exact Tape.init_ofBool_cells_ne_start x q hq
  · obtain ⟨hinp, hwork, hout⟩ := h
    subst hinp
    subst hwork
    subst hout
    refine ⟨fun c' hc' => ?_, fun i => ?_, fun i => ?_, fun i => ?_, ?_, htapes.2.2.2.2.2.1,
      htapes.2.2.2.2.2.2.1, htapes.2.2.2.2.2.2.2.1, htapes.2.2.2.2.2.2.2.2.1, ?_, fun p hp q => ?_⟩
    · by_cases hcc : c' = c
      · subst hcc
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (fun hcx => hcc (by
          have hv := congrArg Fin.val hcx
          simp only [auxIdx, val_natAdd_castSucc] at hv
          exact Fin.ext (by omega))), Function.update_of_ne hcc]
        exact htapes.1 c' hc'
    · by_cases hi : i = auxIdx jj c
      · rw [hi, Function.update_self]
        exact hSI
      · rw [Function.update_of_ne hi]
        exact htapes.2.1 i
    · by_cases hi : i = auxIdx jj c
      · rw [hi, Function.update_self, hhead1]
      · rw [Function.update_of_ne hi]
        exact htapes.2.2.1 i
    · rw [Function.update_of_ne (auxIdx_ne_castAdd c i).symm]
      exact htapes.2.2.2.1 i
    · rw [Function.update_of_ne (walkReg_ne_auxIdx _ c)]
      exact htapes.2.2.2.2.1
    · rw [Function.update_of_ne (auxIdx_ne_last c).symm]
      exact htapes.2.2.2.2.2.2.2.2.2.1
    · rw [Function.update_of_ne (walkReg_ne_auxIdx _ c)]
      exact htapes.2.2.2.2.2.2.2.2.2.2 p hp q

end Complexity
