/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.Subroutines.PairSplit.Defs
import Complexitylib.Models.TuringMachine.Subroutines.PairSplit.Internal

/-!
# Split a paired input onto work tapes

`pairSplitCoreTM` is the deterministic machine-level inverse of the neutral
`pair` codec. On a canonical input `pair x y`, it writes `x` and `y` to two
distinct work tapes in exact time `2 * |x| + |y| + 4`.

This is intentionally a canonical-pair primitive, not a total recognizer for
the image of `pair`: malformed inputs may share its halting state. A client
requiring rejecting semantics for arbitrary outer strings must use a parser
with a distinct failure result.

## Main results

- `pairSplitCoreTM_reachesIn_initCfg` — exact initialized endpoint with frames.
- `pairSplitCoreTM_from_init_initTape_move_right` — exact endpoint semantics.
- `pairSplitCoreTM_hoareTime_frame` — compositional frame-preserving specification.
- `pairSplitCoreTM_hoareTime` — compact target-tape specification.
-/

namespace Complexity

namespace TM

/-- On a canonical pair, the splitter's exact time is the encoded input
length plus two steps. -/
@[simp] theorem pairSplitCoreTime_eq_pair_length (x y : List Bool) :
    pairSplitCoreTime x.length y.length = (pair x y).length + 2 := by
  simp [pairSplitCoreTime, pair_length]
  omega

/-- Exact pair-split correctness from the genuine machine initialization.
The target work tapes contain the decoded components, while every unrelated
work tape and the output are the canonical started blank tape. -/
theorem pairSplitCoreTM_reachesIn_initCfg
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx) (x y : List Bool) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn
        (pairSplitCoreTime x.length y.length)
        ((pairSplitCoreTM xIdx yIdx).initCfg (pair x y)) c' ∧
      (pairSplitCoreTM xIdx yIdx).halted c' ∧
      c'.input.head = (pair x y).length + 1 ∧
      c'.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
      (c'.work xIdx).head = 1 + x.length ∧
      (c'.work xIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < x.length) →
        (c'.work xIdx).cells (i + 1) = Γ.ofBool (x[i]'h)) ∧
      (∀ i, x.length ≤ i → (c'.work xIdx).cells (i + 1) = Γ.blank) ∧
      (c'.work yIdx).head = 1 + y.length ∧
      (c'.work yIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < y.length) →
        (c'.work yIdx).cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) ∧
      (∀ i, i ≠ xIdx → i ≠ yIdx →
        c'.work i = (Tape.init []).move Dir3.right) ∧
      c'.output = (Tape.init []).move Dir3.right :=
  pairSplitCoreTM_from_initCfg_internal xIdx yIdx hne x y

/-- Core correctness from the already-started `.scanX` phase. This preserves
the theorem name formerly exposed from the NP-internal implementation. -/
theorem pairSplitCoreTM_from_scanX_initTape_move_right
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .scanX)
    (hinp : c.input = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (hxw : c.work xIdx = (Tape.init []).move Dir3.right)
    (hyw : c.work yIdx = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn
        (2 * x.length + y.length + 3) c c' ∧
      (pairSplitCoreTM xIdx yIdx).halted c' ∧
      c'.input.head = (pair x y).length + 1 ∧
      c'.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
      (c'.work xIdx).head = 1 + x.length ∧
      (c'.work xIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < x.length) →
        (c'.work xIdx).cells (i + 1) = Γ.ofBool (x[i]'h)) ∧
      (∀ i, x.length ≤ i → (c'.work xIdx).cells (i + 1) = Γ.blank) ∧
      (c'.work yIdx).head = 1 + y.length ∧
      (c'.work yIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < y.length) →
        (c'.work yIdx).cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) :=
  pairSplitCoreTM_from_scanX_initTape_move_right_internal
    xIdx yIdx hne x y c hst hinp hxw hyw

/-- One phase-composition step from `.init` to `.scanX`, preserving the
already-started input and target work tapes. -/
theorem pairSplit_init_step_all_started {k : ℕ} (xIdx yIdx : Fin k)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .init)
    (hinp : c.input.read ≠ Γ.start)
    (hx : (c.work xIdx).read ≠ Γ.start)
    (hy : (c.work yIdx).read ≠ Γ.start) :
    ∃ c', (pairSplitCoreTM xIdx yIdx).step c = some c' ∧
      c'.state = .scanX ∧
      c'.input = c.input ∧
      c'.work xIdx = c.work xIdx ∧
      c'.work yIdx = c.work yIdx :=
  pairSplit_init_step_all_started_internal xIdx yIdx c hst hinp hx hy

/-- Starting from `.init` with a canonical pair and two empty started work
tapes, `pairSplitCoreTM` halts in its exact advertised time. The two target
tapes contain the decoded components and finish immediately after them. -/
theorem pairSplitCoreTM_from_init_initTape_move_right
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool)
    (c : Cfg k (pairSplitCoreTM xIdx yIdx).Q)
    (hst : c.state = .init)
    (hinp : c.input = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right)
    (hxw : c.work xIdx = (Tape.init []).move Dir3.right)
    (hyw : c.work yIdx = (Tape.init []).move Dir3.right) :
    ∃ c',
      (pairSplitCoreTM xIdx yIdx).reachesIn
        (pairSplitCoreTime x.length y.length) c c' ∧
      (pairSplitCoreTM xIdx yIdx).halted c' ∧
      c'.input.head = (pair x y).length + 1 ∧
      c'.input.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
      (c'.work xIdx).head = 1 + x.length ∧
      (c'.work xIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < x.length) →
        (c'.work xIdx).cells (i + 1) = Γ.ofBool (x[i]'h)) ∧
      (∀ i, x.length ≤ i → (c'.work xIdx).cells (i + 1) = Γ.blank) ∧
      (c'.work yIdx).head = 1 + y.length ∧
      (c'.work yIdx).cells 0 = Γ.start ∧
      (∀ i, (h : i < y.length) →
        (c'.work yIdx).cells (i + 1) = Γ.ofBool (y[i]'h)) ∧
      (∀ i, y.length ≤ i → (c'.work yIdx).cells (i + 1) = Γ.blank) :=
  pairSplitCoreTM_from_init_initTape_move_right_internal xIdx yIdx hne x y c
    hst hinp hxw hyw

/-- Frame-preserving compositional specification. In addition to decoding the
two target tapes, the splitter preserves an arbitrary off-start output tape
and every arbitrary off-start work tape outside the two targets. -/
theorem pairSplitCoreTM_hoareTime_frame
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) (frameWork : Fin k → Tape) (frameOutput : Tape)
    (hframeWork : ∀ i, i ≠ xIdx → i ≠ yIdx →
      (frameWork i).read ≠ Γ.start)
    (hframeOutput : frameOutput.read ≠ Γ.start) :
    (pairSplitCoreTM xIdx yIdx).HoareTime
      (fun inp work out =>
        inp = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
        work xIdx = (Tape.init []).move Dir3.right ∧
        work yIdx = (Tape.init []).move Dir3.right ∧
        (∀ i, i ≠ xIdx → i ≠ yIdx → work i = frameWork i) ∧
        out = frameOutput)
      (fun inp work out =>
        inp.head = (pair x y).length + 1 ∧
        inp.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
        (work xIdx).head = 1 + x.length ∧
        (work xIdx).HasOutput x ∧
        (work yIdx).head = 1 + y.length ∧
        (work yIdx).HasOutput y ∧
        (∀ i, i ≠ xIdx → i ≠ yIdx → work i = frameWork i) ∧
        out = frameOutput)
      (pairSplitCoreTime x.length y.length) := by
  intro inp work out hpre
  rcases hpre with ⟨hinp, hxw, hyw, hwork, hout⟩
  let c : Cfg k (pairSplitCoreTM xIdx yIdx).Q :=
    { state := (pairSplitCoreTM xIdx yIdx).qstart
      input := inp
      work := work
      output := out }
  obtain ⟨c', hreach, hhalt, hinputHead, hinputCells,
      hxHead, -, hxData, hxTail, hyHead, -, hyData, hyTail⟩ :=
    pairSplitCoreTM_from_init_initTape_move_right_internal xIdx yIdx hne x y c
      rfl hinp hxw hyw
  have htrace :
      ((pairSplitCoreTM xIdx yIdx).toNTM).trace
        (pairSplitCoreTime x.length y.length) (fun _ => false) c = c' :=
    (pairSplitCoreTM xIdx yIdx).toNTM_trace_of_reachesIn
      hreach hhalt le_rfl (fun _ => false)
  have hother : ∀ i, i ≠ xIdx → i ≠ yIdx → c'.work i = frameWork i := by
    intro i hix hiy
    have hread : (c.work i).read ≠ Γ.start := by
      change (work i).read ≠ Γ.start
      rw [hwork i hix hiy]
      exact hframeWork i hix hiy
    have hpres := pairSplitCoreTM_toNTM_trace_preserves_other_work_internal
      xIdx yIdx i (pairSplitCoreTime x.length y.length) (fun _ => false) c
        hix hiy hread
    rw [htrace] at hpres
    exact hpres.trans (hwork i hix hiy)
  have hout' : c'.output = frameOutput := by
    have hread : c.output.read ≠ Γ.start := by
      change out.read ≠ Γ.start
      rw [hout]
      exact hframeOutput
    have hpres := pairSplitCoreTM_toNTM_trace_preserves_output_internal
      xIdx yIdx (pairSplitCoreTime x.length y.length) (fun _ => false) c hread
    rw [htrace] at hpres
    exact hpres.trans hout
  refine ⟨c', pairSplitCoreTime x.length y.length, le_rfl, hreach, hhalt,
    hinputHead, hinputCells, hxHead, ?_, hyHead, ?_, hother, hout'⟩
  · exact ⟨hxData, hxTail x.length le_rfl⟩
  · exact ⟨hyData, hyTail y.length le_rfl⟩

/-- Compositional canonical-pair specification. The target work tapes begin
empty at cell `1`; on exit they contain the two decoded strings, with their
heads just after the data. This compact theorem makes no claim about unrelated
work tapes or the output; use `pairSplitCoreTM_hoareTime_frame` when those
frames must be preserved. -/
theorem pairSplitCoreTM_hoareTime
    {k : ℕ} (xIdx yIdx : Fin k) (hne : xIdx ≠ yIdx)
    (x y : List Bool) :
    (pairSplitCoreTM xIdx yIdx).HoareTime
      (fun inp work _ =>
        inp = (Tape.init ((pair x y).map Γ.ofBool)).move Dir3.right ∧
        work xIdx = (Tape.init []).move Dir3.right ∧
        work yIdx = (Tape.init []).move Dir3.right)
      (fun inp work _ =>
        inp.head = (pair x y).length + 1 ∧
        inp.cells = (Tape.init ((pair x y).map Γ.ofBool)).cells ∧
        (work xIdx).head = 1 + x.length ∧
        (work xIdx).HasOutput x ∧
        (work yIdx).head = 1 + y.length ∧
        (work yIdx).HasOutput y)
      (pairSplitCoreTime x.length y.length) := by
  intro inp work out hpre
  obtain ⟨hinp, hxw, hyw⟩ := hpre
  let c : Cfg k (pairSplitCoreTM xIdx yIdx).Q :=
    { state := (pairSplitCoreTM xIdx yIdx).qstart
      input := inp
      work := work
      output := out }
  obtain ⟨c', hreach, hhalt, hinputHead, hinputCells,
      hxHead, -, hxData, hxTail, hyHead, -, hyData, hyTail⟩ :=
    pairSplitCoreTM_from_init_initTape_move_right_internal xIdx yIdx hne x y c
      rfl hinp hxw hyw
  refine ⟨c', pairSplitCoreTime x.length y.length, le_rfl, hreach, hhalt,
    hinputHead, hinputCells, hxHead, ?_, hyHead, ?_⟩
  · exact ⟨hxData, hxTail x.length le_rfl⟩
  · exact ⟨hyData, hyTail y.length le_rfl⟩

end TM

end Complexity
