import Complexitylib.Models.TuringMachine.Combinators
import Complexitylib.Models.TuringMachine.UTM.Defs
import Complexitylib.Models.TuringMachine.UTM.Helpers
import Complexitylib.Models.TuringMachine.UTM.ReadCurrent
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Mathlib.Data.Fintype.Prod

/-!
# UTM Extract Output

After the simulation loop terminates, extract the simulated output from the
super-cell encoding and write it to the real output tape.

## Architecture

The machine operates in three phases:

1. **Rewind output**: Scan the output tape left to ▷, then move right to cell 1.
2. **Scan to output symbol**: Move the sim tape head right by a fixed distance
   to reach the hi bit of the output tape's position-1 super-cell. The distance
   is `3*(n+2) + 3*(n+1) + 1` cells from cell 1, computed as: one full super-cell
   width (position 0) + tapes 0..n within position 1 + the head marker.
3. **Read and decode**: Read the 2 symbol cells (hi, lo), decode via
   `SuperCell.cellPairToSym`, write to output cell 1.

## Main results

- `extractOutputTM` — the machine definition
- `extractOutputTM_hoareTime` — HoareTime spec: parametric in `simCfg`
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Distance from sim tape cell 1 to the hi bit of the output tape's
    position-1 super-cell. -/
def extractSkipDist (n : ℕ) : ℕ := 3 * (n + 2) + 3 * (n + 1) - 1

/-- States for the extractOutput machine. -/
inductive ExtractOutputQ (n : ℕ) where
  /-- Rewind output tape left until ▷. -/
  | rewindOut
  /-- Output at ▷, move right one step to cell 1. -/
  | rightOut
  /-- Scan sim tape right, `rem` steps remaining until hi bit. -/
  | scanSim (rem : Fin (extractSkipDist n + 1))
  /-- At hi bit position on sim tape. Read it. -/
  | readHi
  /-- At lo bit position. Remembering hi value. -/
  | readLo (hi : Γ)
  /-- Decode (hi, lo) → symbol, write to output. -/
  | writeOut (hi lo : Γ)
  /-- Halt. -/
  | done
  deriving DecidableEq

private instance : Fintype (ExtractOutputQ n) where
  elems :=
    {.rewindOut, .rightOut, .readHi, .done} ∪
    (Finset.univ.image fun (i : Fin (extractSkipDist n + 1)) =>
      ExtractOutputQ.scanSim i) ∪
    (Finset.univ.image fun (g : Γ) => ExtractOutputQ.readLo g) ∪
    (Finset.univ.image fun (p : Γ × Γ) => ExtractOutputQ.writeOut p.1 p.2)
  complete x := by
    cases x with
    | rewindOut => simp [Finset.mem_union, Finset.mem_insert]
    | rightOut => simp [Finset.mem_union, Finset.mem_insert]
    | readHi => simp [Finset.mem_union, Finset.mem_insert]
    | done => simp [Finset.mem_union, Finset.mem_insert]
    | scanSim i =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; left; right; exact ⟨i, rfl⟩
    | readLo g =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      left; right; exact ⟨g, rfl⟩
    | writeOut hi lo =>
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
        Prod.exists]
      right; exact ⟨hi, lo, rfl⟩

-- ════════════════════════════════════════════════════════════════════════
-- Machine definition
-- ════════════════════════════════════════════════════════════════════════

/-- Extract the simulated output and write it to the real output tape.

    Phase 1: Rewind output tape to ▷, then step right to cell 1.
    Phase 2: Scan sim tape right by `extractSkipDist n` cells to reach the
    output tape's position-1 hi bit.
    Phase 3: Read hi and lo bits, decode, write to output cell 1. -/
def extractOutputTM : TM 4 where
  Q := ExtractOutputQ n
  qstart := .rewindOut
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rewindOut =>
      if oHead = Γ.start then
        -- At ▷, move right to cell 1
        (.rightOut,
         fun i => readBackWrite (wHeads i), .blank,
         idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
      else
        -- Move output left
        (.rewindOut,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), moveLeftDir oHead)
    | .rightOut =>
      -- Output is now at cell 1. Start scanning sim tape.
      (.scanSim ⟨extractSkipDist n, by omega⟩,
       fun i => readBackWrite (wHeads i),
       readBackWrite oHead,
       idleDir iHead,
       fun i => if i = utmSimTape then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    | .scanSim rem =>
      if h : rem.val = 0 then
        -- Arrived at hi bit. Read it.
        (.readHi,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmSimTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        -- Keep scanning right on sim tape
        (.scanSim ⟨rem.val - 1, by omega⟩,
         fun i => readBackWrite (wHeads i),
         readBackWrite oHead,
         idleDir iHead,
         fun i => if i = utmSimTape then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .readHi =>
      -- At hi bit cell. Remember it, advance to lo bit.
      (.readLo (wHeads utmSimTape),
       fun i => readBackWrite (wHeads i),
       readBackWrite oHead,
       idleDir iHead,
       fun i => if i = utmSimTape then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    | .readLo hi =>
      -- At lo bit cell. Decode (hi, lo) and prepare to write.
      (.writeOut hi (wHeads utmSimTape),
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .writeOut hi lo =>
      -- Write the decoded symbol to output cell 1.
      let sym : Γw := match hi, lo with
        | .zero, .zero   => .zero   -- Γ.zero
        | .zero, .one    => .one    -- Γ.one
        | .blank, .blank => .blank  -- Γ.blank
        | _, _           => .blank  -- fallback (shouldn't occur for valid super-cells)
      (.done,
       fun i => readBackWrite (wHeads i), sym,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    have hros := fun (h : iHead = Γ.start) => idleDir_right_of_start h
    have hrosW := fun (i : Fin 4) (h : wHeads i = Γ.start) => idleDir_right_of_start h
    have hrosO := fun (h : oHead = Γ.start) => idleDir_right_of_start h
    have simRos : ∀ i, wHeads i = Γ.start →
        (if i = utmSimTape then Dir3.right else idleDir (wHeads i)) = Dir3.right := by
      intro i hi; split <;> [rfl; exact idleDir_right_of_start hi]
    match state with
    | .rewindOut =>
      dsimp only []; split
      · exact ⟨hros, fun _ => hrosW _, fun _ => rfl⟩
      · exact ⟨hros, fun _ => hrosW _, fun h => by subst h; rfl⟩
    | .rightOut =>
      dsimp only []
      exact ⟨hros, simRos, hrosO⟩
    | .scanSim rem =>
      dsimp only []; split
      · exact ⟨hros, simRos, hrosO⟩
      · exact ⟨hros, simRos, hrosO⟩
    | .readHi =>
      dsimp only []
      exact ⟨hros, simRos, hrosO⟩
    | .readLo _ =>
      exact ⟨hros, fun _ => hrosW _, hrosO⟩
    | .writeOut _ _ =>
      exact ⟨hros, fun _ => hrosW _, hrosO⟩
    | .done =>
      exact ⟨hros, fun _ => hrosW _, hrosO⟩

-- ════════════════════════════════════════════════════════════════════════
-- HoareTime specification
-- ════════════════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════════════════════════
-- Phase simulation lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- During idle operation, a tape with head ≥ 1 and read ≠ start is preserved by
    writeAndMove with readBackWrite and idleDir. -/
private theorem idle_tape_preserve (t : Tape) (hns : t.read ≠ Γ.start) (hh : t.head ≥ 1) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
  split
  · omega
  · simp only [Tape.read] at hns ⊢
    have : (readBackWrite (t.cells t.head)).toΓ = t.cells t.head := by
      cases h : t.cells t.head <;> simp_all [readBackWrite, Γw.toΓ]
    rw [this, Function.update_eq_self]

/-- Input tape is preserved by move with idleDir when read ≠ start. -/
private theorem input_idle_preserve (t : Tape) (hns : t.read ≠ Γ.start) :
    t.move (idleDir t.read) = t := by
  simp only [Tape.move, idleDir, hns, ↓reduceIte]

/-- superCellsCorrect implies sim tape cells ≥ 1 are never ▷.
    All super-cell content uses only zero/one/blank. -/
private theorem sim_cells_ne_start_of_scc {Q : Type} {simCfg : Cfg n Q}
    {utmSim : Tape} (hscc : superCellsCorrect simCfg utmSim)
    {j : ℕ} (hj : j ≥ 1) : utmSim.cells j ≠ Γ.start := by
  obtain ⟨_, hinp, hwork, hout⟩ := hscc
  -- Any cell within a correct super-cell is not Γ.start
  have cell_ne_of_scc : ∀ {tapeIdx pos simHead : ℕ} {simSym : Γ},
      simTapeCellCorrect (n + 2) tapeIdx pos simHead simSym utmSim →
      ∀ k, k < 3 →
        utmSim.cells (SuperCell.simTapeOffset (n + 2) pos tapeIdx + k) ≠ Γ.start := by
    intro tapeIdx pos simHead simSym h k hk
    cases simSym <;>
      dsimp only [simTapeCellCorrect, SuperCell.symToCellPair] at h <;>
      obtain ⟨h0, h1, h2⟩ := h <;>
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl
    all_goals first
      | (simp only [Nat.add_zero]; rw [h0]; split_ifs <;> decide)
      | (rw [h1]; decide)
      | (rw [h2]; decide)
  -- Every cell ≥ 1 maps to some super-cell coordinate (pos, tapeIdx, offset)
  -- Prove decomposition without set (to avoid omega issues with let bindings)
  have hj_eq : j = SuperCell.simTapeOffset (n + 2)
      ((j - 1) / (3 * (n + 2)))
      (((j - 1) % (3 * (n + 2))) / 3) +
      ((j - 1) % (3 * (n + 2))) % 3 := by
    simp only [SuperCell.simTapeOffset, SuperCell.width]
    have h1 := Nat.div_add_mod (j - 1) (3 * (n + 2))
    have h2 := Nat.div_add_mod ((j - 1) % (3 * (n + 2))) 3
    have hmc : (3 * (n + 2)) * ((j - 1) / (3 * (n + 2))) =
        (j - 1) / (3 * (n + 2)) * (3 * (n + 2)) := Nat.mul_comm _ _
    rw [hmc] at h1
    omega
  rw [hj_eq]
  -- Prove bounds on coordinates
  have hmod : (j - 1) % (3 * (n + 2)) < 3 * (n + 2) := Nat.mod_lt _ (by omega)
  have htIdx : ((j - 1) % (3 * (n + 2))) / 3 < n + 2 := by
    have := Nat.div_mul_le_self ((j - 1) % (3 * (n + 2))) 3; omega
  have hoff : ((j - 1) % (3 * (n + 2))) % 3 < 3 := Nat.mod_lt _ (by omega)
  -- Map tapeIdx to the right component of superCellsCorrect
  by_cases h0 : ((j - 1) % (3 * (n + 2))) / 3 = 0
  · simp only [h0]; exact cell_ne_of_scc (hinp _) _ hoff
  · by_cases hn : ((j - 1) % (3 * (n + 2))) / 3 = n + 1
    · simp only [hn]; exact cell_ne_of_scc (hout _) _ hoff
    · have hscc' := hwork ⟨((j - 1) % (3 * (n + 2))) / 3 - 1, by omega⟩
          ((j - 1) / (3 * (n + 2)))
      simp only [] at hscc'
      rw [show ((j - 1) % (3 * (n + 2))) / 3 - 1 + 1 =
          ((j - 1) % (3 * (n + 2))) / 3 from by omega] at hscc'
      exact cell_ne_of_scc hscc' _ hoff

/-- Phase 1: Rewind output tape from position h to position 1.
    All work tapes with head ≥ 1 and read ≠ start are preserved. -/
private theorem rewind_output_phase
    (c : Cfg 4 (extractOutputTM (n := n)).Q) (h : ℕ)
    (hstate : c.state = .rewindOut)
    (hout_h : c.output.head = h)
    (hout0 : c.output.cells 0 = Γ.start)
    (hout_ns : ∀ j, j ≥ 1 → c.output.cells j ≠ Γ.start)
    (hsim_h : (c.work utmSimTape).head ≥ 1)
    (hsim_ns : (c.work utmSimTape).read ≠ Γ.start)
    (hinp_ns : c.input.read ≠ Γ.start) :
    ∃ c₁, (extractOutputTM (n := n)).reachesIn (h + 1) c c₁ ∧
      c₁.state = .rightOut ∧
      c₁.output.head = 1 ∧
      c₁.output.cells = c.output.cells ∧
      (c₁.work utmSimTape).head = (c.work utmSimTape).head ∧
      (c₁.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      c₁.input.read = c.input.read ∧
      c₁.input.head = c.input.head := by
  induction h generalizing c with
  | zero =>
    -- Output head at 0, reads Γ.start. One step to rightOut.
    have hoRead : c.output.read = Γ.start := by
      simp only [Tape.read, hout_h, hout0]
    -- Build the step
    have hstep : extractOutputTM.step c = some
      { state := .rightOut
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ
          (idleDir (c.work i).read)
        output := c.output.writeAndMove Γw.blank.toΓ Dir3.right } := by
      simp only [TM.step, extractOutputTM]
      split
      · next heq => simp [hstate] at heq
      · simp only [hstate]
    refine ⟨_, TM.reachesIn.step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- output.head = 1
      simp only [Tape.writeAndMove, Tape.write, hout_h, Tape.move, ite_true]
    · -- output.cells preserved
      simp only [Tape.writeAndMove, Tape.write, hout_h, Tape.move, ite_true]
    · -- sim tape head preserved
      simp only [idle_tape_preserve _ hsim_ns hsim_h]
    · -- sim tape cells preserved
      simp only [idle_tape_preserve _ hsim_ns hsim_h]
    · -- input.read preserved
      unfold Tape.read
      have hinp_ns' : c.input.cells c.input.head ≠ Γ.start := hinp_ns
      simp only [Tape.move, idleDir, hinp_ns', ↓reduceIte]
    · -- input.head preserved
      simp only [Tape.move, idleDir, hinp_ns, ↓reduceIte]
  | succ h' ih =>
    have hoRead : c.output.read ≠ Γ.start := by
      simp only [Tape.read]; exact hout_ns _ (by omega)
    have hinp_ns' : c.input.cells c.input.head ≠ Γ.start := hinp_ns
    let c' : Cfg 4 (extractOutputTM (n := n)).Q :=
      { state := .rewindOut
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ
          (idleDir (c.work i).read)
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (moveLeftDir c.output.read) }
    have hstep : (extractOutputTM (n := n)).step c = some c' := by
      simp only [TM.step, extractOutputTM]
      split
      · next heq => simp [hstate] at heq
      · simp only [hstate]; rfl
    have hc'_work_sim : c'.work utmSimTape = c.work utmSimTape :=
      show (c.work utmSimTape).writeAndMove _ _ = _ from
        idle_tape_preserve _ hsim_ns hsim_h
    have hc'_inp : c'.input = c.input := by
      show c.input.move (idleDir c.input.read) = c.input
      simp only [Tape.move, idleDir, Tape.read, hinp_ns', ↓reduceIte]
    have hout_head_ne0 : c.output.head ≠ 0 := by omega
    have hc'_out_h : c'.output.head = h' := by
      show (c.output.writeAndMove _ _).head = h'
      simp only [Tape.writeAndMove, Tape.write, Tape.move, moveLeftDir, hoRead, ↓reduceIte]
      split
      · omega
      · simp only [hout_h]; omega
    have hc'_out_cells : c'.output.cells = c.output.cells := by
      show (c.output.writeAndMove _ _).cells = c.output.cells
      simp only [Tape.writeAndMove, Tape.write, hout_head_ne0, ↓reduceIte, Tape.move,
        moveLeftDir, hoRead]
      have : (readBackWrite c.output.read).toΓ = c.output.cells c.output.head := by
        simp only [Tape.read]
        cases hcell : c.output.cells c.output.head
        · simp [readBackWrite, Γw.toΓ]
        · simp [readBackWrite, Γw.toΓ]
        · simp [readBackWrite, Γw.toΓ]
        · exact absurd (show c.output.read = Γ.start from by simp [Tape.read, hcell]) hoRead
      rw [this, Function.update_eq_self]
    have hc'_out0 : c'.output.cells 0 = Γ.start := by rw [hc'_out_cells]; exact hout0
    have hc'_out_ns : ∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start := by
      rw [hc'_out_cells]; exact hout_ns
    have hc'_sim_h : (c'.work utmSimTape).head ≥ 1 := hc'_work_sim ▸ hsim_h
    have hc'_sim_ns : (c'.work utmSimTape).read ≠ Γ.start := hc'_work_sim ▸ hsim_ns
    have hc'_inp_ns : c'.input.read ≠ Γ.start := hc'_inp ▸ hinp_ns
    obtain ⟨c₁, hreach, hc₁_state, hc₁_out_h, hc₁_out_cells, hc₁_sim_h,
      hc₁_sim_cells, hc₁_inp_read, hc₁_inp_head⟩ :=
      ih c' rfl hc'_out_h hc'_out0 hc'_out_ns hc'_sim_h hc'_sim_ns hc'_inp_ns
    refine ⟨c₁, ?_, hc₁_state, hc₁_out_h, ?_, ?_, ?_, ?_, ?_⟩
    · exact TM.reachesIn.step hstep hreach
    · rw [hc₁_out_cells, hc'_out_cells]
    · rw [hc₁_sim_h, hc'_work_sim]
    · rw [hc₁_sim_cells, hc'_work_sim]
    · rw [hc₁_inp_read]; exact congrArg Tape.read hc'_inp
    · rw [hc₁_inp_head]; exact congrArg Tape.head hc'_inp

/-- Phase 3: scanSim loop advances sim tape from position p to position p + d + 1.
    Other tapes idle. -/
private theorem scanSim_phase
    (c : Cfg 4 (extractOutputTM (n := n)).Q)
    (d : ℕ) (hd : d < extractSkipDist n + 1)
    (hstate : c.state = .scanSim ⟨d, hd⟩)
    (hsim_h : (c.work utmSimTape).head ≥ 1)
    (hsim_ns : ∀ j, j ≥ 1 → (c.work utmSimTape).cells j ≠ Γ.start)
    (hout_h : c.output.head ≥ 1) (hout_ns : c.output.read ≠ Γ.start)
    (hinp_ns : c.input.read ≠ Γ.start) :
    ∃ c₂, (extractOutputTM (n := n)).reachesIn (d + 1) c c₂ ∧
      c₂.state = .readHi ∧
      (c₂.work utmSimTape).head = (c.work utmSimTape).head + d + 1 ∧
      (c₂.work utmSimTape).cells = (c.work utmSimTape).cells ∧
      c₂.output = c.output := by
  induction d generalizing c with
  | zero =>
    -- One step: scanSim ⟨0, _⟩ → readHi, sim moves right, others idle
    -- Compute the step
    have hstep : (extractOutputTM (n := n)).step c = some
      { state := .readHi
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ
          (if i = utmSimTape then Dir3.right else idleDir (c.work i).read)
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) } := by
      simp only [TM.step, extractOutputTM]
      split
      · next heq => simp [hstate] at heq
      · simp only [hstate, Γw.toΓ, dite_true]
    -- Sim tape read is not start (for readBackWrite preservation)
    have hsim_read_ns : (c.work utmSimTape).read ≠ Γ.start :=
      hsim_ns _ hsim_h
    refine ⟨_, TM.reachesIn.step hstep .zero, rfl, ?_, ?_, ?_⟩
    · -- sim tape head: advances by 1
      simp only [ite_true, Tape.writeAndMove, Tape.write, Tape.move, Tape.read] at hsim_read_ns ⊢
      split
      · omega
      · dsimp only []
    · -- sim tape cells: preserved
      simp only [ite_true, Tape.writeAndMove, Tape.write, Tape.move, Tape.read] at hsim_read_ns ⊢
      split
      · omega
      · congr 1; rw [readBackWrite_toΓ_eq hsim_read_ns, Function.update_eq_self]
    · -- output: preserved by idle
      exact idle_tape_preserve _ hout_ns hout_h
  | succ d' ih =>
    -- One step: scanSim ⟨d'+1, _⟩ → scanSim ⟨d', _⟩, sim moves right
    have hstep : (extractOutputTM (n := n)).step c = some
      { state := .scanSim ⟨d', by omega⟩
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ
          (if i = utmSimTape then Dir3.right else idleDir (c.work i).read)
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) } := by
      simp only [TM.step, extractOutputTM]
      split
      · next heq => simp [hstate] at heq
      · simp only [hstate, Γw.toΓ, show (d' + 1 : ℕ) ≠ 0 from by omega, dite_false]
        congr 2
    -- Name the intermediate config
    set c' : Cfg 4 (extractOutputTM (n := n)).Q :=
      { state := .scanSim ⟨d', by omega⟩
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read).toΓ
          (if i = utmSimTape then Dir3.right else idleDir (c.work i).read)
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) }
    -- Establish preconditions for IH on c'
    have hsim_read_ns : (c.work utmSimTape).read ≠ Γ.start := hsim_ns _ hsim_h
    -- c'.work utmSimTape.head = c.work utmSimTape.head + 1
    have hc'_sim_head_eq : (c'.work utmSimTape).head = (c.work utmSimTape).head + 1 := by
      simp only [c', ite_true, Tape.writeAndMove, Tape.write, Tape.move, Tape.read] at hsim_read_ns ⊢
      split
      · omega
      · dsimp only []
    have hc'_sim_h : (c'.work utmSimTape).head ≥ 1 := by omega
    have hc'_sim_cells : (c'.work utmSimTape).cells = (c.work utmSimTape).cells := by
      simp only [c', ite_true, Tape.writeAndMove, Tape.write, Tape.move, Tape.read] at hsim_read_ns ⊢
      split
      · omega
      · congr 1; rw [readBackWrite_toΓ_eq hsim_read_ns, Function.update_eq_self]
    have hc'_sim_ns : ∀ j, j ≥ 1 → (c'.work utmSimTape).cells j ≠ Γ.start := by
      rw [hc'_sim_cells]; exact hsim_ns
    have hc'_out : c'.output = c.output := idle_tape_preserve _ hout_ns hout_h
    have hc'_out_h : c'.output.head ≥ 1 := by rw [hc'_out]; exact hout_h
    have hc'_out_ns : c'.output.read ≠ Γ.start := by rw [hc'_out]; exact hout_ns
    have hc'_inp_ns : c'.input.read ≠ Γ.start := by
      simp only [c', Tape.read, Tape.move, idleDir]
      have : c.input.cells c.input.head ≠ Γ.start := hinp_ns
      simp only [this, ↓reduceIte]; exact this
    -- Apply IH
    obtain ⟨c₂, hreach, hc₂_state, hc₂_sim_h, hc₂_sim_cells, hc₂_out⟩ :=
      ih c' (by omega) rfl hc'_sim_h hc'_sim_ns hc'_out_h hc'_out_ns hc'_inp_ns
    refine ⟨c₂, ?_, hc₂_state, ?_, ?_, ?_⟩
    · -- reachesIn composition: 1 step + (d' + 1) steps = d' + 1 + 1 steps
      exact TM.reachesIn.step hstep hreach
    · -- sim head: c'.head + d' + 1 = c.head + (d' + 1) + 1
      rw [hc₂_sim_h, hc'_sim_head_eq]; omega
    · -- sim cells: preserved
      rw [hc₂_sim_cells, hc'_sim_cells]
    · -- output: preserved
      rw [hc₂_out, hc'_out]

/-- HoareTime specification for `extractOutputTM`.

    Parametric in `simCfg`. The postcondition says the real output cell 1
    matches the simulated output cell 1.

    **Pre**: Sim tape encodes `simCfg`; sim tape head at 1; output tape WF;
    simulated output cell 1 is not ▷ (guaranteed by AB model where writes use Γw).
    **Post**: Real output cell 1 = `simCfg.output.cells 1`. -/
theorem extractOutputTM_hoareTime {Q : Type} [Fintype Q] [DecidableEq Q]
    (simCfg : Cfg n Q) (B : ℕ)
    (hout_sym : simCfg.output.cells 1 ≠ Γ.start) :
    (extractOutputTM (n := n)).HoareTime
      (fun inp work out =>
        superCellsCorrect simCfg (work utmSimTape) ∧
        (work utmSimTape).head = 1 ∧
        out.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → out.cells j ≠ Γ.start) ∧
        out.head ≤ B ∧
        inp.read ≠ Γ.start)
      (fun _inp _work out =>
        out.cells 1 = simCfg.output.cells 1)
      (B + extractSkipDist n + 6) := by
  -- Unfold HoareTime and introduce preconditions
  intro inp work out ⟨hscc, hsim_h, hout0, hout_ns, hout_hB, hinp_ns⟩
  -- Derive sim tape properties from superCellsCorrect
  have hsim_ns : ∀ j, j ≥ 1 → (work utmSimTape).cells j ≠ Γ.start :=
    fun j hj => sim_cells_ne_start_of_scc hscc hj
  have hsim_read_ns : (work utmSimTape).read ≠ Γ.start := by
    rw [Tape.read]; exact hsim_ns _ (by omega)
  -- Set up the initial configuration
  set c₀ : Cfg 4 (extractOutputTM (n := n)).Q :=
    { state := extractOutputTM.qstart, input := inp, work := work, output := out }
  -- Phase 1: Rewind output tape (out.head + 1 steps)
  have hc₀_state : c₀.state = .rewindOut := rfl
  obtain ⟨c₁, hreach₁, hc₁_state, hc₁_out_h, hc₁_out_cells, hc₁_sim_h,
    hc₁_sim_cells, hc₁_inp_read, hc₁_inp_head⟩ :=
    rewind_output_phase c₀ out.head hc₀_state rfl hout0 hout_ns
      (by simp [c₀, hsim_h]) hsim_read_ns hinp_ns
  -- Simplify c₀ references in c₁ properties
  change (c₁.work utmSimTape).head = (work utmSimTape).head at hc₁_sim_h
  change (c₁.work utmSimTape).cells = (work utmSimTape).cells at hc₁_sim_cells
  change c₁.output.cells = out.cells at hc₁_out_cells
  -- Derive c₁ properties
  have hc₁_sim_h' : (c₁.work utmSimTape).head = 1 := by rw [hc₁_sim_h, hsim_h]
  have hc₁_sim_h_ge : (c₁.work utmSimTape).head ≥ 1 := by omega
  have hc₁_sim_read_ns : (c₁.work utmSimTape).read ≠ Γ.start := by
    rw [Tape.read, hc₁_sim_cells]; exact hsim_ns _ (by omega)
  have hc₁_out_ns : ∀ j, j ≥ 1 → c₁.output.cells j ≠ Γ.start := by
    rw [hc₁_out_cells]; exact hout_ns
  have hc₁_out_read_ns : c₁.output.read ≠ Γ.start := by
    rw [Tape.read, hc₁_out_cells]; exact hout_ns _ (by omega)
  have hc₁_inp_ns : c₁.input.read ≠ Γ.start := by rw [hc₁_inp_read]; exact hinp_ns
  -- Phase 2: rightOut → scanSim (1 step)
  have hstep₂ : (extractOutputTM (n := n)).step c₁ = some
    { state := .scanSim ⟨extractSkipDist n, by omega⟩
      input := c₁.input.move (idleDir c₁.input.read)
      work := fun i => (c₁.work i).writeAndMove (readBackWrite (c₁.work i).read).toΓ
        (if i = utmSimTape then Dir3.right else idleDir (c₁.work i).read)
      output := c₁.output.writeAndMove (readBackWrite c₁.output.read).toΓ
        (idleDir c₁.output.read) } := by
    simp only [TM.step, extractOutputTM]
    split
    · next heq => simp [hc₁_state] at heq
    · simp only [hc₁_state]
  -- Name the config after the rightOut step
  set c₂ : Cfg 4 (extractOutputTM (n := n)).Q :=
    { state := .scanSim ⟨extractSkipDist n, by omega⟩
      input := c₁.input.move (idleDir c₁.input.read)
      work := fun i => (c₁.work i).writeAndMove (readBackWrite (c₁.work i).read).toΓ
        (if i = utmSimTape then Dir3.right else idleDir (c₁.work i).read)
      output := c₁.output.writeAndMove (readBackWrite c₁.output.read).toΓ
        (idleDir c₁.output.read) }
  -- Establish c₂ properties
  -- c₂.output = c₁.output (idle operation)
  have hc₂_out : c₂.output = c₁.output := idle_tape_preserve _ hc₁_out_read_ns (by omega)
  -- c₂.work utmSimTape: head advances by 1, cells preserved
  have hc₂_sim_head : (c₂.work utmSimTape).head = (c₁.work utmSimTape).head + 1 := by
    show ((c₁.work utmSimTape).writeAndMove _ _).head = _
    simp only [ite_true, Tape.writeAndMove, Tape.write, Tape.move, Tape.read]
    split
    · omega
    · dsimp only []
  have hc₂_sim_cells : (c₂.work utmSimTape).cells = (c₁.work utmSimTape).cells := by
    show ((c₁.work utmSimTape).writeAndMove _ _).cells = _
    simp only [ite_true, Tape.writeAndMove, Tape.write, Tape.move, Tape.read] at hc₁_sim_read_ns ⊢
    split
    · omega
    · congr 1; rw [readBackWrite_toΓ_eq hc₁_sim_read_ns, Function.update_eq_self]
  have hc₂_sim_h_ge : (c₂.work utmSimTape).head ≥ 1 := by omega
  have hc₂_sim_ns : ∀ j, j ≥ 1 → (c₂.work utmSimTape).cells j ≠ Γ.start := by
    rw [hc₂_sim_cells, hc₁_sim_cells]; exact hsim_ns
  have hc₂_out_h : c₂.output.head ≥ 1 := by rw [hc₂_out]; omega
  have hc₂_out_read_ns : c₂.output.read ≠ Γ.start := by rw [hc₂_out]; exact hc₁_out_read_ns
  have hc₂_inp_ns : c₂.input.read ≠ Γ.start := by
    show (c₁.input.move (idleDir c₁.input.read)).read ≠ _
    rw [input_idle_preserve _ hc₁_inp_ns]; exact hc₁_inp_ns
  -- Phase 3: scanSim loop (extractSkipDist n + 1 steps)
  obtain ⟨c₃, hreach₃, hc₃_state, hc₃_sim_h, hc₃_sim_cells, hc₃_out⟩ :=
    scanSim_phase c₂ (extractSkipDist n) (by omega) rfl
      hc₂_sim_h_ge hc₂_sim_ns hc₂_out_h hc₂_out_read_ns hc₂_inp_ns
  -- Compute c₃ sim tape head position
  -- c₃.work utmSimTape.head = 2 + extractSkipDist n + 1 = extractSkipDist n + 3
  have hc₃_sim_h_val : (c₃.work utmSimTape).head = extractSkipDist n + 3 := by
    rw [hc₃_sim_h, hc₂_sim_head, hc₁_sim_h']; omega
  -- The sim tape cells are the original work tape cells
  have hc₃_sim_cells_orig : (c₃.work utmSimTape).cells = (work utmSimTape).cells := by
    rw [hc₃_sim_cells, hc₂_sim_cells, hc₁_sim_cells]
  -- Key: extractSkipDist n + 3 = simTapeOffset (n+2) 1 (n+1) + 1
  -- simTapeOffset (n+2) 1 (n+1) = 1 + 1 * width(n+2) + 3*(n+1) = 1 + 3*(n+2) + 3*(n+1)
  -- extractSkipDist n = 3*(n+2) + 3*(n+1) - 1
  -- extractSkipDist n + 3 = 3*(n+2) + 3*(n+1) + 2 = (1 + 3*(n+2) + 3*(n+1)) + 1
  have hbase_eq : SuperCell.simTapeOffset (n + 2) 1 (n + 1) = extractSkipDist n + 2 := by
    simp only [SuperCell.simTapeOffset, SuperCell.width, extractSkipDist]
    omega
  -- Get the output tape's super-cell correctness
  have hscc_out := hscc.2.2.2
  have hscc_out1 := hscc_out 1
  -- Extract the hi and lo values from the super-cell encoding
  set outSym := simCfg.output.cells 1 with hOutSym_def
  set hiLo := SuperCell.symToCellPair outSym
  have hscc_out1' : simTapeCellCorrect (n + 2) (n + 1) 1
      simCfg.output.head outSym (work utmSimTape) := hscc_out1
  -- The hi bit is at base + 1 = extractSkipDist n + 3
  have hhi_cell : (work utmSimTape).cells (extractSkipDist n + 3) = hiLo.1 := by
    have h := hscc_out1'.2.1
    have hoff : SuperCell.simTapeOffset (n + 2) 1 (n + 1) + 1 = extractSkipDist n + 3 := by
      rw [hbase_eq]
    rw [hoff] at h; exact h
  -- The lo bit is at base + 2 = extractSkipDist n + 4
  have hlo_cell : (work utmSimTape).cells (extractSkipDist n + 4) = hiLo.2 := by
    have h := hscc_out1'.2.2
    have hoff : SuperCell.simTapeOffset (n + 2) 1 (n + 1) + 2 = extractSkipDist n + 4 := by
      rw [hbase_eq]
    rw [hoff] at h; exact h
  -- c₃.work utmSimTape reads the hi bit
  have hc₃_read : (c₃.work utmSimTape).read = hiLo.1 := by
    rw [Tape.read, hc₃_sim_cells_orig, hc₃_sim_h_val, hhi_cell]
  -- c₃ sim read ≠ start (hi bit of any non-start symbol is not start)
  have hc₃_sim_ns' : ∀ j, j ≥ 1 → (c₃.work utmSimTape).cells j ≠ Γ.start := by
    rw [hc₃_sim_cells_orig]; exact hsim_ns
  have hc₃_sim_read_ns : (c₃.work utmSimTape).read ≠ Γ.start :=
    hc₃_sim_ns' _ (by omega)
  -- c₃ output properties (carried through from c₁)
  have hc₃_out_eq : c₃.output = c₁.output := by rw [hc₃_out, hc₂_out]
  have hc₃_out_h : c₃.output.head ≥ 1 := by rw [hc₃_out_eq]; omega
  have hc₃_out_read_ns : c₃.output.read ≠ Γ.start := by
    rw [hc₃_out_eq]; exact hc₁_out_read_ns
  -- Phase 4: readHi → readLo (1 step)
  -- The machine reads c₃.work utmSimTape.read = hiLo.1 and goes to readLo(hiLo.1)
  have hstep₄ : (extractOutputTM (n := n)).step c₃ = some
    { state := .readLo (c₃.work utmSimTape).read
      input := c₃.input.move (idleDir c₃.input.read)
      work := fun i => (c₃.work i).writeAndMove (readBackWrite (c₃.work i).read).toΓ
        (if i = utmSimTape then Dir3.right else idleDir (c₃.work i).read)
      output := c₃.output.writeAndMove (readBackWrite c₃.output.read).toΓ
        (idleDir c₃.output.read) } := by
    simp only [TM.step, extractOutputTM]
    split
    · next heq => simp [hc₃_state] at heq
    · simp only [hc₃_state]
  -- Name the config after readHi
  set c₄ : Cfg 4 (extractOutputTM (n := n)).Q :=
    { state := .readLo (c₃.work utmSimTape).read
      input := c₃.input.move (idleDir c₃.input.read)
      work := fun i => (c₃.work i).writeAndMove (readBackWrite (c₃.work i).read).toΓ
        (if i = utmSimTape then Dir3.right else idleDir (c₃.work i).read)
      output := c₃.output.writeAndMove (readBackWrite c₃.output.read).toΓ
        (idleDir c₃.output.read) }
  -- c₄ properties
  have hc₄_out : c₄.output = c₃.output := idle_tape_preserve _ hc₃_out_read_ns hc₃_out_h
  -- c₄ sim tape: head advances, cells preserved
  have hc₄_sim_head : (c₄.work utmSimTape).head = (c₃.work utmSimTape).head + 1 := by
    show ((c₃.work utmSimTape).writeAndMove _ _).head = _
    simp only [ite_true, Tape.writeAndMove, Tape.write, Tape.move, Tape.read] at hc₃_sim_read_ns ⊢
    split
    · omega
    · dsimp only []
  have hc₄_sim_cells : (c₄.work utmSimTape).cells = (c₃.work utmSimTape).cells := by
    show ((c₃.work utmSimTape).writeAndMove _ _).cells = _
    simp only [ite_true, Tape.writeAndMove, Tape.write, Tape.move, Tape.read] at hc₃_sim_read_ns ⊢
    split
    · omega
    · congr 1; rw [readBackWrite_toΓ_eq hc₃_sim_read_ns, Function.update_eq_self]
  -- c₄ sim tape reads the lo bit
  have hc₄_sim_h_val : (c₄.work utmSimTape).head = extractSkipDist n + 4 := by
    rw [hc₄_sim_head, hc₃_sim_h_val]
  have hc₄_read : (c₄.work utmSimTape).read = hiLo.2 := by
    rw [Tape.read, hc₄_sim_cells, hc₃_sim_cells_orig, hc₄_sim_h_val, hlo_cell]
  -- c₄ state has hi = hiLo.1
  have hc₄_state : c₄.state = .readLo hiLo.1 := by
    show ExtractOutputQ.readLo (c₃.work utmSimTape).read = .readLo hiLo.1
    rw [hc₃_read]
  -- Phase 5: readLo → writeOut (1 step)
  have hstep₅ : (extractOutputTM (n := n)).step c₄ = some
    { state := .writeOut hiLo.1 (c₄.work utmSimTape).read
      input := c₄.input.move (idleDir c₄.input.read)
      work := fun i => (c₄.work i).writeAndMove (readBackWrite (c₄.work i).read).toΓ
        (idleDir (c₄.work i).read)
      output := c₄.output.writeAndMove (readBackWrite c₄.output.read).toΓ
        (idleDir c₄.output.read) } := by
    simp only [TM.step, extractOutputTM]
    split
    · next heq => simp [hc₄_state] at heq
    · simp only [hc₄_state]
  -- Name the config after readLo
  set c₅ : Cfg 4 (extractOutputTM (n := n)).Q :=
    { state := .writeOut hiLo.1 (c₄.work utmSimTape).read
      input := c₄.input.move (idleDir c₄.input.read)
      work := fun i => (c₄.work i).writeAndMove (readBackWrite (c₄.work i).read).toΓ
        (idleDir (c₄.work i).read)
      output := c₄.output.writeAndMove (readBackWrite c₄.output.read).toΓ
        (idleDir c₄.output.read) }
  -- c₅ state: writeOut hiLo.1 hiLo.2
  have hc₅_state : c₅.state = .writeOut hiLo.1 hiLo.2 := by
    show ExtractOutputQ.writeOut hiLo.1 (c₄.work utmSimTape).read = _
    rw [hc₄_read]
  -- c₅ output = c₄.output (idle)
  have hc₅_out : c₅.output = c₄.output := by
    show c₄.output.writeAndMove _ _ = c₄.output
    rw [hc₄_out, hc₃_out_eq]
    exact idle_tape_preserve _ hc₁_out_read_ns (by omega)
  -- Phase 6: writeOut → done (1 step)
  -- The decoded symbol from (hiLo.1, hiLo.2) is written to the output tape
  -- The machine computes: match hiLo.1, hiLo.2 with ...
  -- For outSym:
  --   zero → (zero,zero) → match zero,zero → Γw.zero → Γ.zero
  --   one  → (zero,one)  → match zero,one  → Γw.one  → Γ.one
  --   blank→ (blank,blank)→ match blank,blank→ Γw.blank→ Γ.blank
  --   start→ impossible (hout_sym)
  have hstep₆ : (extractOutputTM (n := n)).step c₅ = some
    { state := .done
      input := c₅.input.move (idleDir c₅.input.read)
      work := fun i => (c₅.work i).writeAndMove (readBackWrite (c₅.work i).read).toΓ
        (idleDir (c₅.work i).read)
      output := c₅.output.writeAndMove
        (match hiLo.1, hiLo.2 with
          | .zero, .zero => Γw.zero
          | .zero, .one => Γw.one
          | .blank, .blank => Γw.blank
          | _, _ => Γw.blank).toΓ
        (idleDir c₅.output.read) } := by
    simp only [TM.step, extractOutputTM]
    split
    · next heq => simp [hc₅_state] at heq
    · simp only [hc₅_state]
  -- Name the final config
  set c₆ : Cfg 4 (extractOutputTM (n := n)).Q :=
    { state := .done
      input := c₅.input.move (idleDir c₅.input.read)
      work := fun i => (c₅.work i).writeAndMove (readBackWrite (c₅.work i).read).toΓ
        (idleDir (c₅.work i).read)
      output := c₅.output.writeAndMove
        (match hiLo.1, hiLo.2 with
          | .zero, .zero => Γw.zero
          | .zero, .one => Γw.one
          | .blank, .blank => Γw.blank
          | _, _ => Γw.blank).toΓ
        (idleDir c₅.output.read) }
  -- c₆ is halted
  have hc₆_halted : (extractOutputTM (n := n)).halted c₆ := by
    show c₆.state = ExtractOutputQ.done; rfl
  -- The decoded symbol written to output matches outSym
  -- c₅.output = c₁.output, which has head = 1 and cells = out.cells
  -- So c₅.output.head = 1, and write goes to cell 1
  have hc₅_out_eq : c₅.output = c₁.output := by
    rw [hc₅_out, hc₄_out, hc₃_out_eq]
  have hc₅_out_h : c₅.output.head = 1 := by rw [hc₅_out_eq]; exact hc₁_out_h
  -- The write value: match hiLo.1 hiLo.2 gives back outSym
  -- For each case of outSym:
  have hwrite_val : (match hiLo.1, hiLo.2 with
      | .zero, .zero => Γw.zero
      | .zero, .one => Γw.one
      | .blank, .blank => Γw.blank
      | _, _ => Γw.blank).toΓ = outSym := by
    have hHiLo : hiLo = SuperCell.symToCellPair (simCfg.output.cells 1) := rfl
    cases h : simCfg.output.cells 1 <;>
      simp_all [SuperCell.symToCellPair, Γw.toΓ]
  -- c₆.output.cells 1 = outSym
  have hc₆_out_cells1 : c₆.output.cells 1 = outSym := by
    -- c₆.output = c₅.output.writeAndMove(write_val)(idleDir c₅.output.read)
    -- c₅.output.head = 1, so write goes to cell 1
    -- idleDir c₅.output.read = stay (since c₅.output reads cell 1 which is not start)
    -- After write: cells 1 = write_val = outSym
    show (c₅.output.writeAndMove _ _).cells 1 = outSym
    simp only [Tape.writeAndMove, Tape.write, hc₅_out_h, Tape.move]
    -- head ≠ 0 at position 1
    simp only [show (1 : ℕ) ≠ 0 from by omega, ↓reduceIte]
    -- idleDir for output: c₅.output.read ≠ start
    have hc₅_out_read_ns : c₅.output.read ≠ Γ.start := by
      rw [hc₅_out_eq]; exact hc₁_out_read_ns
    simp only [idleDir, hc₅_out_read_ns, ↓reduceIte]
    -- After stay, cells are updated at position 1
    simp only [Function.update_self, hwrite_val]
  -- Compose all reachesIn chains
  -- Total steps: (out.head + 1) + 1 + (extractSkipDist n + 1) + 1 + 1 + 1
  --            = out.head + extractSkipDist n + 6
  -- Bound: out.head + extractSkipDist n + 6 ≤ B + extractSkipDist n + 6
  have hreach_total : (extractOutputTM (n := n)).reachesIn
      (out.head + extractSkipDist n + 6) c₀ c₆ := by
    -- c₀ →[out.head + 1] c₁ →[1] c₂ →[extractSkipDist n + 1] c₃ →[1] c₄ →[1] c₅ →[1] c₆
    have h₁₂ : (extractOutputTM (n := n)).reachesIn 1 c₁ c₂ :=
      TM.reachesIn.step hstep₂ .zero
    have h₂₃ := hreach₃
    have h₃₄ : (extractOutputTM (n := n)).reachesIn 1 c₃ c₄ :=
      TM.reachesIn.step hstep₄ .zero
    have h₄₅ : (extractOutputTM (n := n)).reachesIn 1 c₄ c₅ :=
      TM.reachesIn.step hstep₅ .zero
    have h₅₆ : (extractOutputTM (n := n)).reachesIn 1 c₅ c₆ :=
      TM.reachesIn.step hstep₆ .zero
    -- Compose: use reachesIn_trans
    have hc₀₆ := TM.reachesIn_trans _ hreach₁ (TM.reachesIn_trans _ h₁₂
      (TM.reachesIn_trans _ h₂₃ (TM.reachesIn_trans _ h₃₄
        (TM.reachesIn_trans _ h₄₅ h₅₆))))
    convert hc₀₆ using 1; omega
  exact ⟨c₆, _, by omega, hreach_total, hc₆_halted, hc₆_out_cells1⟩

end TM
