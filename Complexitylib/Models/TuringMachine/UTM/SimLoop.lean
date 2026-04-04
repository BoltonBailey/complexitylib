import Complexitylib.Models.TuringMachine.UTM.Machine
import Complexitylib.Models.TuringMachine.Hoare
import Complexitylib.Models.TuringMachine.UTM.SimConfig.Defs
import Complexitylib.Models.TuringMachine.UTM.Init
import Complexitylib.Models.TuringMachine.UTM.ReadCurrentInternal
import Complexitylib.Models.TuringMachine.UTM.LookupInternal
import Complexitylib.Models.TuringMachine.UTM.ApplyTransitionInternal
import Complexitylib.Models.TuringMachine.UTM.CheckHaltInternal
import Complexitylib.Models.TuringMachine.UTM.ExtractOutput
import Complexitylib.Models.TuringMachine.Combinators.LoopInternal
import Complexitylib.Models.TuringMachine.Combinators.SeqInternal
import Complexitylib.Models.TuringMachine.Internal

/-!
# UTM Simulation Loop — Composition Proof

Composes the sub-machine Hoare specs into a proof that the UTM correctly
simulates any TM. The proof proceeds in three phases:

1. **Init**: `initTM` sets up work tapes encoding `tm.initCfg x`
2. **Loop**: By induction on remaining simulation steps, each iteration
   chains readCurrent → lookup → applyTransition → checkHalt
3. **Extract**: `extractOutputTM` copies the simulated output
-/

set_option maxHeartbeats 400000

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Helpers
-- ════════════════════════════════════════════════════════════════════════

/-- A halted config can only reach itself in 0 steps. -/
private theorem reachesIn_zero_of_halted {tm : TM n} {t : ℕ}
    {c c' : Cfg n tm.Q} (hh : tm.halted c) (hr : tm.reachesIn t c c') :
    t = 0 ∧ c' = c := by
  cases hr with
  | zero => exact ⟨rfl, rfl⟩
  | step hs _ => simp [step, hh] at hs

/-- Step determinism: if `step c = some a` and `step c = some b`, then `a = b`. -/
private theorem step_det {tm : TM n} {c a b : Cfg n tm.Q}
    (ha : tm.step c = some a) (hb : tm.step c = some b) : a = b := by
  rw [ha] at hb; exact Option.some.inj hb

-- ════════════════════════════════════════════════════════════════════════
-- The simulation loop invariant (full version for composition)
-- ════════════════════════════════════════════════════════════════════════

/-- Full loop invariant: UTM tapes encode a simulated config with all
    conditions needed by the sub-machine preconditions. -/
structure LoopInv (tm : TM n) (k : ℕ) (hk : k = @Fintype.card tm.Q tm.finQ)
    (desc : List Bool) (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (simCfg : Cfg n tm.Q) : Prop where
  hNotHalted : simCfg.state ≠ tm.qhalt
  hdesc : descOnTape desc (work utmDescTape)
  hstate : stateOnTapeAt k (tm.stateEquivK hk simCfg.state) (work utmStateTape)
  hsim : superCellsCorrect simCfg (work utmSimTape)
  hheads : ∀ i, (work i).head = 1
  hwf : WorkTapesWF work
  hscratch_inp_blank :
    (work utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank
  hscratch_out_blank :
    (work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank
  hinp_c0 : inp.cells 0 = Γ.start
  hinp_ns : ∀ j, j ≥ 1 → inp.cells j ≠ Γ.start
  hinp_h : inp.head ≥ 1
  hout_c0 : out.cells 0 = Γ.start
  hout_ns : ∀ j, j ≥ 1 → out.cells j ≠ Γ.start
  hout_h : out.head ≥ 1

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: One iteration of the simulation loop
-- ════════════════════════════════════════════════════════════════════════

/-- The body machine (readCurrent ; lookup ; applyTransition) advances the
    simulation by one step. Produces `reachesIn` at the `utmSimStepTM` level. -/
private theorem utm_body_step (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (desc : List Bool) (hdesc_eq : desc = TMEncoding.encodeTM tm)
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (simCfg : Cfg n tm.Q)
    (hinv : LoopInv tm k hk desc inp work out simCfg) :
    let e := tm.stateEquivK hk
    let iHead := simCfg.input.read
    let wHeads := fun i => (simCfg.work i).read
    let oHead := simCfg.output.read
    let (q', wW, oW, iD, wD, oD) := tm.δ simCfg.state iHead wHeads oHead
    let simCfg' : Cfg n tm.Q :=
      ⟨q', simCfg.input.move iD,
       fun i => (simCfg.work i).writeAndMove (wW i).toΓ (wD i),
       simCfg.output.writeAndMove oW.toΓ oD⟩
    ∃ c' t,
      (utmSimStepTM (n := n) k).reachesIn t
        ⟨(utmSimStepTM (n := n) k).qstart, inp, work, out⟩ c' ∧
      (utmSimStepTM (n := n) k).halted c' ∧
      stateOnTapeAt k (e q') (c'.work utmStateTape) ∧
      superCellsCorrect simCfg' (c'.work utmSimTape) ∧
      descOnTape desc (c'.work utmDescTape) ∧
      (∀ i, (c'.work i).head = 1) ∧
      WorkTapesWF c'.work ∧
      (c'.work utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
      (c'.work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank ∧
      c'.input.read ≠ Γ.start ∧ c'.input.head ≥ 1 ∧
      c'.output.read ≠ Γ.start ∧ c'.output.head ≥ 1 := by
  intro e iHead wHeads oHead
  set δr := tm.δ simCfg.state iHead wHeads oHead with hδ_def
  obtain ⟨q', wW, oW, iD, wD, oD⟩ := δr
  dsimp only
  -- Step 1: Invoke readCurrentTM_hoareTime'
  obtain ⟨B_rc, hrc⟩ := readCurrentTM_hoareTime' tm k hk desc simCfg
  -- Build readCurrent precondition from LoopInv
  have hrc_pre : descOnTape desc (work utmDescTape) ∧
      stateOnTapeAt k ((tm.stateEquivK hk) simCfg.state) (work utmStateTape) ∧
      superCellsCorrect simCfg (work utmSimTape) ∧
      (work utmDescTape).head = 1 ∧
      (work utmStateTape).head = 1 ∧
      (work utmSimTape).head = 1 ∧
      (work utmScratchTape).head = 1 ∧
      (work utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
      (work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank ∧
      WorkTapesWF work ∧
      inp.read ≠ Γ.start ∧ inp.head ≥ 1 ∧
      out.read ≠ Γ.start ∧ out.head ≥ 1 := by
    refine ⟨hinv.hdesc, hinv.hstate, hinv.hsim, ?_, ?_, ?_, ?_,
            hinv.hscratch_inp_blank, hinv.hscratch_out_blank, hinv.hwf, ?_, hinv.hinp_h, ?_, hinv.hout_h⟩
    · exact hinv.hheads utmDescTape
    · exact hinv.hheads utmStateTape
    · exact hinv.hheads utmSimTape
    · exact hinv.hheads utmScratchTape
    · simp only [Tape.read]; exact hinv.hinp_ns _ hinv.hinp_h
    · simp only [Tape.read]; exact hinv.hout_ns _ hinv.hout_h
  -- Apply HoareTime to get readCurrent result
  obtain ⟨c_rc, t_rc, ht_rc_le, hreach_rc, hhalt_rc, hpost_rc⟩ := hrc inp work out hrc_pre
  -- Destructure readCurrent postcondition
  obtain ⟨hrc_desc, hrc_state, hrc_sim, hrc_scratch, hrc_out_blank, hrc_dh, hrc_sth,
          hrc_simh, hrc_wf, hrc_wheads, hrc_inp_read, hrc_inp_head, hrc_out_read, hrc_out_head⟩ := hpost_rc
  -- Step 2: Invoke lookupTM_hoareTime_proof
  obtain ⟨B_lu, hlu⟩ := lookupTM_hoareTime_proof tm k hk hdesc_eq simCfg
    (e simCfg.state) simCfg.input.read (fun i => (simCfg.work i).read) simCfg.output.read
  -- Build lookup precondition from readCurrent postcondition
  have hlu_pre : descOnTape desc (c_rc.work utmDescTape) ∧
      (c_rc.work utmDescTape).head = 1 ∧
      (∀ (i : Fin 4), (c_rc.work i).head ≥ 1) ∧
      scratchHasInputPattern k n (e simCfg.state) simCfg.input.read
        (fun i => (simCfg.work i).read) simCfg.output.read (c_rc.work utmScratchTape) ∧
      (c_rc.work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank ∧
      WorkTapesWF c_rc.work ∧
      c_rc.input.read ≠ Γ.start ∧ c_rc.input.head ≥ 1 ∧
      c_rc.output.read ≠ Γ.start ∧ c_rc.output.head ≥ 1 ∧
      stateOnTapeAt k (e simCfg.state) (c_rc.work utmStateTape) ∧
      superCellsCorrect simCfg (c_rc.work utmSimTape) ∧
      (c_rc.work utmStateTape).head = 1 ∧ (c_rc.work utmSimTape).head = 1 :=
    ⟨hrc_desc, hrc_dh, hrc_wheads,
     hrc_scratch, hrc_out_blank, hrc_wf,
     hrc_inp_read, hrc_inp_head, hrc_out_read, hrc_out_head,
     hrc_state, hrc_sim, hrc_sth, hrc_simh⟩
  -- Apply lookup HoareTime
  obtain ⟨c_lu, t_lu, ht_lu_le, hreach_lu, hhalt_lu, hpost_lu⟩ :=
    hlu c_rc.input c_rc.work c_rc.output hlu_pre
  -- The lookup postcondition has a match on tm.δ (e.symm (e simCfg.state)) ...
  -- Since e.symm (e _) = _, this reduces to our hδ_def
  have hsymm : (tm.stateEquivK hk).symm (e simCfg.state) = simCfg.state :=
    Equiv.symm_apply_apply _ _
  rw [hsymm] at hpost_lu
  -- Now hpost_lu has match on tm.δ simCfg.state iHead wHeads oHead
  -- which equals (q', wW, oW, iD, wD, oD) by hδ_def
  rw [← hδ_def] at hpost_lu
  dsimp only at hpost_lu
  -- Destructure lookup postcondition
  obtain ⟨hlu_desc, hlu_scratch, hlu_dh, hlu_sch, hlu_wf, hlu_state, hlu_sim,
          hlu_sth, hlu_simh, hlu_wheads, hlu_inp_read, hlu_inp_head, hlu_out_read, hlu_out_head⟩ := hpost_lu
  -- Step 3: Invoke applyTransitionTM_hoare_proof
  have hat := applyTransitionTM_hoare_proof (tm := tm) k hk desc simCfg hinv.hNotHalted
  -- hat has `let e := ...; let iHead := ...; ... match tm.δ simCfg.state iHead wHeads oHead`
  -- We need to reduce those lets and the match to get at the Hoare spec
  -- First intro the let binders, then rewrite the match
  dsimp only [] at hat
  -- hat still has a match. Use show/change to specify the type after match reduction:
  -- Since tm.δ simCfg.state iHead wHeads oHead = (q', wW, oW, iD, wD, oD) by hδ_def (reversed),
  -- and the `set δr = ...` already gives hδ_def, we can use conv + simp
  have hδ_eq : tm.δ simCfg.state simCfg.input.read (fun i => (simCfg.work i).read) simCfg.output.read =
    (q', wW, oW, iD, wD, oD) := hδ_def.symm
  rw [show iHead = simCfg.input.read from rfl,
      show wHeads = fun i => (simCfg.work i).read from rfl,
      show oHead = simCfg.output.read from rfl] at hδ_def
  simp only [hδ_eq] at hat
  -- Build applyTransition precondition from lookup postcondition
  have hat_pre : stateOnTapeAt k ((tm.stateEquivK hk) simCfg.state) (c_lu.work utmStateTape) ∧
      superCellsCorrect simCfg (c_lu.work utmSimTape) ∧
      scratchHasTransOutput k n ((tm.stateEquivK hk) q') wW oW iD wD oD (c_lu.work utmScratchTape) ∧
      descOnTape desc (c_lu.work utmDescTape) ∧
      WorkTapesWF c_lu.work ∧
      (c_lu.work utmStateTape).head = 1 ∧
      (c_lu.work utmSimTape).head = 1 ∧
      (c_lu.work utmDescTape).head = 1 ∧
      c_lu.input.read ≠ Γ.start ∧ c_lu.input.head ≥ 1 ∧
      c_lu.output.read ≠ Γ.start ∧ c_lu.output.head ≥ 1 :=
    ⟨hlu_state, hlu_sim, hlu_scratch, hlu_desc, hlu_wf, hlu_sth, hlu_simh, hlu_dh,
     hlu_inp_read, hlu_inp_head, hlu_out_read, hlu_out_head⟩
  -- Apply Hoare to get applyTransition result
  obtain ⟨c_at, hreach_at, hhalt_at, hpost_at⟩ := hat c_lu.input c_lu.work c_lu.output hat_pre
  -- Convert reaches to reachesIn
  obtain ⟨t_at, hreachIn_at⟩ := reaches_to_reachesIn _ hreach_at
  -- Destructure hpost_at for later use
  obtain ⟨hat_state, hat_sim, hat_desc, hat_wheads, hat_wf,
          hat_inp_read, hat_inp_head, hat_out_read, hat_out_head,
          hat_scr_inp, hat_scr_out⟩ := hpost_at
  -- ═════ Compose inner seq: lookupTM ; applyTransitionTM ═════
  -- Need: transition tapes are identity for lookup → applyTransition
  have hlu_halt_state : c_lu.state = (lookupTM (n := n) k).qhalt := hhalt_lu
  -- seqTransitionInput is identity for c_lu.input (read ≠ start)
  have hlu_inp_id : seqTransitionInput c_lu.input = c_lu.input :=
    seqTransitionInput_id hlu_inp_read
  -- seqTransitionTape is identity for all work tapes (WF + heads ≥ 1)
  have hlu_work_id : (fun i => seqTransitionTape (c_lu.work i)) = c_lu.work :=
    seqTransition_work_id hlu_wf hlu_wheads
  -- seqTransitionTape is identity for output tape
  have hlu_out_id : seqTransitionTape c_lu.output = c_lu.output :=
    seqTransitionTape_id hlu_out_read hlu_out_head
  -- Build the inner reachesIn for applyTransitionTM starting from seq-transition of c_lu
  have hreachIn_at' : (applyTransitionTM (n := n) k).reachesIn t_at
      { state := (applyTransitionTM (n := n) k).qstart,
        input := seqTransitionInput c_lu.input,
        work := fun i => seqTransitionTape (c_lu.work i),
        output := seqTransitionTape c_lu.output } c_at := by
    rw [hlu_inp_id, hlu_work_id, hlu_out_id]; exact hreachIn_at
  -- Inner seq composition: lookupTM ; applyTransitionTM
  have h_inner := seqTM_full_simulation (lookupTM (n := n) k) (applyTransitionTM (n := n) k)
    hreach_lu hlu_halt_state hreachIn_at'
  -- ═════ Compose outer seq: readCurrentTM ; (lookupTM ; applyTransitionTM) ═════
  -- Need: transition tapes are identity for c_rc
  have hrc_halt_state : c_rc.state = readCurrentTM.qhalt := hhalt_rc
  have hrc_inp_id : seqTransitionInput c_rc.input = c_rc.input :=
    seqTransitionInput_id hrc_inp_read
  have hrc_work_id : (fun i => seqTransitionTape (c_rc.work i)) = c_rc.work :=
    seqTransition_work_id hrc_wf hrc_wheads
  have hrc_out_id : seqTransitionTape c_rc.output = c_rc.output :=
    seqTransitionTape_id hrc_out_read hrc_out_head
  -- The inner composition starts from phase1Wrap of {lookupTM.qstart, c_rc.input, c_rc.work, c_rc.output}
  -- which is the same as {seqTransitionInput c_rc.input, ...} after identity rewrites
  -- We need to rewrite h_inner to use seqTransition forms
  have h_inner' : (seqTM (lookupTM (n := n) k) (applyTransitionTM (n := n) k)).reachesIn (t_lu + 1 + t_at)
      { state := (seqTM (lookupTM (n := n) k) (applyTransitionTM (n := n) k)).qstart,
        input := seqTransitionInput c_rc.input,
        work := fun i => seqTransitionTape (c_rc.work i),
        output := seqTransitionTape c_rc.output }
      (phase2Wrap (lookupTM (n := n) k) (applyTransitionTM (n := n) k) c_at) := by
    rw [hrc_inp_id, hrc_work_id, hrc_out_id]
    exact h_inner
  -- Outer composition
  have h_outer := seqTM_full_simulation readCurrentTM
    (seqTM (lookupTM (n := n) k) (applyTransitionTM (n := n) k))
    hreach_rc hrc_halt_state h_inner'
  -- The result is at the utmSimStepTM level, since utmSimStepTM = seqTM readCurrentTM (seqTM lookupTM applyTransitionTM)
  -- phase1Wrap readCurrentTM (seqTM lookupTM applyTransitionTM) {qstart, inp, work, out}
  --   = {Sum.inl readCurrentTM.qstart, inp, work, out}
  --   = {(utmSimStepTM k).qstart, inp, work, out}
  -- Unfold: the final config from h_outer
  set c_final := phase2Wrap readCurrentTM (seqTM (lookupTM (n := n) k) (applyTransitionTM (n := n) k))
    (phase2Wrap (lookupTM (n := n) k) (applyTransitionTM (n := n) k) c_at) with hc_final_def
  -- Show the starting config matches
  have hstart_eq : phase1Wrap readCurrentTM (seqTM (lookupTM (n := n) k) (applyTransitionTM (n := n) k))
      { state := readCurrentTM.qstart, input := inp, work := work, output := out } =
      { state := (utmSimStepTM (n := n) k).qstart, input := inp, work := work, output := out } := by
    simp [phase1Wrap, utmSimStepTM, seqTM]
  -- Rewrite h_outer to use utmSimStepTM start config
  rw [hstart_eq] at h_outer
  -- Show c_final is halted at utmSimStepTM level
  have hfinal_halted : (utmSimStepTM (n := n) k).halted c_final := by
    simp only [hc_final_def, utmSimStepTM]
    rw [phase2Wrap_halted]
    rw [phase2Wrap_halted]
    exact hhalt_at
  -- Show c_final has the same work/input/output as c_at (phase2Wrap preserves fields)
  have hfinal_work : c_final.work = c_at.work := by
    simp [hc_final_def, phase2Wrap]
  have hfinal_input : c_final.input = c_at.input := by
    simp [hc_final_def, phase2Wrap]
  have hfinal_output : c_final.output = c_at.output := by
    simp [hc_final_def, phase2Wrap]
  -- Witness the existentials
  refine ⟨c_final, t_rc + 1 + (t_lu + 1 + t_at), ?_, hfinal_halted, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- h_outer gives the reachesIn, but we need utmSimStepTM not seqTM
  · exact h_outer
  · rw [hfinal_work]; exact hat_state
  · rw [hfinal_work]; exact hat_sim
  · rw [hfinal_work]; exact hat_desc
  · intro i; rw [hfinal_work]; exact hat_wheads i
  · rw [hfinal_work]; exact hat_wf
  · rw [hfinal_work]; exact hat_scr_inp
  · rw [hfinal_work]; exact hat_scr_out
  · rw [hfinal_input]; exact hat_inp_read
  · rw [hfinal_input]; exact hat_inp_head
  · rw [hfinal_output]; exact hat_out_read
  · rw [hfinal_output]; exact hat_out_head

/-- One iteration of the simulation loop advances the simulated config by
    one step and either halts (if the new config is halted) or continues
    with the updated invariant. Returns `reachesIn` at the `loopTM` level. -/
private theorem utm_one_iteration (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (desc : List Bool) (hdesc_eq : desc = TMEncoding.encodeTM tm)
    (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (simCfg : Cfg n tm.Q)
    (hinv : LoopInv tm k hk desc inp work out simCfg) :
    -- Either the loop halts (simulated TM stepped to qhalt)
    (∃ c' t,
      (loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).reachesIn t
        ⟨(loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).qstart,
         inp, work, out⟩ c' ∧
      (loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).halted c' ∧
      ∃ (simCfg' : Cfg n tm.Q),
        tm.step simCfg = some simCfg' ∧
        simCfg'.state = tm.qhalt ∧
        superCellsCorrect simCfg' (c'.work utmSimTape) ∧
        (c'.work utmSimTape).head = 1 ∧
        c'.output.cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
        c'.input.read ≠ Γ.start)
    ∨
    -- Or the loop continues (simulated TM not yet halted)
    (∃ inp' work' out' t,
      (loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).reachesIn t
        ⟨(loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).qstart,
         inp, work, out⟩
        ⟨(loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).qstart,
         inp', work', out'⟩ ∧
      ∃ (simCfg' : Cfg n tm.Q),
        tm.step simCfg = some simCfg' ∧
        LoopInv tm k hk desc inp' work' out' simCfg') := by
  -- Step 1: Invoke utm_body_step to get reachesIn at utmSimStepTM level
  set e := tm.stateEquivK hk with he_def
  set iHead := simCfg.input.read with hiHead
  set wHeads := (fun i => (simCfg.work i).read) with hwHeads
  set oHead := simCfg.output.read with hoHead
  set δr := tm.δ simCfg.state iHead wHeads oHead with hδ_def
  obtain ⟨q', wW, oW, iD, wD, oD⟩ := δr
  obtain ⟨c_body, t_body, hreach_body, hhalt_body, hstate_body, hsim_body,
          hdesc_body, hheads_body, hwf_body,
          hscr_inp_body, hscr_out_body,
          hinp_read_body, hinp_head_body, hout_read_body, hout_head_body⟩ :=
    utm_body_step tm k hk desc hdesc_eq inp work out simCfg hinv
  -- Simplify the δ projections in postconditions
  have hδ_eq : tm.δ simCfg.state simCfg.input.read (fun i => (simCfg.work i).read)
      simCfg.output.read = (q', wW, oW, iD, wD, oD) := hδ_def.symm
  simp only [hδ_eq] at hstate_body hsim_body
  -- Define the stepped simCfg
  set simCfg' : Cfg n tm.Q :=
    ⟨q', simCfg.input.move iD,
     fun i => (simCfg.work i).writeAndMove (wW i).toΓ (wD i),
     simCfg.output.writeAndMove oW.toΓ oD⟩ with hsimCfg'_def
  -- Show tm.step simCfg = some simCfg'
  have hstep_eq : tm.step simCfg = some simCfg' := by
    simp only [step, hinv.hNotHalted, ↓reduceIte, hδ_eq]; rfl
  -- Step 2: Lift body reachesIn to loopTM level
  have hreach_loop_body :=
    loopTM_body_simulation (utmSimStepTM (n := n) k) utmCheckHaltTM hreach_body
  -- Step 3: Body→test transition (1 step)
  have hbody_to_test :=
    loopTM_body_to_test (utmSimStepTM (n := n) k) utmCheckHaltTM hhalt_body
  -- Step 4: Show loopTransition is identity on tapes
  have hinp_body_id : loopTransitionInput c_body.input = c_body.input :=
    loopTransitionInput_id hinp_read_body
  have hwork_body_id : (fun i => loopTransitionTape (c_body.work i)) = c_body.work :=
    loopTransition_work_id hwf_body (fun i => by rw [hheads_body i])
  have hout_body_id : loopTransitionTape c_body.output = c_body.output :=
    loopTransitionTape_id hout_read_body hout_head_body
  -- Rewrite the body→test target to use identity
  rw [hinp_body_id, hwork_body_id, hout_body_id] at hbody_to_test
  -- Step 5: Invoke checkHaltTM_hoareTime
  have he_val : ∀ q : tm.Q, (e q).val = (tm.stateEquiv q).val :=
    stateEquivK_val tm hk
  have hchk := checkHaltTM_hoareTime tm k e desc (e q') simCfg' (c_body.output.head) hk hdesc_eq he_val
  -- Build checkHalt precondition
  have hchk_pre : descOnTape desc (c_body.work utmDescTape) ∧
      stateOnTapeAt k (e q') (c_body.work utmStateTape) ∧
      (c_body.work utmDescTape).head = 1 ∧
      (c_body.work utmStateTape).head = 1 ∧
      c_body.output.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → c_body.output.cells j ≠ Γ.start) ∧
      c_body.output.head ≤ c_body.output.head ∧
      WorkTapesWF c_body.work ∧
      c_body.input.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → c_body.input.cells j ≠ Γ.start) ∧
      c_body.input.head ≥ 1 ∧
      (∀ i, (c_body.work i).head ≥ 1) ∧
      c_body.output.head ≥ 1 ∧
      superCellsCorrect simCfg' (c_body.work utmSimTape) ∧
      (c_body.work utmSimTape).head = 1 ∧
      (c_body.work utmScratchTape).head = 1 ∧
      (c_body.work utmScratchTape).cells (TMEncoding.inputPatternWidth k n + 1) = Γ.blank ∧
      (c_body.work utmScratchTape).cells (TMEncoding.outputWidth k n + 1) = Γ.blank := by
    have hinp_cells := input_cells_of_reachesIn hreach_body
    have hout_c0_body := output_cell0_of_reachesIn hreach_body hinv.hout_c0
    have hout_ns_body := output_noStart_of_reachesIn hreach_body hinv.hout_ns
    refine ⟨hdesc_body, hstate_body, hheads_body utmDescTape, hheads_body utmStateTape,
            hout_c0_body, hout_ns_body, le_refl _, hwf_body,
            ?_, ?_, hinp_head_body,
            fun i => by rw [hheads_body i], hout_head_body,
            hsim_body, hheads_body utmSimTape, hheads_body utmScratchTape,
            hscr_inp_body, hscr_out_body⟩
    · rw [hinp_cells]; exact hinv.hinp_c0
    · intro j hj; rw [hinp_cells]; exact hinv.hinp_ns j hj
  -- Apply checkHalt HoareTime
  obtain ⟨c_chk, t_chk, _, hreach_chk, hhalt_chk, hpost_chk⟩ :=
    hchk c_body.input c_body.work c_body.output hchk_pre
  obtain ⟨hchk_desc, hchk_state, hchk_halt_one, hchk_cont_zero, hchk_out_head,
          hchk_dh, hchk_sh, hchk_wf, hchk_wheads,
          hchk_inp_read, hchk_inp_head, hchk_out_c0, hchk_out_ns,
          hchk_sim, hchk_simh, hchk_scrh,
          hchk_scr_inp, hchk_scr_out⟩ := hpost_chk
  -- Step 6: Lift test reachesIn to loopTM level
  have hreach_loop_test :=
    loopTM_test_simulation (utmSimStepTM (n := n) k) utmCheckHaltTM hreach_chk
  -- Step 7: Test→rewind transition (1 step)
  have htest_to_rewind :=
    loopTM_test_to_rewind (utmSimStepTM (n := n) k) utmCheckHaltTM hhalt_chk
  -- Show loopTransition is identity on c_chk tapes
  have hchk_inp_id : loopTransitionInput c_chk.input = c_chk.input :=
    loopTransitionInput_id hchk_inp_read
  have hchk_work_id : (fun i => loopTransitionTape (c_chk.work i)) = c_chk.work :=
    loopTransition_work_id hchk_wf hchk_wheads
  have hchk_out_read : c_chk.output.read ≠ Γ.start := by
    simp only [Tape.read, hchk_out_head]; exact hchk_out_ns 1 (by omega)
  have hchk_out_id : loopTransitionTape c_chk.output = c_chk.output :=
    loopTransitionTape_id hchk_out_read (by rw [hchk_out_head])
  -- Rewrite test→rewind target to use identities
  rw [hchk_inp_id, hchk_work_id, hchk_out_id] at htest_to_rewind
  -- Step 8: Rewind loop
  -- c_chk.output.head = 1, so rewind takes 1+1 = 2 steps
  -- But actually, the rewind expects to start from rewindOut state.
  -- After test_to_rewind, we're at rewindOut state with c_chk's tapes.
  -- We need the output head value for the rewind.
  -- The rewind needs c_chk.output.cells 0 = start, ∀ j ≥ 1, cells j ≠ start,
  -- head = p, input head ≥ 1, input cells ≥ 1 ≠ start, work heads ≥ 1, work cells ≠ start
  -- All of these are available from hchk_* and hinv.
  -- Also need input cells from c_chk.
  -- c_chk.input = c_body.input (checkHalt preserves input) via hchk_inp_read/hchk_inp_head.
  -- But we need c_chk.input.cells facts. Use input_cells_of_reachesIn on hreach_chk.
  have hchk_inp_cells := input_cells_of_reachesIn hreach_chk
  -- hchk_inp_cells : c_chk.input.cells = c_body.input.cells
  have hinp_cells_body := input_cells_of_reachesIn hreach_body
  -- hinp_cells_body : c_body.input.cells = inp.cells
  have hchk_inp_ns : ∀ j, j ≥ 1 → c_chk.input.cells j ≠ Γ.start := by
    intro j hj; rw [hchk_inp_cells, hinp_cells_body]; exact hinv.hinp_ns j hj
  -- Apply rewind loop (with p = c_chk.output.head = 1)
  set c_rewind_start : Cfg 4 (LoopQ (utmSimStepTM (n := n) k).Q utmCheckHaltTM.Q) :=
    { state := Sum.inr (Sum.inl LoopPhase.rewindOut),
      input := c_chk.input,
      work := c_chk.work,
      output := c_chk.output } with hc_rewind_start_def
  obtain ⟨c_check, hreach_rewind, hcheck_state, hcheck_out_head, hcheck_out_cells,
          hcheck_input, hcheck_work⟩ :=
    loopTM_rewind_loop_full (utmSimStepTM (n := n) k) utmCheckHaltTM
      c_chk.output.head c_rewind_start
      rfl hchk_out_c0 hchk_out_ns rfl hchk_inp_head hchk_inp_ns
      hchk_wheads hchk_wf.2
  -- Simplify c_check tapes: they equal c_chk tapes
  -- c_check.output.cells = c_chk.output.cells (via c_rewind_start)
  -- c_check.work = c_chk.work, c_check.input = c_chk.input
  have hcheck_out_cells' : c_check.output.cells = c_chk.output.cells := by
    rw [hcheck_out_cells]
  have hcheck_input' : c_check.input = c_chk.input := hcheck_input
  have hcheck_work' : c_check.work = c_chk.work := hcheck_work
  -- Derive check-phase tape facts from c_chk facts via rewrites
  have hcheck_wf : WorkTapesWF c_check.work := hcheck_work' ▸ hchk_wf
  have hcheck_wheads : ∀ i, (c_check.work i).head ≥ 1 := by
    intro i; rw [hcheck_work']; exact hchk_wheads i
  have hcheck_inp_head : c_check.input.head ≥ 1 := by rw [hcheck_input']; exact hchk_inp_head
  have hcheck_inp_ns : ∀ j, j ≥ 1 → c_check.input.cells j ≠ Γ.start := by
    intro j hj; rw [hcheck_input']; exact hchk_inp_ns j hj
  have hcheck_out_c0 : c_check.output.cells 0 = Γ.start := by
    rw [hcheck_out_cells']; exact hchk_out_c0
  have hcheck_out_ns : ∀ j, j ≥ 1 → c_check.output.cells j ≠ Γ.start := by
    intro j hj; rw [hcheck_out_cells']; exact hchk_out_ns j hj
  -- Step 9: Case split on e q' = e tm.qhalt
  by_cases hqhalt : e q' = e tm.qhalt
  · -- ═══ HALT case: simulated TM reached qhalt ═══
    have hcell1 : c_check.output.cells 1 = Γ.one := by
      rw [hcheck_out_cells']; exact hchk_halt_one hqhalt
    obtain ⟨c_done, hdone_step, hdone_state, hdone_cells, hdone_head,
            hdone_input, hdone_work⟩ :=
      loopTM_check_halt_full (utmSimStepTM (n := n) k) utmCheckHaltTM c_check
        hcheck_state hcheck_out_head hcell1 hcheck_inp_head hcheck_inp_ns
        hcheck_wheads hcheck_wf.2
    -- Build the full reachesIn chain:
    -- loopStart →[t_body] bodyWrap c_body →[1] testWrap c_chk_start
    -- →[t_chk] testWrap c_chk →[1] rewindStart →[head+1] c_check →[1] c_done
    -- First: loopBodyWrap start config = loopTM qstart config
    have hloop_start_eq : loopBodyWrap (utmSimStepTM (n := n) k) utmCheckHaltTM
        { state := (utmSimStepTM (n := n) k).qstart, input := inp, work := work, output := out } =
        { state := ((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM).qstart,
          input := inp, work := work, output := out } := by
      simp [loopBodyWrap, loopTM]
    rw [hloop_start_eq] at hreach_loop_body
    -- Chain: body →[1] test start
    have hreach_to_test := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_loop_body
      (.step hbody_to_test .zero)
    -- Chain: test start →[t_chk] test end
    have hreach_to_test_end := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_to_test hreach_loop_test
    -- Chain: →[1] rewind start
    have hreach_to_rewind := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_to_test_end (.step htest_to_rewind .zero)
    -- Chain: →[head+1] c_check
    have hreach_to_check := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_to_rewind hreach_rewind
    -- Chain: →[1] c_done
    have hreach_to_done := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_to_check (.step hdone_step .zero)
    -- c_done is halted (state = done)
    have hdone_halted : ((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM).halted c_done :=
      loopTM_halted_done _ _ c_done hdone_state
    -- q' = tm.qhalt by injectivity of e
    have hq'_halt : q' = tm.qhalt := e.injective hqhalt
    left
    refine ⟨c_done, _, hreach_to_done, hdone_halted, simCfg', hstep_eq, hq'_halt, ?_, ?_,
            ?_, ?_, ?_⟩
    · rw [hdone_work, hcheck_work']; exact hchk_sim
    · rw [hdone_work, hcheck_work']; exact hchk_simh
    · rw [hdone_cells]; exact hcheck_out_c0
    · intro j hj; rw [hdone_cells]; exact hcheck_out_ns j hj
    · rw [hdone_input, hcheck_input']; exact hchk_inp_read
  · -- ═══ CONTINUE case: simulated TM not yet halted ═══
    have hcell1_zero : c_chk.output.cells 1 = Γ.zero := hchk_cont_zero hqhalt
    have hcell1_ne : c_check.output.cells 1 ≠ Γ.one := by
      rw [hcheck_out_cells', hcell1_zero]; exact Γ.noConfusion
    obtain ⟨c_cont, hcont_step, hcont_state, hcont_cells, hcont_head,
            hcont_input, hcont_work⟩ :=
      loopTM_check_continue_full (utmSimStepTM (n := n) k) utmCheckHaltTM c_check
        hcheck_state hcheck_out_head hcell1_ne hcheck_out_ns
        hcheck_inp_head hcheck_inp_ns hcheck_wheads hcheck_wf.2
    -- c_cont.state = Sum.inl (utmSimStepTM k).qstart = loopTM.qstart
    -- Build the full reachesIn chain (same as halt case but ending at c_cont)
    have hloop_start_eq : loopBodyWrap (utmSimStepTM (n := n) k) utmCheckHaltTM
        { state := (utmSimStepTM (n := n) k).qstart, input := inp, work := work, output := out } =
        { state := ((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM).qstart,
          input := inp, work := work, output := out } := by
      simp [loopBodyWrap, loopTM]
    rw [hloop_start_eq] at hreach_loop_body
    have hreach_to_test := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_loop_body (.step hbody_to_test .zero)
    have hreach_to_test_end := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_to_test hreach_loop_test
    have hreach_to_rewind := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_to_test_end (.step htest_to_rewind .zero)
    have hreach_to_check := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_to_rewind hreach_rewind
    have hreach_to_cont := reachesIn_trans
      (((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM))
      hreach_to_check (.step hcont_step .zero)
    -- c_cont.state = Sum.inl (utmSimStepTM k).qstart = loopTM.qstart
    have hcont_is_qstart : c_cont.state = ((utmSimStepTM (n := n) k).loopTM utmCheckHaltTM).qstart := by
      show c_cont.state = Sum.inl (utmSimStepTM (n := n) k).qstart
      exact hcont_state
    -- q' ≠ tm.qhalt from hqhalt and injectivity
    have hq'_ne_halt : q' ≠ tm.qhalt := fun h => hqhalt (congrArg e h)
    -- Get input cells facts for c_cont
    have hcont_inp_c0 : c_cont.input.cells 0 = Γ.start := by
      rw [hcont_input, hcheck_input', hchk_inp_cells, hinp_cells_body]; exact hinv.hinp_c0
    -- Get heads = 1 for work tapes from checkHalt postcondition
    have hcont_wheads : ∀ i, (c_cont.work i).head = 1 := by
      intro i; rw [hcont_work, hcheck_work']
      have : i = (0 : Fin 4) ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact hchk_dh
      · exact hchk_sh
      · exact hchk_simh
      · exact hchk_scrh
    right
    exact ⟨c_cont.input, c_cont.work, c_cont.output, _,
      by convert hreach_to_cont using 2; exact hcont_is_qstart.symm,
      simCfg', hstep_eq, {
        hNotHalted := hq'_ne_halt
        hdesc := by rw [hcont_work, hcheck_work']; exact hchk_desc
        hstate := by rw [hcont_work, hcheck_work']; exact hchk_state
        hsim := by rw [hcont_work, hcheck_work']; exact hchk_sim
        hheads := hcont_wheads
        hwf := by rw [hcont_work, hcheck_work']; exact hchk_wf
        hscratch_inp_blank := by rw [hcont_work, hcheck_work']; exact hchk_scr_inp
        hscratch_out_blank := by rw [hcont_work, hcheck_work']; exact hchk_scr_out
        hinp_c0 := hcont_inp_c0
        hinp_ns := by intro j hj; rw [hcont_input, hcheck_input']; exact hchk_inp_ns j hj
        hinp_h := by rw [hcont_input, hcheck_input']; exact hchk_inp_head
        hout_c0 := by rw [hcont_cells]; exact hcheck_out_c0
        hout_ns := by intro j hj; rw [hcont_cells]; exact hcheck_out_ns j hj
        hout_h := by rw [hcont_head]
      }⟩

-- ════════════════════════════════════════════════════════════════════════
-- Phase 2: Simulation loop by induction
-- ════════════════════════════════════════════════════════════════════════

/-- The simulation loop terminates correctly. -/
private theorem utm_loop_terminates (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (desc : List Bool) (hdesc_eq : desc = TMEncoding.encodeTM tm)
    (L : Language)
    (c'_halt : Cfg n tm.Q) (hhalt : tm.halted c'_halt)
    (hmem : x ∈ L → c'_halt.output.cells 1 = Γ.one)
    (hnmem : x ∉ L → c'_halt.output.cells 1 = Γ.zero) :
    ∀ (t_remain : ℕ) (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
      (simCfg : Cfg n tm.Q) (s : ℕ),
    tm.reachesIn s (tm.initCfg x) simCfg →
    LoopInv tm k hk desc inp work out simCfg →
    tm.reachesIn t_remain simCfg c'_halt →
    ∃ c' t,
      (loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).reachesIn t
        ⟨(loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).qstart,
         inp, work, out⟩ c' ∧
      (loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM).halted c' ∧
      superCellsCorrect c'_halt (c'.work utmSimTape) ∧
      (c'.work utmSimTape).head = 1 ∧
      c'.output.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → c'.output.cells j ≠ Γ.start) ∧
      c'.input.read ≠ Γ.start := by
  intro t_remain
  induction t_remain with
  | zero =>
    intro inp work out simCfg s _ hinv hhalt_reach
    cases hhalt_reach; exact absurd hhalt hinv.hNotHalted
  | succ t_remain ih =>
    intro inp work out simCfg s hreach_sim hinv hhalt_reach
    -- One iteration of the UTM loop
    obtain h_halt | h_cont := utm_one_iteration tm k hk desc hdesc_eq
      inp work out simCfg hinv
    · -- Loop halted: the stepped simCfg' has state = qhalt
      obtain ⟨c', t, hreach_loop, hhalted_loop, simCfg', hstep_eq, hhalt_sim',
              hsim', hsimh', hoc0', hons', hinp_r'⟩ := h_halt
      -- simCfg' is halted, and c'_halt is reached from simCfg in t_remain+1 steps
      -- Decompose: simCfg →[1] c_next →[t_remain] c'_halt
      obtain ⟨c_next, hstep_sim, hreach_rest⟩ : ∃ c_next,
          tm.step simCfg = some c_next ∧ tm.reachesIn t_remain c_next c'_halt := by
        cases hhalt_reach with | step hs hr => exact ⟨_, hs, hr⟩
      -- By determinism: simCfg' = c_next
      have heq : simCfg' = c_next := step_det hstep_eq hstep_sim
      -- c_next is halted (since simCfg' is)
      have hhalt_next : tm.halted c_next := heq ▸ hhalt_sim'
      -- Therefore t_remain = 0 and c'_halt = c_next
      obtain ⟨ht0, hc_eq⟩ := reachesIn_zero_of_halted hhalt_next hreach_rest
      subst ht0; subst hc_eq
      exact ⟨c', t, hreach_loop, hhalted_loop, heq ▸ hsim', hsimh',
        hoc0', hons', hinp_r'⟩
    · -- Loop continues: simCfg' has state ≠ qhalt
      obtain ⟨inp', work', out', t₁, hreach₁, simCfg', hstep_eq', hinv'⟩ := h_cont
      -- Decompose: simCfg →[1] c_next →[t_remain] c'_halt
      obtain ⟨c_next, hstep_sim, hreach_rest⟩ : ∃ c_next,
          tm.step simCfg = some c_next ∧ tm.reachesIn t_remain c_next c'_halt := by
        cases hhalt_reach with | step hs hr => exact ⟨_, hs, hr⟩
      -- By determinism: simCfg' = c_next
      have heq : simCfg' = c_next := step_det hstep_eq' hstep_sim
      -- Apply IH: from c_next, t_remain steps to halt
      have hreach_sim' : tm.reachesIn (s + 1) (tm.initCfg x) c_next :=
        reachesIn_trans _ hreach_sim (.step hstep_sim .zero)
      obtain ⟨c', t₂, hreach₂, hhalted₂, hsim₂, hsimh₂, hoc0₂, hons₂, hinp_r₂⟩ :=
        ih inp' work' out' c_next (s + 1) hreach_sim' (heq ▸ hinv') hreach_rest
      exact ⟨c', t₁ + t₂, reachesIn_trans _ hreach₁ hreach₂,
        hhalted₂, hsim₂, hsimh₂, hoc0₂, hons₂, hinp_r₂⟩

-- ════════════════════════════════════════════════════════════════════════
-- Full UTM simulation proof
-- ════════════════════════════════════════════════════════════════════════

/-- **UTM simulation correctness**. -/
theorem utm_simulates_proof (tm : TM n) (k : ℕ)
    (hk : k = @Fintype.card tm.Q tm.finQ)
    (L : Language) (T : ℕ → ℕ)
    (hM : tm.DecidesInTime L T) (x : List Bool) :
    ∃ (c' : Cfg 4 (utmTM (n := n) k).Q) (t : ℕ),
      (utmTM (n := n) k).reachesIn t (utmInitCfg tm k x) c' ∧
      (utmTM (n := n) k).halted c' ∧
      (x ∈ L → c'.output.cells 1 = Γ.one) ∧
      (x ∉ L → c'.output.cells 1 = Γ.zero) := by
  -- Extract the halting guarantee from DecidesInTime
  obtain ⟨c'_halt, t_halt, _, hreach_halt, hhalt, hmem, hnmem⟩ := hM x
  let desc := TMEncoding.encodeTM tm
  -- ── Show qstart ≠ qhalt ───────────────────────────────────────────
  -- If t_halt = 0, then initCfg x = c'_halt, so output.cells 1 = blank.
  -- But hmem/hnmem says it should be one or zero. Contradiction.
  have hstart_ne_halt : tm.qstart ≠ tm.qhalt := by
    intro heq
    have : t_halt = 0 ∧ c'_halt = tm.initCfg x := by
      cases hreach_halt with
      | zero => exact ⟨rfl, rfl⟩
      | step hs _ =>
        simp only [step, heq] at hs
        split at hs <;> simp_all [halted, Cfg.isHalted]
    obtain ⟨_, hceq⟩ := this
    have hout : c'_halt.output.cells 1 = Γ.blank := by
      rw [hceq]; simp [initTape]
    by_cases hx : x ∈ L
    · have := hmem hx; rw [hout] at this; exact absurd this (by decide)
    · have := hnmem hx; rw [hout] at this; exact absurd this (by decide)
  -- ── Phase 1: Init ──────────────────────────────────────────────────
  obtain ⟨B_init, h_init⟩ := initTM_hoareTime_exact tm k x hk
  -- Apply init HoareTime to the initial tapes
  have h_init_pre : (initTape (encodeUTMInput tm x)) = initTape (encodeUTMInput tm x) ∧
      ((fun _ : Fin 4 => initTape ([] : List Γ)) = fun _ => initTape []) ∧
      (initTape ([] : List Γ)) = initTape [] := ⟨rfl, rfl, rfl⟩
  obtain ⟨c_init, t_init, ht_init_le, hreach_init, hhalt_init, hpost_init⟩ :=
    h_init _ _ _ h_init_pre
  obtain ⟨henv, hdesc_init, hstate_init, hscc_init, hheads_init, hscratch_init⟩ := hpost_init
  -- ── Phase 2: Construct LoopInv for initCfg x ──────────────────────
  -- Extract InitEnvelope facts
  obtain ⟨hinp_c0, hinp_ns, hinp_h, hwf_init, hwork_heads_ge1, hout_c0, hout_ns, hout_h⟩ := henv
  have hinv : LoopInv tm k hk desc c_init.input c_init.work c_init.output (tm.initCfg x) := {
    hNotHalted := hstart_ne_halt
    hdesc := hdesc_init
    hstate := by convert hstate_init using 2
    hsim := hscc_init
    hheads := fun i => by have := hheads_init i; omega
    hwf := hwf_init
    hscratch_inp_blank := by
      apply hscratch_init; simp [TMEncoding.inputPatternWidth]; omega
    hscratch_out_blank := by
      apply hscratch_init; simp [TMEncoding.outputWidth]; omega
    hinp_c0 := hinp_c0
    hinp_ns := hinp_ns
    hinp_h := hinp_h
    hout_c0 := hout_c0
    hout_ns := hout_ns
    hout_h := hout_h
  }
  -- ── Abbreviations for the sub-machines ─────────────────────────────
  let tm_loop := loopTM (utmSimStepTM (n := n) k) utmCheckHaltTM
  let tm_extract := extractOutputTM (n := n)
  -- ── Phase 2: Run the simulation loop ───────────────────────────────
  obtain ⟨c_loop, t_loop, hreach_loop, hhalt_loop, hscc_loop, hsimh_loop,
          hoc0_loop, hons_loop, hinp_r_loop⟩ :=
    utm_loop_terminates tm k hk desc rfl L c'_halt hhalt hmem hnmem
      t_halt c_init.input c_init.work c_init.output (tm.initCfg x) 0
      .zero hinv hreach_halt
  -- ── Phase 3: Run extractOutputTM ───────────────────────────────────
  -- The simulated c'_halt.output.cells 1 ≠ Γ.start
  have hout_sym : c'_halt.output.cells 1 ≠ Γ.start := by
    by_cases hx : x ∈ L
    · rw [hmem hx]; decide
    · rw [hnmem hx]; decide
  -- Show sim tape read ≠ Γ.start (for seqTransition identity)
  -- cells 1 is the head marker of (pos=0, tapeIdx=0) super-cell
  have hsim_read_loop : (c_loop.work utmSimTape).read ≠ Γ.start := by
    rw [Tape.read, hsimh_loop]
    -- cells 1 = simTapeOffset (n+2) 0 0 = 1, and simTapeCellCorrect says
    -- it's either Γ.one or Γ.blank (head marker)
    obtain ⟨_, hinp_scc, _, _⟩ := hscc_loop
    have h := hinp_scc 0
    simp only [simTapeCellCorrect, SuperCell.simTapeOffset, SuperCell.width] at h
    obtain ⟨h0, _, _⟩ := h
    simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero] at h0
    split at h0 <;> (rw [h0]; decide)
  have hsim_seq_id : seqTransitionTape (c_loop.work utmSimTape) = c_loop.work utmSimTape :=
    seqTransitionTape_id hsim_read_loop (by omega)
  -- Show output tape seqTransition preserves cells
  have hout_seq_cells : (seqTransitionTape c_loop.output).cells = c_loop.output.cells :=
    seqTransitionTape_cells c_loop.output hons_loop
  -- Show output tape seqTransition head ≤ original head + 1
  -- (seqTransition moves head right by at most 1, when read = start)
  have hout_seq_head_le : (seqTransitionTape c_loop.output).head ≤ c_loop.output.head + 1 := by
    by_cases hr : c_loop.output.read = Γ.start
    · -- read = start → idleDir = right → head + 1
      unfold seqTransitionTape Tape.writeAndMove idleDir
      rw [hr]; simp only [ite_true, Tape.move, Tape.write]
      split_ifs with h0 <;> simp_all
    · -- read ≠ start → seqTransitionTape is identity
      have hge1 : c_loop.output.head ≥ 1 := by
        by_contra h; push_neg at h
        have h0 : c_loop.output.head = 0 := by omega
        rw [Tape.read, h0] at hr; exact hr hoc0_loop
      rw [seqTransitionTape_id hr hge1]; omega
  -- Show input seqTransition preserves read ≠ start
  have hinp_seq_read : (seqTransitionInput c_loop.input).read ≠ Γ.start := by
    rw [seqTransitionInput_id (by exact hinp_r_loop)]
    exact hinp_r_loop
  -- Apply extractOutputTM_hoareTime with B = c_loop.output.head + 1
  have h_extract_pre :
      superCellsCorrect c'_halt ((fun i => seqTransitionTape (c_loop.work i)) utmSimTape) ∧
      ((fun i => seqTransitionTape (c_loop.work i)) utmSimTape).head = 1 ∧
      (seqTransitionTape c_loop.output).cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → (seqTransitionTape c_loop.output).cells j ≠ Γ.start) ∧
      (seqTransitionTape c_loop.output).head ≤ (c_loop.output.head + 1) ∧
      (seqTransitionInput c_loop.input).read ≠ Γ.start := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hinp_seq_read⟩
    · simp only [hsim_seq_id]; exact hscc_loop
    · simp only [hsim_seq_id]; exact hsimh_loop
    · rw [hout_seq_cells]; exact hoc0_loop
    · intro j hj; rw [hout_seq_cells]; exact hons_loop j hj
    · exact hout_seq_head_le
  obtain ⟨c_extract, t_extract, _, hreach_extract, hhalt_extract, hpost_extract⟩ :=
    (extractOutputTM_hoareTime (n := n) c'_halt (c_loop.output.head + 1) hout_sym)
      (seqTransitionInput c_loop.input)
      (fun i => seqTransitionTape (c_loop.work i))
      (seqTransitionTape c_loop.output)
      h_extract_pre
  -- ── Phase 4: Compose loop → extract via seqTM_full_simulation ──────
  have hhalt_loop_state : c_loop.state = tm_loop.qhalt := hhalt_loop
  have hreach_inner : (seqTM tm_loop tm_extract).reachesIn (t_loop + 1 + t_extract)
      (phase1Wrap tm_loop tm_extract
        ⟨tm_loop.qstart, c_init.input, c_init.work, c_init.output⟩)
      (phase2Wrap tm_loop tm_extract c_extract) :=
    seqTM_full_simulation tm_loop tm_extract hreach_loop hhalt_loop_state hreach_extract
  -- ── Phase 5: Compose init → (loop;extract) via seqTM_full_simulation
  have hhalt_init_state : c_init.state = initTM.qhalt := hhalt_init
  -- The init postcondition gives WF + heads = 1, so seqTransition is identity
  have hwork_seq_init_id : (fun i => seqTransitionTape (c_init.work i)) = c_init.work :=
    seqTransition_work_id hwf_init (fun i => by have := hheads_init i; omega)
  have hout_seq_init_id : seqTransitionTape c_init.output = c_init.output :=
    seqTransitionTape_id (by rw [Tape.read]; exact hout_ns _ hout_h) hout_h
  have hinp_seq_init_id : seqTransitionInput c_init.input = c_init.input :=
    seqTransitionInput_id (by rw [Tape.read]; exact hinp_ns _ hinp_h)
  -- The inner machine starts from the seqTransitioned init output = identity
  have hreach_inner' : (seqTM tm_loop tm_extract).reachesIn (t_loop + 1 + t_extract)
      { state := (seqTM tm_loop tm_extract).qstart,
        input := seqTransitionInput c_init.input,
        work := fun i => seqTransitionTape (c_init.work i),
        output := seqTransitionTape c_init.output }
      (phase2Wrap tm_loop tm_extract c_extract) := by
    rw [hwork_seq_init_id, hout_seq_init_id, hinp_seq_init_id]
    convert hreach_inner using 1
  -- The full composition: init → (loop;extract)
  have hreach_full := seqTM_full_simulation initTM (seqTM tm_loop tm_extract)
    hreach_init hhalt_init_state hreach_inner'
  -- The starting config matches utmInitCfg
  have hstart_eq : phase1Wrap initTM (seqTM tm_loop tm_extract)
      ⟨initTM.qstart, initTape (encodeUTMInput tm x), fun _ => initTape [], initTape []⟩ =
      utmInitCfg tm k x := by
    simp [phase1Wrap, utmInitCfg, utmTM, seqTM]
  -- The final config
  let c_final := phase2Wrap initTM (seqTM tm_loop tm_extract) (phase2Wrap tm_loop tm_extract c_extract)
  -- Output of the final config
  have hfinal_output : c_final.output = c_extract.output := rfl
  -- The final config is halted in utmTM
  have hfinal_halted : (utmTM (n := n) k).halted c_final := by
    show (seqTM initTM (seqTM tm_loop tm_extract)).halted c_final
    rw [phase2Wrap_halted]
    rw [phase2Wrap_halted]
    exact hhalt_extract
  -- Output correctness
  have hfinal_mem : x ∈ L → c_final.output.cells 1 = Γ.one := by
    intro hx; rw [hfinal_output, hpost_extract]; exact hmem hx
  have hfinal_nmem : x ∉ L → c_final.output.cells 1 = Γ.zero := by
    intro hx; rw [hfinal_output, hpost_extract]; exact hnmem hx
  exact ⟨c_final, _, hstart_eq ▸ hreach_full, hfinal_halted, hfinal_mem, hfinal_nmem⟩

end TM
