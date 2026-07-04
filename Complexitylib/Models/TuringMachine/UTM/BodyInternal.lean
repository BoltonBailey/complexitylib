import Complexitylib.Models.TuringMachine.UTM.Body
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

/-!
# Body machine: step reduction

The single lemma every phase proof of the body correctness uses:
`bodyTM.step` on a non-halted configuration, when the transition arm is a
`mkAct` (they all are, by `bodyδ_shape`), produces the configuration whose
work tapes act per `acts`, whose real input idles, and whose real output
write-backs — in closed form.
-/

namespace TM.UTMBody

open BodyQ

/-- Closed form of one `bodyTM` step whose transition arm is `mkAct q' acts`
    (every arm is — `bodyδ_shape`). The real input tape idle-moves, the real
    output tape write-backs and idle-moves, and work tape `i` performs
    `acts i` (with the `▷ ⇒ right` sanitization) or idles. -/
theorem step_mkAct {c : Cfg 6 bodyTM.Q} (hne : c.state ≠ bodyDone)
    {q' : BodyQ} {acts : TapeActs}
    (h : bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
      = mkAct q' c.input.read (fun i => (c.work i).read) c.output.read acts) :
    bodyTM.step c = some
      { state := q'
        input := c.input.move (idleDir c.input.read)
        work := fun i => match acts i with
          | some (w, d) => (c.work i).writeAndMove w.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d)
          | none => (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
              (idleDir ((c.work i).read))
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) } := by
  have hne' : c.state ≠ bodyTM.qhalt := hne
  simp only [step, if_neg hne', Option.some.injEq]
  show (let (q'', wW, oW, iD, wD, oD) :=
      bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
    ({ state := q'', input := c.input.move iD,
       work := fun i => (c.work i).writeAndMove (wW i).toΓ (wD i),
       output := c.output.writeAndMove oW.toΓ oD } : Cfg 6 bodyTM.Q)) = _
  rw [h]
  simp only [mkAct, Cfg.mk.injEq]
  refine ⟨trivial, trivial, ?_, trivial⟩
  funext i
  cases acts i with
  | none => rfl
  | some wd => rfl

/-- An idle work tape is exactly preserved by a `mkAct` step when it reads
    a non-`▷` symbol (its action is precisely `transitionTape`). -/
theorem idle_tape_id {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t :=
  transitionTape_id h

/-- The idled real input tape is exactly preserved when reading non-`▷`. -/
theorem idle_input_id {t : Tape} (h : t.read ≠ Γ.start) :
    t.move (idleDir t.read) = t :=
  transitionInput_id h

-- ════════════════════════════════════════════════════════════════════════
-- Generic rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- Closed form of a step whose arm is `act1` (one active tape). -/
theorem step_act1 {c : Cfg 6 bodyTM.Q} (hne : c.state ≠ bodyDone)
    {q' : BodyQ} {t : Fin 6} {w : Γw} {d : Dir3}
    (h : bodyδ c.state c.input.read (fun i => (c.work i).read) c.output.read
      = act1 q' c.input.read (fun i => (c.work i).read) c.output.read t w d) :
    bodyTM.step c = some
      { state := q'
        input := c.input.move (idleDir c.input.read)
        work := fun i =>
          if i = t then
            (c.work i).writeAndMove w.toΓ
              (if (c.work i).read = Γ.start then Dir3.right else d)
          else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
            (idleDir ((c.work i).read))
        output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
          (idleDir c.output.read) } := by
  rw [step_mkAct hne h]
  refine congrArg some ?_
  simp only [Cfg.mk.injEq]
  refine ⟨trivial, trivial, funext fun i => ?_, trivial⟩
  by_cases hi : i = t <;> simp [hi]

/-- **Generic rewind loop** for any pair of states whose transition is
    `rewStep cur next · t`: from state `cur` with work-tape-`t` head at `p`
    (cells `W`, well-formed), reach state `next` with head 1 in `p + 1`
    steps; tape `t`'s cells and every other tape are exactly preserved. -/
theorem rewStep_loop {cur next : BodyQ} {t : Fin 6}
    (hcur : cur ≠ bodyDone)
    (hδ : ∀ iH wH oH, bodyδ cur iH wH oH = rewStep cur next iH wH oH t)
    (W : ℕ → Γ) (hW0 : W 0 = Γ.start) (hWns : ∀ j, 1 ≤ j → W j ≠ Γ.start) :
    ∀ (p : ℕ) (c : Cfg 6 bodyTM.Q),
      c.state = cur →
      (c.work t).cells = W → (c.work t).head = p →
      c.input.read ≠ Γ.start → c.output.read ≠ Γ.start →
      (∀ i, i ≠ t → (c.work i).read ≠ Γ.start) →
      ∃ c', bodyTM.reachesIn (p + 1) c c' ∧
        c'.state = next ∧
        c'.work t = ⟨1, W⟩ ∧
        c'.input = c.input ∧ c'.output = c.output ∧
        (∀ i, i ≠ t → c'.work i = c.work i) := by
  intro p
  induction p with
  | zero =>
    intro c hst hcW hhead hin hout hoth
    have hread : (c.work t).read = Γ.start := by
      simp [Tape.read, hhead, hcW, hW0]
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
    rw [rewStep, if_pos hread] at harm
    have hstep := step_act1 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    refine ⟨_, .step hstep .zero, rfl, ?_, idle_input_id hin, idle_tape_id hout, ?_⟩
    · show (if t = t then _ else _) = _
      rw [if_pos rfl, if_pos hread]
      have hwr : (c.work t).write (readBackWrite ((c.work t).read)).toΓ = c.work t := by
        unfold Tape.write
        rw [if_pos hhead]
      show ((c.work t).write _).move .right = _
      rw [hwr]
      simp only [Tape.move, Tape.mk.injEq]
      exact ⟨by rw [hhead], hcW⟩
    · intro i hi
      show (if i = t then _ else _) = _
      rw [if_neg hi]
      exact idle_tape_id (hoth i hi)
  | succ p ih =>
    intro c hst hcW hhead hin hout hoth
    have hread : (c.work t).read ≠ Γ.start := by
      simp only [Tape.read, hhead, hcW]
      exact hWns (p + 1) (by omega)
    have harm := hδ c.input.read (fun i => (c.work i).read) c.output.read
    rw [rewStep, if_neg hread] at harm
    have hstep := step_act1 (by rw [hst]; exact hcur) (by rw [hst]; exact harm)
    obtain ⟨c', hreach, hst', hwt', hin', hout', hoth'⟩ :=
      ih { state := cur
           input := c.input.move (idleDir c.input.read)
           work := fun i =>
             if i = t then
               (c.work i).writeAndMove (readBackWrite ((c.work t).read)).toΓ
                 (if (c.work i).read = Γ.start then Dir3.right else Dir3.left)
             else (c.work i).writeAndMove (readBackWrite ((c.work i).read)).toΓ
               (idleDir ((c.work i).read))
           output := c.output.writeAndMove (readBackWrite c.output.read).toΓ
             (idleDir c.output.read) }
        rfl
        (by
          dsimp only
          rw [if_pos rfl, if_neg hread,
            tape_readBackWrite_preserves _ _ (Or.inr hread), hcW])
        (by
          dsimp only
          rw [if_pos rfl, if_neg hread]
          simp only [Tape.writeAndMove, Tape.move, Tape.write_head', hhead]
          omega)
        (by dsimp only; rw [idle_input_id hin]; exact hin)
        (by dsimp only; rw [idle_tape_id hout]; exact hout)
        (fun i hi => by
          dsimp only
          rw [if_neg hi, idle_tape_id (hoth i hi)]
          exact hoth i hi)
    refine ⟨c', .step hstep hreach, hst', hwt', ?_, ?_, ?_⟩
    · rw [hin']; exact idle_input_id hin
    · rw [hout']; exact idle_tape_id hout
    · intro i hi
      rw [hoth' i hi]
      show (if i = t then _ else _) = _
      rw [if_neg hi]
      exact idle_tape_id (hoth i hi)

end TM.UTMBody
