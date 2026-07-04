import Complexitylib.Models.TuringMachine.UTM.Body

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

end TM.UTMBody
