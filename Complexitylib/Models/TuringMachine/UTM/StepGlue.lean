import Complexitylib.Models.TuringMachine.UTM.BodyAssembly
import Complexitylib.Models.TuringMachine.UTM.BodyLookup

/-!
# Glue facts: phase outputs vs the interpreted step

Small bridges used when matching the body's phase outputs against
`TMDesc.toTM.step`:

* a well-formed tape reads `▷` exactly at the origin, so the peek flags
  and the interpreter's sanitization conditions coincide;
* `simRead` of the live shadow read recovers the simulated read exactly;
* parsed entries' targets are in range, so the interpreter's `min`-clamp is
  the identity on them.
-/

namespace TM.UTMBody

/-- A well-formed tape reads `▷` exactly at cell 0. -/
theorem read_start_iff {t : Tape} (h : t.WFCells) :
    t.read = Γ.start ↔ t.head = 0 := by
  constructor
  · intro hr
    by_contra hne
    exact h.2 t.head (by omega) hr
  · intro hh
    rw [Tape.read, hh]
    exact h.1

/-- The simulated read, reconstructed from the honest flag and the live
    shadow read, is exactly the simulated tape's read. -/
theorem simRead_flag_eq {sim utm : Tape} (h : VShift sim utm)
    (hwf : sim.WFCells) :
    simRead (decide (sim.head = 0)) utm.read = sim.read := by
  by_cases hz : sim.head = 0
  · rw [simRead, decide_eq_true hz, if_pos rfl, Tape.read, hz]
    exact hwf.1.symm
  · rw [simRead, decide_eq_false hz, if_neg Bool.false_ne_true]
    exact h.read_eq (by omega)

/-- Every entry produced by `parseEntry` has an in-range target, so the
    interpreter's `min`-clamp is the identity on it. -/
theorem parseEntry_q'_lt {w : ℕ} {seg : List Γw} {e : DescEntry}
    (hp : parseEntry w seg = some e) : e.act.q' < 2 ^ w := by
  unfold parseEntry at hp
  dsimp only at hp
  by_cases hlen : (seg.filterMap symBit?).length < 2 * w + 16
  · rw [if_pos hlen] at hp
    exact absurd hp (by simp)
  · rw [if_neg hlen] at hp
    simp only [Option.some.injEq] at hp
    subst hp
    dsimp only
    exact lt_of_lt_of_le (Nat.fromBits_lt_pow_length _)
      (Nat.pow_le_pow_right (by omega) (by rw [List.length_take]; omega))

end TM.UTMBody
