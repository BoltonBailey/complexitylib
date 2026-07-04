import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
import Complexitylib.Models.TuringMachine.UTM.VTape
import Complexitylib.Models.TuringMachine.UTM.Desc

/-!
# The UTM halt test machine

`haltTestTM : TM 6` compares the state tape (work tape 3) against the
description's second field (the `qhalt` field of the desc tape, work tape 4)
and writes the verdict to output cell 1: `Γ.one` on match, `Γ.zero` on
mismatch. Both tape heads are rewound to cell 1 before halting.

Phases (from `qstart = .skip`):

* **A (skip)** — move the desc head right past the first field and its
  separator (`□`), landing on the first cell of the `qhalt` field;
* **B (compare)** — lockstep compare of state head vs desc head: both `□`
  simultaneously ⇒ match; any difference ⇒ mismatch;
* **C (verdict)** — one step: write `Γ.one`/`Γ.zero` at output cell 1
  (output head stays at 1);
* **D (rewind)** — rewind the state head to cell 1, then the desc head to
  cell 1, then halt.

The machine writes `readBackWrite` on every work tape at every step, so no
work-tape cell is ever changed; tapes 3 and 4 are restored *exactly* (same
head, same cells), and all other tapes are untouched.

## Main results

- `TM.haltTestTM_hoareTime` — full HoareTime specification with ghost
  initial tapes, verdict `Γ.one` iff `stSyms = (takeField (takeField dSyms).2).1`,
  in time `2·|dSyms| + 2·|stSyms| + 12`.

`takeField` connection: the desc tape holds `dSyms` (`Tape.HoldsExact`);
cells beyond the content read `Γ.blank`, indistinguishable from an
in-content `Γw.blank` — and `takeField` semantics agrees, by design. The
`stSyms` blank-freeness hypothesis is required: a `□` inside `stSyms` would
truncate the machine's comparison at that point while `stSyms` as a list
extends beyond it (and `takeField` fields are always blank-free). The UTM
state tape holds bit symbols only, so this is no restriction in use.
-/

-- ════════════════════════════════════════════════════════════════════════
-- takeField structural lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- The first field produced by `takeField` is blank-free. -/
theorem takeField_fst_ne_blank : ∀ (l : List Γw), ∀ s ∈ (takeField l).1, s ≠ Γw.blank
  | [] => by simp [takeField]
  | .blank :: _ => by simp [takeField]
  | .zero :: rest => by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · simp
    · exact takeField_fst_ne_blank rest s hs
  | .one :: rest => by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · simp
    · exact takeField_fst_ne_blank rest s hs

/-- `takeField` decomposition: either the input splits as
    `field ++ □ :: rest`, or it contains no separator and the field is the
    whole input. -/
theorem takeField_structure : ∀ (l : List Γw),
    l = (takeField l).1 ++ Γw.blank :: (takeField l).2 ∨
    ((takeField l).1 = l ∧ (takeField l).2 = [])
  | [] => Or.inr ⟨rfl, rfl⟩
  | .blank :: _ => Or.inl rfl
  | .zero :: rest => by
    rcases takeField_structure rest with h | ⟨h1, h2⟩
    · exact Or.inl (by simpa [takeField] using h)
    · exact Or.inr ⟨by simp [takeField, h1], by simpa [takeField] using h2⟩
  | .one :: rest => by
    rcases takeField_structure rest with h | ⟨h1, h2⟩
    · exact Or.inl (by simpa [takeField] using h)
    · exact Or.inr ⟨by simp [takeField, h1], by simpa [takeField] using h2⟩

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Γw.toΓ helper lemmas
-- ════════════════════════════════════════════════════════════════════════

private theorem toΓ_ne_start (s : Γw) : s.toΓ ≠ Γ.start := by
  cases s <;> simp [Γw.toΓ]

private theorem toΓ_ne_blank {s : Γw} (h : s ≠ Γw.blank) : s.toΓ ≠ Γ.blank := by
  cases s <;> simp_all [Γw.toΓ]

private theorem toΓ_inj {a b : Γw} (h : a.toΓ = b.toΓ) : a = b := by
  cases a <;> cases b <;> simp_all [Γw.toΓ]

-- ════════════════════════════════════════════════════════════════════════
-- The machine
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `haltTestTM`. -/
inductive HaltTestPhase where
  | skip | compare | writeOne | writeZero | rewindSt | rewindD | done
  deriving DecidableEq

instance : Fintype HaltTestPhase where
  elems := {.skip, .compare, .writeOne, .writeZero, .rewindSt, .rewindD, .done}
  complete := fun x => by cases x <;> simp

/-- The UTM halt test: skip the first desc field, compare the state tape
    (work tape 3) with the second desc field (work tape 4), write the
    verdict to output cell 1, rewind both heads to cell 1, halt. -/
def haltTestTM : TM 6 where
  Q := HaltTestPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
      ((if wHeads 4 = Γ.blank then HaltTestPhase.compare else .skip),
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = 4 then Dir3.right else idleDir (wHeads i),
       idleDir oHead)
    | .compare =>
      if wHeads 3 = Γ.blank ∧ wHeads 4 = Γ.blank then
        (HaltTestPhase.writeOne, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      else if wHeads 3 = wHeads 4 then
        (HaltTestPhase.compare, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 3 then Dir3.right else if i = 4 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (HaltTestPhase.writeZero, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .writeOne =>
      (HaltTestPhase.rewindSt, fun i => readBackWrite (wHeads i), Γw.one,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .writeZero =>
      (HaltTestPhase.rewindSt, fun i => readBackWrite (wHeads i), Γw.zero,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rewindSt =>
      ((if wHeads 3 = Γ.start then HaltTestPhase.rewindD else .rewindSt),
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = 3 then (if wHeads 3 = Γ.start then Dir3.right else Dir3.left)
                else idleDir (wHeads i),
       idleDir oHead)
    | .rewindD =>
      ((if wHeads 4 = Γ.start then HaltTestPhase.done else .rewindD),
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead,
       fun i => if i = 4 then (if wHeads 4 = Γ.start then Dir3.right else Dir3.left)
                else idleDir (wHeads i),
       idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; dsimp only []; split
      · rfl
      · exact idleDir_right_of_start hwi
    | .compare =>
      dsimp only []; split
      · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
               idleDir_right_of_start⟩
      · split
        · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
          intro i hwi; dsimp only []; split
          · rfl
          · split
            · rfl
            · exact idleDir_right_of_start hwi
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
                 idleDir_right_of_start⟩
    | .writeOne =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .writeZero =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
             idleDir_right_of_start⟩
    | .rewindSt =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; dsimp only []; split
      · rename_i heq; subst heq; rw [if_pos hwi]
      · exact idleDir_right_of_start hwi
    | .rewindD =>
      refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hwi; dsimp only []; split
      · rename_i heq; subst heq; rw [if_pos hwi]
      · exact idleDir_right_of_start hwi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Idle-tape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- A tape whose head is not on `▷` is fixed by an idle step, regardless of
    head position. -/
private theorem tape_idle_fix (t : Tape) (hne : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  rw [readBackWrite_toΓ_eq hne]
  show (t.write t.read).move (idleDir t.read) = t
  simp only [idleDir, hne, ↓reduceIte]
  show (t.write (t.cells t.head)).move .stay = t
  simp only [Tape.write, Tape.move]
  split
  · rfl
  · simp only [Function.update_eq_self]

/-- The input tape is fixed by an idle move when not reading `▷`. -/
private theorem input_idle_fix (t : Tape) (hne : t.read ≠ Γ.start) :
    t.move (idleDir t.read) = t := by
  simp only [idleDir, hne, ↓reduceIte, Tape.move]

/-- Two tapes with the same head and cells are equal. -/
private theorem tape_eq_of_parts {t t' : Tape} (hh : t.head = t'.head)
    (hc : t.cells = t'.cells) : t = t' := by
  cases t; cases t'; simp_all

-- ════════════════════════════════════════════════════════════════════════
-- HoldsExact + takeField: cell layout of the first two fields
-- ════════════════════════════════════════════════════════════════════════

private theorem getElem_append_cons_self {α : Type _} {l₁ l₂ : List α} {a : α} :
    (l₁ ++ a :: l₂)[l₁.length]'(by simp) = a := by
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

private theorem getElem_append_cons_right {α : Type _} {l₁ l₂ : List α} {a : α} {k : ℕ}
    (hk : k < l₂.length) :
    (l₁ ++ a :: l₂)[l₁.length + 1 + k]'(by simp; omega) = l₂[k] := by
  rw [List.getElem_append_right (by omega)]
  simp only [show l₁.length + 1 + k - l₁.length = k + 1 by omega,
    List.getElem_cons_succ]

/-- The first two fields of `l` sit inside `l` in one of three shapes:
    both separators present, only the first separator present, or no
    separator at all. -/
private theorem two_fields_decomp (l : List Γw) :
    (∃ tail, l = (takeField l).1 ++ Γw.blank ::
      ((takeField (takeField l).2).1 ++ Γw.blank :: tail)) ∨
    l = (takeField l).1 ++ Γw.blank :: (takeField (takeField l).2).1 ∨
    ((takeField l).1 = l ∧ (takeField (takeField l).2).1 = []) := by
  rcases takeField_structure l with hdec | ⟨h1, h2⟩
  · rcases takeField_structure (takeField l).2 with hdec2 | ⟨h21, _⟩
    · exact Or.inl ⟨(takeField (takeField l).2).2, by rw [← hdec2]; exact hdec⟩
    · exact Or.inr (Or.inl (by rw [h21]; exact hdec))
  · exact Or.inr (Or.inr ⟨h1, by rw [h2]⟩)

/-- Cell layout of a tape holding `l`, in terms of its first two fields
    `f₁ = (takeField l).1` and `f₂ = (takeField (takeField l).2).1`:
    the first field occupies cells `1..|f₁|`, cell `|f₁|+1` is blank, the
    second field occupies cells `|f₁|+2..|f₁|+|f₂|+1`, the cell after it is
    blank, and the two field lengths together are bounded by `|l|`. -/
private theorem holdsExact_two_fields {t : Tape} {l : List Γw} (h : t.HoldsExact l) :
    (∀ k, (hk : k < (takeField l).1.length) →
      t.cells (1 + k) = (((takeField l).1)[k]).toΓ) ∧
    t.cells (1 + (takeField l).1.length) = Γ.blank ∧
    (∀ k, (hk : k < (takeField (takeField l).2).1.length) →
      t.cells ((takeField l).1.length + 2 + k)
        = (((takeField (takeField l).2).1)[k]).toΓ) ∧
    t.cells ((takeField l).1.length + 2 + (takeField (takeField l).2).1.length)
      = Γ.blank ∧
    (takeField l).1.length + (takeField (takeField l).2).1.length ≤ l.length := by
  rcases two_fields_decomp l with ⟨tail, hdec⟩ | hdec | ⟨h1, h2⟩
  · have hlen := congrArg List.length hdec
    simp only [List.length_append, List.length_cons] at hlen
    refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_, by omega⟩
    · have := h.cells_lt (i := k) (by omega)
      rw [hdec, List.getElem_append_left hk] at this
      rw [Nat.add_comm]; exact this
    · have := h.cells_lt (i := (takeField l).1.length) (by omega)
      rw [hdec, getElem_append_cons_self] at this
      rw [Nat.add_comm]; exact this
    · have := h.cells_lt (i := (takeField l).1.length + 1 + k) (by omega)
      rw [hdec, getElem_append_cons_right (by simp only [List.length_append,
        List.length_cons]; omega), List.getElem_append_left hk] at this
      rw [show (takeField l).1.length + 2 + k
        = (takeField l).1.length + 1 + k + 1 by omega]
      exact this
    · have := h.cells_lt
        (i := (takeField l).1.length + 1 + (takeField (takeField l).2).1.length)
        (by omega)
      rw [hdec, getElem_append_cons_right (by simp only [List.length_append,
        List.length_cons]; omega), getElem_append_cons_self] at this
      rw [show (takeField l).1.length + 2 + (takeField (takeField l).2).1.length
        = (takeField l).1.length + 1 + (takeField (takeField l).2).1.length + 1
        by omega]
      exact this
  · have hlen := congrArg List.length hdec
    simp only [List.length_append, List.length_cons] at hlen
    refine ⟨fun k hk => ?_, ?_, fun k hk => ?_, ?_, by omega⟩
    · have := h.cells_lt (i := k) (by omega)
      rw [hdec, List.getElem_append_left hk] at this
      rw [Nat.add_comm]; exact this
    · have := h.cells_lt (i := (takeField l).1.length) (by omega)
      rw [hdec, getElem_append_cons_self] at this
      rw [Nat.add_comm]; exact this
    · have := h.cells_lt (i := (takeField l).1.length + 1 + k) (by omega)
      rw [hdec, getElem_append_cons_right (by omega)] at this
      rw [show (takeField l).1.length + 2 + k
        = (takeField l).1.length + 1 + k + 1 by omega]
      exact this
    · have := h.cells_ge
        (i := (takeField l).1.length + 1 + (takeField (takeField l).2).1.length)
        (by omega)
      rw [show (takeField l).1.length + 2 + (takeField (takeField l).2).1.length
        = (takeField l).1.length + 1 + (takeField (takeField l).2).1.length + 1
        by omega]
      exact this
  · have hlen : (takeField l).1.length = l.length := by rw [h1]
    refine ⟨fun k hk => ?_, ?_, fun k hk => by omega, ?_, by omega⟩
    · have := h.cells_lt (i := k) (by omega)
      rw [show l[k]'(by omega) = ((takeField l).1)[k]'hk by
        congr 1; exact h1.symm] at this
      rw [Nat.add_comm]; exact this
    · have := h.cells_ge (i := (takeField l).1.length) (by omega)
      rw [Nat.add_comm]; exact this
    · have := h.cells_ge
        (i := (takeField l).1.length + 1 + (takeField (takeField l).2).1.length)
        (by omega)
      rw [show (takeField l).1.length + 2 + (takeField (takeField l).2).1.length
        = (takeField l).1.length + 1 + (takeField (takeField l).2).1.length + 1
        by omega]
      exact this

end TM
