import Complexitylib.Models.TuringMachine.UTM.Desc
import Complexitylib.Models.TuringMachine.UTM.VTape
import Complexitylib.Models.TuringMachine.Hoare.Defs
import Complexitylib.Models.TuringMachine.Combinators.Internal.Generic
import Complexitylib.Classes.Pairing

/-!
# UTM initialization machine

`initTM : TM 6` is the first phase of the universal Turing machine
(`docs/UTM-design.md`). On input `pair α x` it:

1. **parses the α-region** of the input (α's bits doubled, terminated by the
   separator `01`), translating each 2-bit group into one desc symbol
   (`symOfPair`) written onto the desc tape (work tape 4);
2. **copies `x`** onto the virtual input tape (work tape 0) shifted one cell
   right (the +1-shift representation: work-0 cell 1 stays `□`, `x[i]` goes
   to cell `i + 2`);
3. **copies the first desc field** (the `qstart` field, i.e. the symbols
   before the first `□`) onto the state tape (work tape 3);
4. **parks** all work-tape heads at cell 1 and halts, leaving the output
   tape untouched.

The specification is `initTM_hoareTime`. Malformed inputs (a `10` cell pair
or a blank in the middle of a 2-cell group in the α-region) make the machine
halt immediately; the specification only covers well-formed inputs.
-/

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- State type
-- ════════════════════════════════════════════════════════════════════════

/-- Control states of `initTM`.

* `start` — the forced first step (every head bounces off `▷` to cell 1);
* `readFst pending` — phase 1, at the first cell of a 2-cell input group;
  `pending` holds an α-bit waiting for its partner (desc symbols are built
  from *two* α-bits);
* `readSnd fst pending` — phase 1, at the second cell of a 2-cell group whose
  first cell held the bit `fst`;
* `copyX` — phase 2, copying `x` to work tape 0 (shifted);
* `rewindDesc` — phase 3, rewinding the desc tape (work 4) to cell 1;
* `copyField` — phase 3, copying the `qstart` field of the desc tape onto
  the state tape (work 3);
* `rewindDesc2`, `rewindState`, `rewindV0` — final rewinds of work tapes
  4, 3, 0;
* `done` — halt. -/
inductive InitQ where
  | start
  | readFst (pending : Option Bool)
  | readSnd (fst : Bool) (pending : Option Bool)
  | copyX
  | rewindDesc
  | copyField
  | rewindDesc2
  | rewindState
  | rewindV0
  | done
  deriving DecidableEq

instance : Fintype InitQ where
  elems := {.start, .readFst none, .readFst (some false), .readFst (some true),
    .readSnd false none, .readSnd false (some false), .readSnd false (some true),
    .readSnd true none, .readSnd true (some false), .readSnd true (some true),
    .copyX, .rewindDesc, .copyField, .rewindDesc2, .rewindState, .rewindV0, .done}
  complete := fun q => by
    match q with
    | .start | .copyX | .rewindDesc | .copyField | .rewindDesc2
    | .rewindState | .rewindV0 | .done => simp
    | .readFst none | .readFst (some false) | .readFst (some true) => simp
    | .readSnd false none | .readSnd false (some false) | .readSnd false (some true)
    | .readSnd true none | .readSnd true (some false) | .readSnd true (some true) => simp

-- ════════════════════════════════════════════════════════════════════════
-- The machine
-- ════════════════════════════════════════════════════════════════════════

/-- One step of a work-tape rewind: move the head of work tape `idx` left
    until it reads `▷`, then bounce right to cell 1 and enter `qnext`.
    All other tapes idle. -/
private def rewindStep (idx : Fin 6) (qloop qnext : InitQ)
    (iHead : Γ) (wHeads : Fin 6 → Γ) (oHead : Γ) :
    InitQ × (Fin 6 → Γw) × Γw × Dir3 × (Fin 6 → Dir3) × Dir3 :=
  if wHeads idx = Γ.start then
    (qnext, fun i => readBackWrite (wHeads i), readBackWrite oHead,
     idleDir iHead, fun i => if i = idx then Dir3.right else idleDir (wHeads i),
     idleDir oHead)
  else
    (qloop, fun i => readBackWrite (wHeads i), readBackWrite oHead,
     idleDir iHead, fun i => if i = idx then Dir3.left else idleDir (wHeads i),
     idleDir oHead)

/-- The UTM initialization machine. See the module docstring and
    `docs/UTM-design.md` for the phase structure. -/
def initTM : TM 6 where
  Q := InitQ
  qstart := .start
  qhalt := .done
  δ := fun q iHead wHeads oHead =>
    match q with
    | .start =>
        (.readFst none, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .readFst pending =>
        match iHead with
        | .zero =>
            (.readSnd false pending, fun i => readBackWrite (wHeads i),
             readBackWrite oHead, Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | .one =>
            (.readSnd true pending, fun i => readBackWrite (wHeads i),
             readBackWrite oHead, Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | .blank =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.stay, fun i => idleDir (wHeads i), idleDir oHead)
        | .start =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .readSnd fst pending =>
        match iHead, fst with
        | .zero, false =>
            -- α-bit `false`
            match pending with
            | none =>
                (.readFst (some false), fun i => readBackWrite (wHeads i),
                 readBackWrite oHead, Dir3.right,
                 fun i => idleDir (wHeads i), idleDir oHead)
            | some b₁ =>
                (.readFst none,
                 fun i => if i = 4 then symOfPair b₁ false else readBackWrite (wHeads i),
                 readBackWrite oHead, Dir3.right,
                 fun i => if i = 4 then Dir3.right else idleDir (wHeads i), idleDir oHead)
        | .one, true =>
            -- α-bit `true`
            match pending with
            | none =>
                (.readFst (some true), fun i => readBackWrite (wHeads i),
                 readBackWrite oHead, Dir3.right,
                 fun i => idleDir (wHeads i), idleDir oHead)
            | some b₁ =>
                (.readFst none,
                 fun i => if i = 4 then symOfPair b₁ true else readBackWrite (wHeads i),
                 readBackWrite oHead, Dir3.right,
                 fun i => if i = 4 then Dir3.right else idleDir (wHeads i), idleDir oHead)
        | .one, false =>
            -- separator `01`: enter phase 2, advancing work 0 from cell 1 to 2
            (.copyX, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.right, fun i => if i = 0 then Dir3.right else idleDir (wHeads i),
             idleDir oHead)
        | .zero, true =>
            -- `10`: malformed
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.stay, fun i => idleDir (wHeads i), idleDir oHead)
        | .blank, _ =>
            -- blank mid-group: malformed
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.stay, fun i => idleDir (wHeads i), idleDir oHead)
        | .start, _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .copyX =>
        match iHead with
        | .zero =>
            (.copyX, fun i => if i = 0 then Γw.zero else readBackWrite (wHeads i),
             readBackWrite oHead, Dir3.right,
             fun i => if i = 0 then Dir3.right else idleDir (wHeads i), idleDir oHead)
        | .one =>
            (.copyX, fun i => if i = 0 then Γw.one else readBackWrite (wHeads i),
             readBackWrite oHead, Dir3.right,
             fun i => if i = 0 then Dir3.right else idleDir (wHeads i), idleDir oHead)
        | .blank =>
            (.rewindDesc, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.stay, fun i => idleDir (wHeads i), idleDir oHead)
        | .start =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .rewindDesc => rewindStep 4 .rewindDesc .copyField iHead wHeads oHead
    | .copyField =>
        match wHeads 4 with
        | .zero =>
            (.copyField, fun i => if i = 3 then Γw.zero else readBackWrite (wHeads i),
             readBackWrite oHead, idleDir iHead,
             fun i => if i = 3 then Dir3.right else if i = 4 then Dir3.right
                      else idleDir (wHeads i),
             idleDir oHead)
        | .one =>
            (.copyField, fun i => if i = 3 then Γw.one else readBackWrite (wHeads i),
             readBackWrite oHead, idleDir iHead,
             fun i => if i = 3 then Dir3.right else if i = 4 then Dir3.right
                      else idleDir (wHeads i),
             idleDir oHead)
        | .blank =>
            (.rewindDesc2, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        | .start =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
             idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rewindDesc2 => rewindStep 4 .rewindDesc2 .rewindState iHead wHeads oHead
    | .rewindState => rewindStep 3 .rewindState .rewindV0 iHead wHeads oHead
    | .rewindV0 => rewindStep 0 .rewindV0 .done iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro q iHead wHeads oHead
    have hrw : ∀ (idx : Fin 6) (qloop qnext : InitQ),
        let (_, _, _, inDir, workDirs, outDir) :=
          rewindStep idx qloop qnext iHead wHeads oHead
        (iHead = Γ.start → inDir = Dir3.right) ∧
        (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
        (oHead = Γ.start → outDir = Dir3.right) := by
      intro idx qloop qnext
      by_cases hs : wHeads idx = Γ.start
      · simp only [rewindStep, hs, ↓reduceIte]
        refine ⟨idleDir_right_of_start, fun i hwi => ?_, idleDir_right_of_start⟩
        split
        · rfl
        · exact idleDir_right_of_start hwi
      · simp only [rewindStep, hs, ↓reduceIte]
        refine ⟨idleDir_right_of_start, fun i hwi => ?_, idleDir_right_of_start⟩
        split
        · next heq => subst heq; exact absurd hwi hs
        · exact idleDir_right_of_start hwi
    match q with
    | .start =>
        exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .readFst p =>
        cases iHead with
        | zero => exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | one => exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | blank => exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | start => exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .readSnd f p =>
        match iHead, f with
        | .zero, false =>
            match p with
            | none =>
                exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
            | some b₁ =>
                refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
                dsimp only; split
                · rfl
                · exact idleDir_right_of_start hwi
        | .one, true =>
            match p with
            | none =>
                exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
            | some b₁ =>
                refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
                dsimp only; split
                · rfl
                · exact idleDir_right_of_start hwi
        | .one, false =>
            refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · exact idleDir_right_of_start hwi
        | .zero, true =>
            exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | .blank, _ =>
            exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | .start, _ =>
            exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .copyX =>
        cases iHead with
        | zero =>
            refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · exact idleDir_right_of_start hwi
        | one =>
            refine ⟨fun _ => rfl, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · exact idleDir_right_of_start hwi
        | blank => exact ⟨nofun, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
        | start => exact ⟨fun _ => rfl, fun i => idleDir_right_of_start, idleDir_right_of_start⟩
    | .copyField =>
        cases hw4 : wHeads 4 with
        | zero =>
            refine ⟨idleDir_right_of_start, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · split
              · rfl
              · exact idleDir_right_of_start hwi
        | one =>
            refine ⟨idleDir_right_of_start, fun i hwi => ?_, idleDir_right_of_start⟩
            dsimp only; split
            · rfl
            · split
              · rfl
              · exact idleDir_right_of_start hwi
        | blank =>
            exact ⟨idleDir_right_of_start, fun i => idleDir_right_of_start,
                   idleDir_right_of_start⟩
        | start =>
            exact ⟨idleDir_right_of_start, fun i => idleDir_right_of_start,
                   idleDir_right_of_start⟩
    | .rewindDesc => exact hrw 4 .rewindDesc .copyField
    | .rewindDesc2 => exact hrw 4 .rewindDesc2 .rewindState
    | .rewindState => exact hrw 3 .rewindState .rewindV0
    | .rewindV0 => exact hrw 0 .rewindV0 .done
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

-- ════════════════════════════════════════════════════════════════════════
-- Tape helpers
-- ════════════════════════════════════════════════════════════════════════

/-- An idle tape (readback write, idle direction) is unchanged, provided it
    is not reading `▷` and its head is off cell 0. -/
private theorem tape_idle_preserve (t : Tape) (hns : t.read ≠ Γ.start)
    (hh : 1 ≤ t.head) :
    t.writeAndMove (readBackWrite t.read).toΓ (idleDir t.read) = t := by
  simp only [Tape.writeAndMove, idleDir, hns, ↓reduceIte, Tape.move, Tape.write]
  split
  · omega
  · simp only [Tape.read] at hns ⊢
    rw [readBackWrite_toΓ_eq hns, Function.update_eq_self]

/-- `HoldsExact` depends only on the cells. -/
private theorem holdsExact_of_cells_eq {t t' : Tape} {l : List Γw}
    (h : t.HoldsExact l) (he : t'.cells = t.cells) : t'.HoldsExact l :=
  ⟨by rw [he]; exact h.1, fun i => by rw [he]; exact h.2 i⟩

/-- Writing a symbol at the frontier of a `HoldsExact` tape and moving right
    appends the symbol and keeps the head at the (new) frontier. -/
private theorem holdsExact_push {t : Tape} {l : List Γw} (h : t.HoldsExact l)
    (hh : t.head = l.length + 1) (s : Γw) :
    ((t.write s.toΓ).move .right).HoldsExact (l ++ [s]) ∧
    ((t.write s.toΓ).move .right).head = (l ++ [s]).length + 1 := by
  have hw : t.write s.toΓ = { t with cells := Function.update t.cells t.head s.toΓ } := by
    rw [Tape.write, if_neg (by omega)]
  refine ⟨⟨?_, fun i => ?_⟩, ?_⟩
  · show (Tape.move _ .right).cells 0 = Γ.start
    rw [tape_move_cells, hw]
    dsimp only
    rw [Function.update_of_ne (by omega)]
    exact h.1
  · show (Tape.move _ .right).cells (i + 1) = _
    rw [tape_move_cells, hw]
    dsimp only
    by_cases hi : i = l.length
    · subst hi
      rw [show l.length + 1 = t.head from hh.symm, Function.update_self]
      rw [dif_pos (by simp)]
      simp
    · rw [Function.update_of_ne (by omega)]
      rw [h.2 i]
      by_cases hlt : i < l.length
      · rw [dif_pos hlt, dif_pos (by simp; omega)]
        rw [List.getElem_append_left hlt]
      · rw [dif_neg hlt, dif_neg (by simp; omega)]
  · simp [Tape.move, tape_write_head, hh]

/-- Cells of the empty initial tape beyond cell 0 are blank. -/
private theorem initTape_nil_cells_succ (j : ℕ) :
    (initTape []).cells (j + 1) = Γ.blank := by
  simp [initTape]

private theorem bitSym_toΓ (b : Bool) : (bitSym b).toΓ = Γ.ofBool b := by
  cases b <;> rfl

/-- The first field of a symbol string is no longer than the string. -/
private theorem takeField_fst_length : ∀ l : List Γw, (takeField l).1.length ≤ l.length
  | [] => le_refl _
  | .blank :: rest => by simp [takeField]
  | .zero :: rest => by
      simpa [takeField] using takeField_fst_length rest
  | .one :: rest => by
      simpa [takeField] using takeField_fst_length rest

/-- Doubling every bit doubles the length. -/
private theorem dbl_length : ∀ l : List Bool, (l.flatMap fun b => [b, b]).length = 2 * l.length
  | [] => rfl
  | b :: rest => by
      simp only [List.flatMap_cons, List.length_append, dbl_length rest, List.length_cons,
        List.length_nil]
      omega

-- ════════════════════════════════════════════════════════════════════════
-- Input-suffix tracking
-- ════════════════════════════════════════════════════════════════════════

/-- The input tape holds the bits `l` (as `Γ.ofBool` symbols) from cell `k`
    on, followed by blanks. -/
private def InpSfx (t : Tape) (k : ℕ) (l : List Bool) : Prop :=
  ∀ j : ℕ, t.cells (k + j) = ((l[j]?).map Γ.ofBool).getD Γ.blank

private theorem inpSfx_head {t : Tape} {k : ℕ} {b : Bool} {l : List Bool}
    (h : InpSfx t k (b :: l)) : t.cells k = Γ.ofBool b := by
  have := h 0; simpa using this

private theorem inpSfx_tail {t : Tape} {k : ℕ} {b : Bool} {l : List Bool}
    (h : InpSfx t k (b :: l)) : InpSfx t (k + 1) l := by
  intro j
  have := h (j + 1)
  rw [show k + (j + 1) = k + 1 + j by omega] at this
  simpa using this

private theorem inpSfx_nil {t : Tape} {k : ℕ} (h : InpSfx t k []) :
    t.cells k = Γ.blank := by
  have := h 0; simpa using this

private theorem inpSfx_of_cells_eq {t t' : Tape} {k : ℕ} {l : List Bool}
    (h : InpSfx t k l) (he : t'.cells = t.cells) : InpSfx t' k l := by
  intro j; rw [he]; exact h j

private theorem inpSfx_initTape (l : List Bool) :
    InpSfx (initTape (l.map Γ.ofBool)) 1 l := by
  intro j
  show (if 1 + j = 0 then Γ.start else ((l.map Γ.ofBool)[1 + j - 1]?).getD Γ.blank) = _
  rw [if_neg (by omega), show 1 + j - 1 = j by omega, List.getElem?_map]

-- ════════════════════════════════════════════════════════════════════════
-- Single-step lemmas
-- ════════════════════════════════════════════════════════════════════════

/-- The first step: every head bounces off `▷` from cell 0 to cell 1. -/
private theorem step_start {c : Cfg 6 initTM.Q}
    (hst : c.state = InitQ.start)
    (hih : c.input.head = 0)
    (hwh : ∀ i, (c.work i).head = 0) (hwc : ∀ i, (c.work i).cells 0 = Γ.start)
    (hoh : c.output.head = 0) (hoc : c.output.cells 0 = Γ.start) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readFst none ∧
      c'.input.cells = c.input.cells ∧ c'.input.head = 1 ∧
      (∀ i, (c'.work i).cells = (c.work i).cells ∧ (c'.work i).head = 1) ∧
      c'.output.cells = c.output.cells ∧ c'.output.head = 1 := by
  have hwr : ∀ i, (c.work i).read = Γ.start := fun i => by
    rw [Tape.read, hwh i]; exact hwc i
  have hor : c.output.read = Γ.start := by rw [Tape.read, hoh]; exact hoc
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte]
  refine ⟨_, rfl, rfl, tape_move_cells _ _, by simp [Tape.move, hih], ?_, ?_, ?_⟩
  · intro i
    refine ⟨tape_readBackWrite_preserves _ _ (Or.inl (hwh i)), ?_⟩
    simp [Tape.writeAndMove, Tape.move, idleDir, hwr i, tape_write_head, hwh i]
  · exact tape_readBackWrite_preserves _ _ (Or.inl hoh)
  · simp [Tape.writeAndMove, Tape.move, idleDir, hor, tape_write_head, hoh]

/-- Phase 1: the first cell of a 2-cell group holds the bit `b`. -/
private theorem step_readFst {c : Cfg 6 initTM.Q} {b : Bool} {p : Option Bool}
    (hst : c.state = InitQ.readFst p)
    (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readSnd b p ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  cases b
  all_goals
    simp only [Γ.ofBool] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, tape_move_cells _ _, by simp [Tape.move], ?_,
      tape_idle_preserve _ ho hoh⟩
    funext i
    exact tape_idle_preserve _ (hw i).1 (hw i).2

/-- Phase 1: second cell of a group confirming the bit `b`, no pending bit. -/
private theorem step_readSnd_nopend {c : Cfg 6 initTM.Q} {b : Bool}
    (hst : c.state = InitQ.readSnd b none)
    (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readFst (some b) ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      c'.work = c.work ∧
      c'.output = c.output := by
  cases b
  all_goals
    simp only [Γ.ofBool] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, tape_move_cells _ _, by simp [Tape.move], ?_,
      tape_idle_preserve _ ho hoh⟩
    funext i
    exact tape_idle_preserve _ (hw i).1 (hw i).2

/-- Phase 1: second cell of a group confirming the bit `b`, with a pending
    bit `b₁` — emit `symOfPair b₁ b` onto the desc tape (work 4). -/
private theorem step_readSnd_emit {c : Cfg 6 initTM.Q} {b b₁ : Bool}
    (hst : c.state = InitQ.readSnd b (some b₁))
    (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.readFst none ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      (∀ i, i ≠ (4 : Fin 6) → c'.work i = c.work i) ∧
      c'.work 4 = ((c.work 4).write (symOfPair b₁ b).toΓ).move .right ∧
      c'.output = c.output := by
  cases b
  all_goals
    simp only [Γ.ofBool] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, tape_move_cells _ _, by simp [Tape.move], ?_, ?_,
      tape_idle_preserve _ ho hoh⟩
    · intro i hi
      simp only [hi, ↓reduceIte]
      exact tape_idle_preserve _ (hw i).1 (hw i).2
    · simp only [↓reduceIte]

/-- Phase 1 → 2: the separator `01` — enter `copyX`, advancing work tape 0
    (from cell 1 to cell 2). A pending α-bit (odd `|α|`) is dropped. -/
private theorem step_readSnd_sep {c : Cfg 6 initTM.Q} {p : Option Bool}
    (hst : c.state = InitQ.readSnd false p)
    (hread : c.input.read = Γ.one)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.copyX ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      (∀ i, i ≠ (0 : Fin 6) → c'.work i = c.work i) ∧
      (c'.work 0).cells = (c.work 0).cells ∧
      (c'.work 0).head = (c.work 0).head + 1 ∧
      c'.output = c.output := by
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
  refine ⟨_, rfl, rfl, tape_move_cells _ _, by simp [Tape.move], ?_, ?_, ?_,
    tape_idle_preserve _ ho hoh⟩
  · intro i hi
    simp only [hi, ↓reduceIte]
    exact tape_idle_preserve _ (hw i).1 (hw i).2
  · simp only [↓reduceIte]
    exact tape_readBackWrite_preserves _ _ (Or.inr (hw 0).1)
  · simp only [↓reduceIte, Tape.writeAndMove, Tape.move, tape_write_head]

/-- Phase 2: copy one bit of `x` onto work tape 0. -/
private theorem step_copyX_bit {c : Cfg 6 initTM.Q} {b : Bool}
    (hst : c.state = InitQ.copyX)
    (hread : c.input.read = Γ.ofBool b)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.copyX ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = c.input.head + 1 ∧
      (∀ i, i ≠ (0 : Fin 6) → c'.work i = c.work i) ∧
      c'.work 0 = ((c.work 0).write (bitSym b).toΓ).move .right ∧
      c'.output = c.output := by
  cases b
  all_goals
    simp only [Γ.ofBool] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, tape_move_cells _ _, by simp [Tape.move], ?_, ?_,
      tape_idle_preserve _ ho hoh⟩
    · intro i hi
      simp only [hi, ↓reduceIte]
      exact tape_idle_preserve _ (hw i).1 (hw i).2
    · simp only [↓reduceIte]
      rfl

/-- Phase 2 → 3: `x` is exhausted (input reads blank) — start rewinding the
    desc tape. -/
private theorem step_copyX_blank {c : Cfg 6 initTM.Q}
    (hst : c.state = InitQ.copyX)
    (hread : c.input.read = Γ.blank)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.rewindDesc ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
  refine ⟨_, rfl, rfl, rfl, ?_, tape_idle_preserve _ ho hoh⟩
  funext i
  exact tape_idle_preserve _ (hw i).1 (hw i).2

/-- Phase 3: copy one field symbol (`0` or `1`) from the desc tape onto the
    state tape (work 3); both heads advance. -/
private theorem step_copyField_bit {c : Cfg 6 initTM.Q} {s : Γw}
    (hs : s = Γw.zero ∨ s = Γw.one)
    (hst : c.state = InitQ.copyField)
    (hread : (c.work 4).read = s.toΓ)
    (hi : c.input.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.copyField ∧
      c'.input = c.input ∧
      (∀ i, i ≠ (3 : Fin 6) → i ≠ 4 → c'.work i = c.work i) ∧
      c'.work 3 = ((c.work 3).write s.toΓ).move .right ∧
      (c'.work 4).cells = (c.work 4).cells ∧
      (c'.work 4).head = (c.work 4).head + 1 ∧
      c'.output = c.output := by
  rcases hs with rfl | rfl
  all_goals
    simp only [Γw.toΓ] at hread
    simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
    refine ⟨_, rfl, rfl, by simp [Tape.move, idleDir, hi], ?_, ?_, ?_, ?_,
      tape_idle_preserve _ ho hoh⟩
    · intro i hi3 hi4
      simp only [hi3, hi4, ↓reduceIte]
      exact tape_idle_preserve _ (hw i).1 (hw i).2
    · simp only [↓reduceIte]
    · simp only [show (4 : Fin 6) ≠ 3 by decide, ↓reduceIte]
      exact tape_readBackWrite_preserves _ _ (Or.inr (hw 4).1)
    · simp only [show (4 : Fin 6) ≠ 3 by decide, ↓reduceIte, Tape.writeAndMove,
        Tape.move, tape_write_head]

/-- Phase 3: the desc tape reads `□` — the field is over (the `□` is not
    copied); start the second desc rewind. -/
private theorem step_copyField_blank {c : Cfg 6 initTM.Q}
    (hst : c.state = InitQ.copyField)
    (hread : (c.work 4).read = Γ.blank)
    (hi : c.input.read ≠ Γ.start)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (ho : c.output.read ≠ Γ.start) (hoh : 1 ≤ c.output.head) :
    ∃ c', initTM.step c = some c' ∧
      c'.state = InitQ.rewindDesc2 ∧
      c'.input = c.input ∧ c'.work = c.work ∧ c'.output = c.output := by
  simp only [TM.step, hst, initTM, reduceCtorEq, ↓reduceIte, hread]
  refine ⟨_, rfl, rfl, by simp [Tape.move, idleDir, hi], ?_,
    tape_idle_preserve _ ho hoh⟩
  funext i
  exact tape_idle_preserve _ (hw i).1 (hw i).2

-- ════════════════════════════════════════════════════════════════════════
-- Rewind loop
-- ════════════════════════════════════════════════════════════════════════

/-- Generic rewind loop for the four rewind states: from a rewind state with
    the head of work tape `idx` at `h`, reach `qnext` with that head at cell
    1 in `h + 1` steps, preserving all tape contents. -/
private theorem rewind_loop {idx : Fin 6} {qloop qnext : InitQ}
    (hδ : ∀ iH wH oH, initTM.δ qloop iH wH oH = rewindStep idx qloop qnext iH wH oH)
    (hqne : qloop ≠ initTM.qhalt) :
    ∀ (h : ℕ) (c : Cfg 6 initTM.Q),
      c.state = qloop →
      (c.work idx).head = h →
      (c.work idx).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work idx).cells j ≠ Γ.start) →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ idx → (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) →
      c.output.read ≠ Γ.start → 1 ≤ c.output.head →
      ∃ c', initTM.reachesIn (h + 1) c c' ∧
        c'.state = qnext ∧
        (c'.work idx).head = 1 ∧
        (c'.work idx).cells = (c.work idx).cells ∧
        (∀ i, i ≠ idx → c'.work i = c.work i) ∧
        c'.input = c.input ∧
        c'.output = c.output := by
  intro h
  induction h with
  | zero =>
    intro c hst hh hc0 hns hi hwo ho hoh
    have hne' : ¬(c.state = initTM.qhalt) := by rw [hst]; exact hqne
    have hread : (c.work idx).read = Γ.start := by rw [Tape.read, hh]; exact hc0
    obtain ⟨c₁, hstep, hst₁, hhd₁, hcl₁, hfr₁, hin₁, hout₁⟩ :
        ∃ c₁, initTM.step c = some c₁ ∧ c₁.state = qnext ∧
          (c₁.work idx).head = 1 ∧ (c₁.work idx).cells = (c.work idx).cells ∧
          (∀ i, i ≠ idx → c₁.work i = c.work i) ∧
          c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hne', ↓reduceIte, hst, hδ, rewindStep, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, by simp [Tape.move, idleDir, hi],
        tape_idle_preserve _ ho hoh⟩
      · simp only [↓reduceIte, Tape.writeAndMove, Tape.move, tape_write_head, hh]
      · simp only [↓reduceIte]
        exact tape_readBackWrite_preserves _ _ (Or.inl hh)
      · intro i hi'
        simp only [hi', ↓reduceIte]
        exact tape_idle_preserve _ (hwo i hi').1 (hwo i hi').2
    exact ⟨c₁, .step hstep .zero, hst₁, hhd₁, hcl₁, hfr₁, hin₁, hout₁⟩
  | succ h ih =>
    intro c hst hh hc0 hns hi hwo ho hoh
    have hne' : ¬(c.state = initTM.qhalt) := by rw [hst]; exact hqne
    have hread : (c.work idx).read ≠ Γ.start := by
      rw [Tape.read, hh]; exact hns (h + 1) (by omega)
    obtain ⟨c₁, hstep, hst₁, hhd₁, hcl₁, hfr₁, hin₁, hout₁⟩ :
        ∃ c₁, initTM.step c = some c₁ ∧ c₁.state = qloop ∧
          (c₁.work idx).head = h ∧ (c₁.work idx).cells = (c.work idx).cells ∧
          (∀ i, i ≠ idx → c₁.work i = c.work i) ∧
          c₁.input = c.input ∧ c₁.output = c.output := by
      simp only [TM.step, hne', ↓reduceIte, hst, hδ, rewindStep, hread]
      refine ⟨_, rfl, rfl, ?_, ?_, ?_, by simp [Tape.move, idleDir, hi],
        tape_idle_preserve _ ho hoh⟩
      · simp only [↓reduceIte, Tape.writeAndMove, Tape.move, tape_write_head, hh]
      · simp only [↓reduceIte]
        exact tape_readBackWrite_preserves _ _ (Or.inr hread)
      · intro i hi'
        simp only [hi', ↓reduceIte]
        exact tape_idle_preserve _ (hwo i hi').1 (hwo i hi').2
    obtain ⟨c', hreach, hst', hhd', hcl', hfr', hin', hout'⟩ :=
      ih c₁ hst₁ hhd₁ (by rw [hcl₁]; exact hc0) (fun j hj => by rw [hcl₁]; exact hns j hj)
        (by rw [hin₁]; exact hi)
        (fun i hi' => by rw [hfr₁ i hi']; exact hwo i hi')
        (by rw [hout₁]; exact ho) (by rw [hout₁]; exact hoh)
    exact ⟨c', .step hstep hreach, hst', hhd', by rw [hcl', hcl₁],
      fun i hi' => by rw [hfr' i hi', hfr₁ i hi'], by rw [hin', hin₁],
      by rw [hout', hout₁]⟩

end TM
