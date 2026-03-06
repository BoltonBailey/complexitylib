import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs

/-!
# Turing Machines (Arora-Barak style)

This file defines deterministic and nondeterministic Turing machines following
Arora and Barak's *Computational Complexity: A Modern Approach*.

## Main definitions

- `Γ` — the tape alphabet `{0, 1, □, ▷}` (read alphabet)
- `Γw` — the writable alphabet `{0, 1, □}` (write alphabet; `▷` cannot be written)
- `Dir3` — three-way tape head direction (left, right, stay)
- `Tape` — a one-sided infinite tape; cell 0 is leftmost and permanently `▷`
- `Cfg` — a machine configuration with named tapes (input, work, output)
- `TM` — a deterministic multi-tape Turing machine (AB Definition 1.1)
- `NTM` — a nondeterministic TM with two transition functions (AB Definition 2.1)
- `TM.stepRel`, `TM.reaches`, `TM.reachesIn` — deterministic step relation and reachability
- `NTM.trace` — execute an NTM for a fixed choice sequence (canonical NTM execution)
- `TM.Accepts`, `TM.AcceptsInTime` — deterministic acceptance
- `NTM.Accepts`, `NTM.AcceptsInTime` — nondeterministic acceptance (existential)
- `TM.DecidesInTime`, `NTM.DecidesInTime` — deciding a language within a time bound
- `NTM.acceptCount`, `NTM.acceptProb` — counting/probabilistic acceptance
- `TM.toNTM` — embed a DTM into an NTM

## Design notes

- **One-sided tapes**: `Tape` uses `head : ℕ` and `cells : ℕ → Γ`. Cell 0 is leftmost;
  moving left at position 0 is a no-op (`Nat` subtraction saturates), matching AB exactly.
- **Immutable cell 0**: `Tape.write` is a no-op when the head is at position 0, ensuring
  `▷` at cell 0 is permanent. Combined with `Γw` (which excludes `▷`), this guarantees `▷`
  appears only at cell 0 on every tape.
- **Read vs write alphabet**: The transition function reads `Γ = {0, 1, □, ▷}` but writes
  `Γw = {0, 1, □}`, structurally enforcing AB's rule that `δ` never writes `▷`.
- **Finite state**: `Q` carries `[Fintype Q]`, matching AB's requirement that Q is finite.
- **Output**: Read from cell 1 of the output tape (first cell after `▷`), matching AB's
  definition of machine output as the string written after `▷`.
- **Named tapes**: `Cfg` has `input`, `work`, `output` fields rather than `Fin k → Tape`,
  making the read-only/read-write distinction structural.
- **NTM execution**: Defined via `trace` (a fixed choice sequence), not a relational step.
-/

/-- The tape alphabet Γ = {0, 1, □, ▷} following Arora-Barak. -/
inductive Γ where
  | zero | one | blank | start
  deriving DecidableEq

instance : Inhabited Γ := ⟨Γ.blank⟩

/-- The writable alphabet Γw = {0, 1, □}. The start symbol `▷` cannot be written by a
    transition function — this is enforced structurally by using `Γw` in the output of `δ`. -/
inductive Γw where
  | zero | one | blank
  deriving DecidableEq

/-- Embed a writable symbol into the full alphabet. -/
@[simp] def Γw.toΓ : Γw → Γ
  | .zero => .zero
  | .one => .one
  | .blank => .blank

instance : Coe Γw Γ where coe := Γw.toΓ

/-- Convert a boolean to an alphabet symbol. -/
def Γ.ofBool : Bool → Γ
  | false => .zero
  | true => .one

/-- Three-way tape head direction: left, right, or stay. -/
inductive Dir3 where
  | left | right | stay
  deriving DecidableEq

/-- A one-sided infinite tape following Arora-Barak.
    Cell 0 is the leftmost cell and permanently contains `▷`. The head cannot move
    left of cell 0 (moving left at position 0 is a no-op via `Nat` subtraction).
    Writing at cell 0 is a no-op, preserving `▷`. -/
structure Tape where
  head : ℕ
  cells : ℕ → Γ

namespace Tape

/-- Read the symbol under the head. -/
def read (t : Tape) : Γ := t.cells t.head

/-- Write a symbol at the head position. Writing at cell 0 is a no-op,
    preserving the start symbol `▷`. -/
def write (t : Tape) (s : Γ) : Tape :=
  if t.head = 0 then t
  else { t with cells := Function.update t.cells t.head s }

/-- Move the head according to a three-way direction.
    Moving left at position 0 stays at 0 (`Nat` subtraction saturates). -/
def move (t : Tape) (d : Dir3) : Tape :=
  match d with
  | .left => { t with head := t.head - 1 }
  | .right => { t with head := t.head + 1 }
  | .stay => t

end Tape

/-- Initialize a tape: `▷` at cell 0, `contents` at cells 1, 2, ..., `□` elsewhere.
    Head starts at position 0 (on `▷`). -/
def initTape (contents : List Γ) : Tape where
  head := 0
  cells := fun i =>
    if i = 0 then Γ.start
    else (contents[i - 1]?).getD Γ.blank

/-- A language is a set of binary strings. -/
abbrev Language := Set (List Bool)

/-- A configuration of a Turing machine with `n` work tapes:
    a read-only input tape, `n` read-write work tapes, and a read-write output tape. -/
structure Cfg (n : ℕ) (Q : Type) where
  state : Q
  input : Tape
  work : Fin n → Tape
  output : Tape

/-- A deterministic Turing machine with `n` work tapes (Arora-Barak Definition 1.1).

    The machine has a read-only input tape, `n` read-write work tapes, and a read-write
    output tape. The transition function reads `Γ` from all tape heads but writes only
    `Γw` (excluding `▷`) to work and output tapes. `Q` is finite. -/
structure TM (n : ℕ) where
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  qstart : Q
  qhalt : Q
  δ : Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  δ_right_of_start : ∀ (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)

attribute [instance] TM.decEq TM.finQ

/-- A nondeterministic Turing machine with two transition functions (Arora-Barak Definition 2.1).

    The same structure is used for probabilistic TMs (AB Section 7.1) — only the acceptance
    criterion differs (existential for NTM, counting for PTM). `Q` is finite. -/
structure NTM (n : ℕ) where
  Q : Type
  [decEq : DecidableEq Q]
  [finQ : Fintype Q]
  qstart : Q
  qhalt : Q
  δ : Bool → Q → Γ → (Fin n → Γ) → Γ →
      Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3
  δ_right_of_start : ∀ (b : Bool) (q : Q) (iHead : Γ) (wHeads : Fin n → Γ) (oHead : Γ),
    let (_, _, _, inDir, workDirs, outDir) := δ b q iHead wHeads oHead
    (iHead = Γ.start → inDir = Dir3.right) ∧
    (∀ i, wHeads i = Γ.start → workDirs i = Dir3.right) ∧
    (oHead = Γ.start → outDir = Dir3.right)

attribute [instance] NTM.decEq NTM.finQ

namespace TM

variable {n : ℕ}

/-- Step a deterministic TM by one step. Returns `none` if halted. -/
def step (tm : TM n) (c : Cfg n tm.Q) : Option (Cfg n tm.Q) :=
  if c.state = tm.qhalt then none
  else
    let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
      tm.δ c.state c.input.read (fun i => (c.work i).read) c.output.read
    some
      { state := q'
        input := c.input.move inDir
        work := fun i => ((c.work i).write (workWrites i)).move (workDirs i)
        output := (c.output.write outWrite).move outDir }

/-- Initial configuration: input on the input tape, all tapes start with `▷`. -/
def initCfg (tm : TM n) (x : List Bool) : Cfg n tm.Q :=
  { state := tm.qstart
    input := initTape (x.map Γ.ofBool)
    work := fun _ => initTape []
    output := initTape [] }

/-- A configuration is halted when its state is `qhalt`. -/
def halted (tm : TM n) (c : Cfg n tm.Q) : Prop := c.state = tm.qhalt

/-- One-step relation for a deterministic TM. -/
def stepRel (tm : TM n) (c c' : Cfg n tm.Q) : Prop := tm.step c = some c'

/-- Reflexive-transitive closure of the step relation. -/
def reaches (tm : TM n) : Cfg n tm.Q → Cfg n tm.Q → Prop :=
  Relation.ReflTransGen tm.stepRel

/-- Reachability in exactly `t` steps. -/
inductive reachesIn (tm : TM n) : ℕ → Cfg n tm.Q → Cfg n tm.Q → Prop where
  | zero : reachesIn tm 0 c c
  | step : tm.step c = some c'' → reachesIn tm t c'' c' → reachesIn tm (t + 1) c c'

/-- DTM accepts `x`: reaches `qhalt` with output cell 1 (after `▷`) = `1`. -/
def Accepts (tm : TM n) (x : List Bool) : Prop :=
  ∃ c', tm.reaches (tm.initCfg x) c' ∧ tm.halted c' ∧ c'.output.cells 1 = Γ.one

/-- DTM accepts `x` within `T` steps. -/
def AcceptsInTime (tm : TM n) (x : List Bool) (T : ℕ) : Prop :=
  ∃ c' t, t ≤ T ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    c'.output.cells 1 = Γ.one

/-- DTM decides `L` within time bound `T(n)`: halts on all inputs within `T(|x|)` steps,
    accepting exactly the strings in `L`. -/
def DecidesInTime (tm : TM n) (L : Language) (T : ℕ → ℕ) : Prop :=
  ∀ x, ∃ c' t, t ≤ T x.length ∧ tm.reachesIn t (tm.initCfg x) c' ∧ tm.halted c' ∧
    (c'.output.cells 1 = Γ.one ↔ x ∈ L)

end TM

namespace NTM

variable {n : ℕ}

/-- Execute an NTM for `T` steps with a fixed choice sequence.
    Stops early if the machine reaches `qhalt`. -/
def trace (tm : NTM n) :
    (T : ℕ) → (Fin T → Bool) → Cfg n tm.Q → Cfg n tm.Q
  | 0, _, c => c
  | T + 1, choices, c =>
    if c.state = tm.qhalt then c
    else
      let b := choices ⟨0, Nat.zero_lt_succ T⟩
      let (q', workWrites, outWrite, inDir, workDirs, outDir) :=
        tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read
      let c' : Cfg n tm.Q :=
        { state := q'
          input := c.input.move inDir
          work := fun i => ((c.work i).write (workWrites i)).move (workDirs i)
          output := (c.output.write outWrite).move outDir }
      tm.trace T (fun i => choices ⟨i.val + 1, by omega⟩) c'

/-- Initial configuration: input on the input tape, all tapes start with `▷`. -/
def initCfg (tm : NTM n) (x : List Bool) : Cfg n tm.Q :=
  { state := tm.qstart
    input := initTape (x.map Γ.ofBool)
    work := fun _ => initTape []
    output := initTape [] }

/-- A configuration is halted when its state is `qhalt`. -/
def halted (tm : NTM n) (c : Cfg n tm.Q) : Prop := c.state = tm.qhalt

/-- NTM accepts `x`: there exists a time bound and choice sequence leading to
    `qhalt` with output cell 1 = `1`. -/
def Accepts (tm : NTM n) (x : List Bool) : Prop :=
  ∃ (T : ℕ) (choices : Fin T → Bool),
    let c' := tm.trace T choices (tm.initCfg x)
    tm.halted c' ∧ c'.output.cells 1 = Γ.one

/-- NTM accepts `x` within `T` steps: there exists a choice sequence of length `T`
    leading to `qhalt` with output cell 1 = `1`. -/
def AcceptsInTime (tm : NTM n) (x : List Bool) (T : ℕ) : Prop :=
  ∃ choices : Fin T → Bool,
    let c' := tm.trace T choices (tm.initCfg x)
    tm.halted c' ∧ c'.output.cells 1 = Γ.one

/-- NTM decides `L` within time bound `T(n)` (Arora-Barak Definition 2.1):
    all computation paths halt within `T(|x|)` steps, and `x ∈ L` iff there exists
    an accepting path. -/
def DecidesInTime (tm : NTM n) (L : Language) (T : ℕ → ℕ) : Prop :=
  (∀ x (choices : Fin (T x.length) → Bool),
    tm.halted (tm.trace (T x.length) choices (tm.initCfg x))) ∧
  (∀ x, x ∈ L ↔ tm.AcceptsInTime x (T x.length))

/-- Count of accepting choice sequences of length `T`.

    Meaningful when the machine halts on all paths within `T` steps — use in conjunction
    with `NTM.DecidesInTime` or an explicit all-paths-halt hypothesis. -/
noncomputable def acceptCount (tm : NTM n) (x : List Bool) (T : ℕ) : ℕ :=
  (Finset.univ.filter fun (choices : Fin T → Bool) =>
    let c' := tm.trace T choices (tm.initCfg x)
    c'.state = tm.qhalt ∧ c'.output.cells 1 = Γ.one).card

/-- Acceptance probability = |accepting paths| / 2^T.

    Meaningful when the machine halts on all paths within `T` steps. -/
noncomputable def acceptProb (tm : NTM n) (x : List Bool) (T : ℕ) : ℚ :=
  (tm.acceptCount x T : ℚ) / (2 ^ T : ℚ)

end NTM

/-- Embed a DTM into an NTM by using the same transition for both choices. -/
def TM.toNTM (tm : TM n) : NTM n where
  Q := tm.Q
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ := fun _ => tm.δ
  δ_right_of_start := fun _ => tm.δ_right_of_start

/-- The DTM and its NTM embedding agree on acceptance. -/
theorem TM.toNTM_accepts_iff (tm : TM n) (x : List Bool) :
    tm.Accepts x ↔ (tm.toNTM).Accepts x := by
  sorry
