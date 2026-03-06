import Complexitylib.Possible
import Mathlib.Computability.Tape
import Mathlib.Logic.Relation

/-!
# Multi-Tape Monadic Turing Machines

This file defines a multi-tape Turing machine whose transition function is monadic,
parameterized over any monad with a `Possible` instance. The machine has a read-only input
tape, a configurable number of read-write work tapes, and a write-only output tape.

## Main definitions

- `TapeAction` — a tape head action: optionally write a symbol, optionally move
- `MultiTapeTM` — the Turing machine, with a monadic transition function
- `Cfg` — a machine configuration (state + tape contents)
- `MultiTapeTM.stepRel` — the one-step relation extracted via `Possible.possible`
- `MultiTapeTM.reaches` — reflexive-transitive closure of `stepRel`
- `MultiTapeTM.Outputs` — a machine reaches a halting configuration from an input
- `MultiTapeTM.OutputsWithinTime` — same, within a bounded number of steps
-/

universe u v

section
open Turing

/-- An action for a tape head: optionally write a symbol, then optionally move. -/
structure TapeAction (Symbol : Type u) where
  symbol : Option Symbol
  movement : Option Dir

/-- A multi-tape Turing machine with `nWork` work tapes, alphabet `Symbol`, and monadic
transition function in `M`. The input tape is read-only (the transition returns only a
direction) and the output tape is write-only (it receives a `TapeAction`). -/
structure MultiTapeTM (nWork : ℕ) (Symbol : Type u) (M : Type u → Type v) [Possible M] where
  State : Type u
  q₀ : State
  tr : State
    → Option Symbol
    → (Fin nWork → Option Symbol)
    → M ( Option Dir
        × (Fin nWork → TapeAction Symbol)
        × TapeAction Symbol
        × Option State )

/-- Apply a `TapeAction` to a tape: write the symbol (if any), then move (if any). -/
def applyTapeAction (a : TapeAction Symbol) (t : Tape (Option Symbol)) : Tape (Option Symbol) :=
  let t' := t.write a.symbol
  match a.movement with
  | none => t'
  | some d => t'.move d

/-- Apply a direction to the input tape: move if `some`, otherwise stay. -/
def applyInputMove (d : Option Dir) (t : Tape (Option Symbol)) : Tape (Option Symbol) :=
  match d with
  | none => t
  | some d => t.move d

/-- A configuration of a multi-tape Turing machine: current state and tape contents. -/
structure Cfg (nWork : ℕ) (Symbol : Type u) (State : Type u) where
  state : Option State
  input : Tape (Option Symbol)
  work : Fin nWork → Tape (Option Symbol)
  output : Tape (Option Symbol)

namespace MultiTapeTM

section
variable {nWork : ℕ} {Symbol : Type u} {M : Type u → Type v} [Possible M]

/-- The one-step relation: `stepRel tm c c'` holds when `c` transitions to `c'` in one step
according to `tm`, via some output of the monadic transition function. -/
def stepRel (tm : MultiTapeTM nWork Symbol M) (c c' : Cfg nWork Symbol tm.State) : Prop :=
  ∃ q, c.state = some q ∧
  ∃ inputDir workActions outputAction nextState,
    Possible.possible (tm.tr q c.input.head (fun i => (c.work i).head))
      (inputDir, workActions, outputAction, nextState) ∧
    c'.state = nextState ∧
    c'.input = applyInputMove inputDir c.input ∧
    c'.work = (fun i => applyTapeAction (workActions i) (c.work i)) ∧
    c'.output = applyTapeAction outputAction c.output

/-- The initial configuration: start state, input written to the input tape, blank work
and output tapes. -/
def initCfg (tm : MultiTapeTM nWork Symbol M) (input : List Symbol) : Cfg nWork Symbol tm.State :=
  { state := some tm.q₀
    input := Tape.mk' default (ListBlank.mk (input.map some))
    work := fun _ => Tape.mk' default default
    output := Tape.mk' default default }

/-- `reaches tm c c'` holds when `c'` is reachable from `c` in zero or more steps. -/
def reaches (tm : MultiTapeTM nWork Symbol M) (c c' : Cfg nWork Symbol tm.State) : Prop :=
  Relation.ReflTransGen (stepRel tm) c c'

/-- `reachesIn tm n c c'` holds when `c'` is reachable from `c` in exactly `n` steps. -/
inductive reachesIn (tm : MultiTapeTM nWork Symbol M) :
    ℕ → Cfg nWork Symbol tm.State → Cfg nWork Symbol tm.State → Prop where
  | zero : reachesIn tm 0 c c
  | step : stepRel tm c c'' → reachesIn tm n c'' c' → reachesIn tm (n + 1) c c'

/-- A configuration is halted when its state is `none`. -/
def halted {S : Type u} (c : Cfg nWork Symbol S) : Prop :=
  c.state = none

/-- `Outputs tm input c'` holds when `tm` started on `input` can reach the halting
configuration `c'`. -/
def Outputs (tm : MultiTapeTM nWork Symbol M) (input : List Symbol) (c' : Cfg nWork Symbol tm.State) : Prop :=
  reaches tm (initCfg tm input) c' ∧ halted c'

/-- `OutputsWithinTime tm input c' t` holds when `tm` started on `input` reaches the
halting configuration `c'` in exactly `t` steps. -/
def OutputsWithinTime (tm : MultiTapeTM nWork Symbol M)
    (input : List Symbol) (c' : Cfg nWork Symbol tm.State) (t : ℕ) : Prop :=
  reachesIn tm t (initCfg tm input) c' ∧ halted c'

end
end MultiTapeTM

end
