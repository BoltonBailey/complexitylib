import Complexitylib.Possible
import Mathlib.Computability.Tape
import Mathlib.Logic.Relation

universe u v

section
open Turing

structure TapeAction (Symbol : Type u) where
  symbol : Option Symbol
  movement : Option Dir

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

def applyTapeAction (a : TapeAction Symbol) (t : Tape (Option Symbol)) : Tape (Option Symbol) :=
  let t' := t.write a.symbol
  match a.movement with
  | none => t'
  | some d => t'.move d

def applyInputMove (d : Option Dir) (t : Tape (Option Symbol)) : Tape (Option Symbol) :=
  match d with
  | none => t
  | some d => t.move d

structure Cfg (nWork : ℕ) (Symbol : Type u) (State : Type u) where
  state : Option State
  input : Tape (Option Symbol)
  work : Fin nWork → Tape (Option Symbol)
  output : Tape (Option Symbol)

namespace MultiTapeTM

section
variable {nWork : ℕ} {Symbol : Type u} {M : Type u → Type v} [Possible M]

def stepRel (tm : MultiTapeTM nWork Symbol M) (c c' : Cfg nWork Symbol tm.State) : Prop :=
  ∃ q, c.state = some q ∧
  ∃ inputDir workActions outputAction nextState,
    Possible.possible (tm.tr q c.input.head (fun i => (c.work i).head))
      (inputDir, workActions, outputAction, nextState) ∧
    c'.state = nextState ∧
    c'.input = applyInputMove inputDir c.input ∧
    c'.work = (fun i => applyTapeAction (workActions i) (c.work i)) ∧
    c'.output = applyTapeAction outputAction c.output

def initCfg (tm : MultiTapeTM nWork Symbol M) (input : List Symbol) : Cfg nWork Symbol tm.State :=
  { state := some tm.q₀
    input := Tape.mk' default (ListBlank.mk (input.map some))
    work := fun _ => Tape.mk' default default
    output := Tape.mk' default default }

def reaches (tm : MultiTapeTM nWork Symbol M) (c c' : Cfg nWork Symbol tm.State) : Prop :=
  Relation.ReflTransGen (stepRel tm) c c'

inductive reachesIn (tm : MultiTapeTM nWork Symbol M) :
    ℕ → Cfg nWork Symbol tm.State → Cfg nWork Symbol tm.State → Prop where
  | zero : reachesIn tm 0 c c
  | step : stepRel tm c c'' → reachesIn tm n c'' c' → reachesIn tm (n + 1) c c'

def halted {S : Type u} (c : Cfg nWork Symbol S) : Prop :=
  c.state = none

def Outputs (tm : MultiTapeTM nWork Symbol M) (input : List Symbol) (c' : Cfg nWork Symbol tm.State) : Prop :=
  reaches tm (initCfg tm input) c' ∧ halted c'

def OutputsWithinTime (tm : MultiTapeTM nWork Symbol M)
    (input : List Symbol) (c' : Cfg nWork Symbol tm.State) (t : ℕ) : Prop :=
  reachesIn tm t (initCfg tm input) c' ∧ halted c'

end
end MultiTapeTM

end
