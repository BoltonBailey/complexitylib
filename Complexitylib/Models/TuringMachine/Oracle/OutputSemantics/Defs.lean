/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Oracle.Defs

/-!
# Pointwise output semantics for deterministic oracle TMs -- definitions

Programs are ordinary finite binary inputs; the Boolean oracle is a separate
semantic parameter. Production records the complete binary output and an
explicit bound on local steps plus one-step oracle lookups.
-/


@[expose] public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

/-- An oracle machine halts on a program within an explicit step budget. -/
def HaltsInTime (machine : OracleTM n) (oracle : BooleanOracle)
    (program : List Bool) (time : ℕ) : Prop :=
  ∃ cfg steps, steps ≤ time ∧
    machine.reachesIn oracle steps (machine.initCfg program) cfg ∧
    machine.halted cfg

/-- An oracle machine produces an exact output within an explicit step budget. -/
def ProducesInTime (machine : OracleTM n) (oracle : BooleanOracle)
    (program output : List Bool) (time : ℕ) : Prop :=
  ∃ cfg steps, steps ≤ time ∧
    machine.reachesIn oracle steps (machine.initCfg program) cfg ∧
    machine.halted cfg ∧ cfg.output.HasOutput output

/-- Eventual oracle-machine production, expressed through some finite clock. -/
def Produces (machine : OracleTM n) (oracle : BooleanOracle)
    (program output : List Bool) : Prop :=
  ∃ time, machine.ProducesInTime oracle program output time

end OracleTM

end Complexity
