/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.Pairing
public import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Defs

/-!
# Minimum conditional time-bounded Kolmogorov complexity -- definitions

This layer fixes a canonical representation of a conditional description-
complexity instance `(x, y, 1^t)`. The output `x` is measured relative to the
faithful random-access condition oracle for `y`; the primitive clock is encoded
in unary.

The machine remains explicit. Universality and equivalence with another
conditional-input convention are later hypotheses, not properties hidden in
the definition.
-/


@[expose] public section

namespace Complexity

namespace MINCKT

/-- A decoded conditional MinKT instance `(x, y, 1^t)`. -/
structure Instance where
  /-- String whose conditional description complexity is measured. -/
  output : List Bool
  /-- Finite random-access condition. -/
  condition : List Bool
  /-- Primitive oracle-machine step budget, encoded in unary. -/
  time : ℕ

namespace Instance

/-- The canonical unary representation of the primitive clock. -/
def unaryClock (inst : Instance) : List Bool :=
  List.replicate inst.time true

/-- Canonical right-associated encoding of `(x, y, 1^t)`. -/
def encode (inst : Instance) : List Bool :=
  pair inst.output (pair inst.condition inst.unaryClock)

/-- Decode exactly one canonical output/condition/unary-clock triple.

Malformed outer or inner pairing and clocks containing `false` are rejected. -/
def decode? (bits : List Bool) : Option Instance :=
  match unpair? bits with
  | some (output, remaining) =>
      match unpair? remaining with
      | some (condition, clock) =>
          if clock = List.replicate clock.length true then
            some { output, condition, time := clock.length }
          else
            none
      | none => none
  | none => none

/-- Replace only the primitive time bound. -/
def withTime (inst : Instance) (time : ℕ) : Instance :=
  { inst with time }

/-- Machine-relative conditional complexity of the decoded instance. -/
noncomputable def complexity {tapes : ℕ} (inst : Instance)
    (machine : OracleTM tapes) : WithTop ℕ :=
  machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
    inst.output inst.condition inst.time

/-- The bounded conditional complexity is at most an explicit threshold. -/
def IsAtMost {tapes : ℕ} (inst : Instance) (machine : OracleTM tapes)
    (threshold : ℕ) : Prop :=
  inst.complexity machine ≤ (threshold : WithTop ℕ)

/-- Direct program formulation of `IsAtMost`. -/
def HasProgramAtMost {tapes : ℕ} (inst : Instance)
    (machine : OracleTM tapes) (threshold : ℕ) : Prop :=
  ∃ program, program.length ≤ threshold ∧
    machine.ProducesInTime (RandomAccessCondition.oracle inst.condition)
      program inst.output inst.time

end Instance

end MINCKT

end Complexity
