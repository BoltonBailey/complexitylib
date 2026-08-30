/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Encoding.Pairing
public import Complexitylib.Metacomplexity.Kolmogorov.Defs

/-!
# Minimum time-bounded Kolmogorov complexity -- definitions

This definitions layer gives `MINKT[r]` a total machine-relative semantics and
a canonical auxiliary-unary input format. An instance is a pair `(x, 1^t)` of
an output string and a unary clock. It is a yes-instance exactly when
`C_U^t(x) < r(|x|)`.

The comparison is intentionally strict. This matches the convention in which
an `r`-random string satisfies `C_U^t(x) >= r(|x|)`, so `MINKT[r]` recognizes
the complementary low-complexity strings. The machine is an explicit parameter;
universality is a hypothesis for machine-invariance or hardness theorems, not
part of the minimum's definition.

The decoder accepts the empty unary clock as time zero, making the language
total at every input. Auxiliary-unary distributions used in average-case
results can separately restrict their sampled clock to be positive.
-/


@[expose] public section

namespace Complexity

namespace MINKT

/-- A decoded MINKT instance consisting of an output and a unary time bound. -/
structure Instance where
  /-- String whose time-bounded description complexity is measured. -/
  output : List Bool
  /-- Primitive machine-step budget, encoded in unary. -/
  time : ℕ

namespace Instance

/-- The canonical unary representation of the time bound. -/
def unaryClock (inst : Instance) : List Bool :=
  List.replicate inst.time true

/-- Canonically encode an instance as the self-delimiting pair `(x, 1^t)`. -/
def encode (inst : Instance) : List Bool :=
  pair inst.output inst.unaryClock

/-- Decode exactly one canonical output/unary-clock pair.

Malformed pairing and clocks containing `false` are rejected. -/
def decode? (bits : List Bool) : Option Instance := do
  let (output, clock) ← unpair? bits
  if clock = List.replicate clock.length true then
    some { output, time := clock.length }
  else
    none

/-- Replace only the primitive time bound of an instance. -/
def withTime (inst : Instance) (time : ℕ) : Instance :=
  { inst with time }

/-- The strict machine-relative MINKT predicate `C_U^t(x) < r(|x|)`. -/
def IsBelow {tapes : ℕ} (inst : Instance) (machine : TM tapes)
    (threshold : ℕ → ℕ) : Prop :=
  machine.timeBoundedKolmogorovComplexity inst.output inst.time <
    (threshold inst.output.length : WithTop ℕ)

/-- Direct short-program formulation of the MINKT predicate. -/
def HasProgramShorterThan {tapes : ℕ} (inst : Instance) (machine : TM tapes)
    (threshold : ℕ → ℕ) : Prop :=
  ∃ program, program.length < threshold inst.output.length ∧
    machine.ProducesInTime program inst.output inst.time

end Instance

/-- A raw witness relation for encoded MINKT instances.

The witness is the candidate short program. Canonical instance decoding,
strict length, exact output, and the primitive clock are all retained. -/
def ProgramWitnessRelation {tapes : ℕ} (machine : TM tapes)
    (threshold : ℕ → ℕ) (bits program : List Bool) : Prop :=
  ∃ inst : Instance,
    Instance.decode? bits = some inst ∧
      program.length < threshold inst.output.length ∧
      machine.ProducesInTime program inst.output inst.time

end MINKT

/-- The total strict-threshold Minimum Time-Bounded Kolmogorov Complexity
language relative to `machine` and length threshold `threshold`.

Malformed codes are no-instances. -/
def MINKT {tapes : ℕ} (machine : TM tapes) (threshold : ℕ → ℕ) : Language :=
  {bits | match MINKT.Instance.decode? bits with
    | some inst => inst.IsBelow machine threshold
    | none => False}

end Complexity
