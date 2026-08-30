/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Oracle.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Oracle.Internal

/-!
# Oracle-relative Kolmogorov complexity

This module exposes plain and time-bounded description complexity relative to
an arbitrary deterministic oracle machine and Boolean oracle. The ordinary TM
embedding preserves bounded complexity exactly for every oracle. An
oracle-uniform polynomial simulation transfers bounded descriptions with one
compiler constant and clock shared by all oracles.
-/


public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

/-- Any oracle program producing the requested output upper-bounds plain
oracle-relative complexity. -/
theorem plainKolmogorovComplexity_le
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool}
    (hproduce : machine.Produces oracle program output) :
    machine.plainKolmogorovComplexity oracle output ≤ program.length :=
  plainKolmogorovComplexity_le_internal hproduce

/-- Any oracle program producing within a clock upper-bounds time-bounded
oracle-relative complexity. -/
theorem timeBoundedKolmogorovComplexity_le
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime oracle program output time) :
    machine.timeBoundedKolmogorovComplexity oracle output time ≤
      program.length :=
  timeBoundedKolmogorovComplexity_le_internal hproduce

/-- Bounded oracle complexity is infinite exactly when no program produces the
output within the clock. -/
theorem timeBoundedKolmogorovComplexity_eq_top_iff
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ) :
    machine.timeBoundedKolmogorovComplexity oracle output time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime oracle program output time :=
  timeBoundedKolmogorovComplexity_eq_top_iff_internal
    machine oracle output time

/-- Every finite bounded oracle complexity value is attained by a program. -/
theorem timeBoundedKolmogorovComplexity_witness
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity oracle output time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
        machine.timeBoundedKolmogorovComplexity oracle output time ∧
      machine.ProducesInTime oracle program output time :=
  timeBoundedKolmogorovComplexity_witness_internal
    machine oracle output time hfinite

/-- Bounded oracle complexity is at most `bound` exactly when a program of at
most that length produces the output within the clock. -/
theorem timeBoundedKolmogorovComplexity_le_coe_iff
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time bound : ℕ) :
    machine.timeBoundedKolmogorovComplexity oracle output time ≤
        (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime oracle program output time :=
  timeBoundedKolmogorovComplexity_le_coe_iff_internal
    machine oracle output time bound

/-- Enlarging the oracle-machine clock cannot increase bounded complexity. -/
theorem timeBoundedKolmogorovComplexity_mono
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) {first second : ℕ} (hclock : first ≤ second) :
    machine.timeBoundedKolmogorovComplexity oracle output second ≤
      machine.timeBoundedKolmogorovComplexity oracle output first :=
  timeBoundedKolmogorovComplexity_mono_internal
    machine oracle output hclock

/-- An oracle-uniform polynomial simulation transfers every bounded
oracle-relative description using the same compiler constant and polynomial
clock for all Boolean oracles. -/
theorem SimulatesInTime.kolmogorov_transfer
    {simulatorTapes sourceTapes : ℕ}
    {simulator : OracleTM simulatorTapes} {source : OracleTM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ}
    {clock : TM.TimeOverhead}
    (hsim : simulator.SimulatesInTime source compile clock)
    (hlength : TM.HasAdditiveProgramOverhead compile constant)
    (hclock : TM.PolynomialTimeOverhead clock) :
    ∃ coefficient exponent,
      ∀ (oracle : BooleanOracle) (output : List Bool)
        (sourceTime bound : ℕ),
        source.timeBoundedKolmogorovComplexity oracle output sourceTime ≤
            (bound : WithTop ℕ) →
          simulator.timeBoundedKolmogorovComplexity oracle output
              (coefficient * (bound + sourceTime + 1) ^ exponent) ≤
            (bound + constant : ℕ) :=
  polynomialTimeOverhead_kolmogorov_transfer_internal
    hsim hlength hclock

end OracleTM

namespace TM

/-- Embedding an ordinary machine into the oracle model preserves its bounded
Kolmogorov complexity exactly, independently of the supplied oracle. -/
theorem toOracleTM_timeBoundedKolmogorovComplexity_eq
    (machine : TM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ) :
    machine.toOracleTM.timeBoundedKolmogorovComplexity oracle output time =
      machine.timeBoundedKolmogorovComplexity output time :=
  toOracleTM_timeBoundedKolmogorovComplexity_eq_internal
    machine oracle output time

end TM

end Complexity
