/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal

/-!
# Random-access conditional Kolmogorov complexity

The finite condition is exposed through a faithful Boolean oracle. Canonical
tagged queries separately read condition bits and test whether an index is in
bounds, so the oracle retains both contents and length. This is an explicit
random-access convention suitable for conditional meta-complexity; any theorem
whose source fixes a different evaluator convention must provide a simulation
bridge rather than identify the models silently.
-/


public section

namespace Complexity

namespace RandomAccessCondition

/-- A canonical bit query returns the indexed bit, defaulting to false out of
bounds. -/
@[simp] theorem oracle_bitQuery (condition : List Bool) (index : ℕ) :
    oracle condition (bitQuery index) = (condition[index]?).getD false :=
  oracle_bitQuery_internal condition index

/-- A canonical bounds query says exactly whether the index is valid. -/
@[simp] theorem oracle_inBoundsQuery (condition : List Bool) (index : ℕ) :
    oracle condition (inBoundsQuery index) = decide (index < condition.length) :=
  oracle_inBoundsQuery_internal condition index

/-- The random-access oracle faithfully retains the finite condition, including
its length. -/
theorem oracle_injective : Function.Injective oracle :=
  oracle_injective_internal

end RandomAccessCondition

namespace OracleTM

variable {n simulatorTapes sourceTapes : ℕ}

/-- Any program producing relative to the condition oracle upper-bounds plain
conditional complexity. -/
theorem randomAccessConditionalPlainKolmogorovComplexity_le
    {machine : OracleTM n} {program output condition : List Bool}
    (hproduce : machine.Produces (RandomAccessCondition.oracle condition)
      program output) :
    machine.randomAccessConditionalPlainKolmogorovComplexity output condition ≤
      program.length :=
  randomAccessConditionalPlainKolmogorovComplexity_le_internal hproduce

/-- Any program producing within the clock upper-bounds bounded conditional
complexity. -/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_le
    {machine : OracleTM n} {program output condition : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime (RandomAccessCondition.oracle condition)
      program output time) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition time ≤ program.length :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_le_internal hproduce

/-- Bounded conditional complexity is infinite exactly when no program
produces relative to the condition oracle within the clock. -/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_eq_top_iff
    (machine : OracleTM n) (output condition : List Bool) (time : ℕ) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime
        (RandomAccessCondition.oracle condition) program output time :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_eq_top_iff_internal
    machine output condition time

/-- Every finite bounded conditional complexity value is attained. -/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_witness
    (machine : OracleTM n) (output condition : List Bool) (time : ℕ)
    (hfinite : machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
      output condition time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
        machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time ∧
      machine.ProducesInTime (RandomAccessCondition.oracle condition)
        program output time :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_witness_internal
    machine output condition time hfinite

/-- Bounded conditional complexity is at most `bound` exactly when a program
of at most that length succeeds within the clock. -/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff
    (machine : OracleTM n) (output condition : List Bool) (time bound : ℕ) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time ≤ (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime (RandomAccessCondition.oracle condition)
          program output time :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
    machine output condition time bound

/-- Enlarging the clock cannot increase bounded conditional complexity. -/
theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_mono
    (machine : OracleTM n) (output condition : List Bool)
    {first second : ℕ} (hclock : first ≤ second) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition second ≤
      machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition first :=
  randomAccessConditionalTimeBoundedKolmogorovComplexity_mono_internal
    machine output condition hclock

/-- An oracle-uniform polynomial simulation transfers conditional descriptions
with one compiler constant and clock shared by every finite condition. -/
theorem SimulatesInTime.randomAccessConditionalKolmogorov_transfer
    {simulator : OracleTM simulatorTapes} {source : OracleTM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ}
    {clock : TM.TimeOverhead}
    (hsim : simulator.SimulatesInTime source compile clock)
    (hlength : TM.HasAdditiveProgramOverhead compile constant)
    (hclock : TM.PolynomialTimeOverhead clock) :
    ∃ coefficient exponent,
      ∀ (condition output : List Bool) (sourceTime bound : ℕ),
        source.randomAccessConditionalTimeBoundedKolmogorovComplexity
              output condition sourceTime ≤ (bound : WithTop ℕ) →
          simulator.randomAccessConditionalTimeBoundedKolmogorovComplexity
              output condition
              (coefficient * (bound + sourceTime + 1) ^ exponent) ≤
            (bound + constant : ℕ) :=
  hsim.randomAccessConditionalKolmogorov_transfer_internal hlength hclock

end OracleTM

namespace TM

/-- An embedded ordinary machine ignores every condition, so its bounded
conditional complexity is exactly its ordinary bounded complexity. -/
theorem toOracleTM_randomAccessConditionalTimeBoundedKolmogorovComplexity_eq
    (machine : TM n) (output condition : List Bool) (time : ℕ) :
    machine.toOracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition time =
      machine.timeBoundedKolmogorovComplexity output time :=
  toOracleTM_randomAccessConditionalTimeBoundedKolmogorovComplexity_eq_internal
    machine output condition time

end TM

end Complexity
