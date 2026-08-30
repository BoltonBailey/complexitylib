/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Defs
public import Complexitylib.Models.TuringMachine.Oracle.Universality.Defs
import Complexitylib.Metacomplexity.Kolmogorov.Oracle.Internal

/-!
# Random-access conditional Kolmogorov complexity -- proof internals
-/


public section

namespace Complexity

namespace RandomAccessCondition

theorem oracle_bitQuery_internal
    (condition : List Bool) (index : ℕ) :
    oracle condition (bitQuery index) = (condition[index]?).getD false := by
  simp [oracle, bitQuery]

theorem oracle_inBoundsQuery_internal
    (condition : List Bool) (index : ℕ) :
    oracle condition (inBoundsQuery index) = decide (index < condition.length) := by
  simp [oracle, inBoundsQuery]

theorem oracle_injective_internal : Function.Injective oracle := by
  intro first second horacle
  have hlength : first.length = second.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hquery := congrFun horacle (inBoundsQuery first.length)
      simp [oracle_inBoundsQuery_internal, hlt] at hquery
    · have hquery := congrFun horacle (inBoundsQuery second.length)
      simp [oracle_inBoundsQuery_internal, hgt] at hquery
  apply List.ext_get hlength
  intro index hfirst hsecond
  have hquery := congrFun horacle (bitQuery index)
  simpa [oracle_bitQuery_internal, hfirst, hsecond] using hquery

end RandomAccessCondition

namespace OracleTM

variable {n simulatorTapes sourceTapes : ℕ}

theorem randomAccessConditionalPlainKolmogorovComplexity_le_internal
    {machine : OracleTM n} {program output condition : List Bool}
    (hproduce : machine.Produces (RandomAccessCondition.oracle condition)
      program output) :
    machine.randomAccessConditionalPlainKolmogorovComplexity output condition ≤
      program.length := by
  exact plainKolmogorovComplexity_le_internal hproduce

theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_le_internal
    {machine : OracleTM n} {program output condition : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime (RandomAccessCondition.oracle condition)
      program output time) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition time ≤ program.length := by
  exact timeBoundedKolmogorovComplexity_le_internal hproduce

theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_eq_top_iff_internal
    (machine : OracleTM n) (output condition : List Bool) (time : ℕ) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime
        (RandomAccessCondition.oracle condition) program output time := by
  exact timeBoundedKolmogorovComplexity_eq_top_iff_internal
    machine (RandomAccessCondition.oracle condition) output time

theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_witness_internal
    (machine : OracleTM n) (output condition : List Bool) (time : ℕ)
    (hfinite : machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
      output condition time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
        machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time ∧
      machine.ProducesInTime (RandomAccessCondition.oracle condition)
        program output time := by
  exact timeBoundedKolmogorovComplexity_witness_internal
    machine (RandomAccessCondition.oracle condition) output time hfinite

theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
    (machine : OracleTM n) (output condition : List Bool) (time bound : ℕ) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
          output condition time ≤ (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime (RandomAccessCondition.oracle condition)
          program output time := by
  exact timeBoundedKolmogorovComplexity_le_coe_iff_internal
    machine (RandomAccessCondition.oracle condition) output time bound

theorem randomAccessConditionalTimeBoundedKolmogorovComplexity_mono_internal
    (machine : OracleTM n) (output condition : List Bool)
    {first second : ℕ} (hclock : first ≤ second) :
    machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition second ≤
      machine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition first := by
  exact timeBoundedKolmogorovComplexity_mono_internal
    machine (RandomAccessCondition.oracle condition) output hclock

theorem SimulatesInTime.randomAccessConditionalKolmogorov_transfer_internal
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
            (bound + constant : ℕ) := by
  obtain ⟨coefficient, exponent, htransfer⟩ :=
    polynomialTimeOverhead_kolmogorov_transfer_internal
      hsim hlength hclock
  refine ⟨coefficient, exponent, ?_⟩
  intro condition output sourceTime bound hsource
  exact htransfer (RandomAccessCondition.oracle condition) output sourceTime
    bound hsource

end OracleTM

namespace TM

theorem toOracleTM_randomAccessConditionalTimeBoundedKolmogorovComplexity_eq_internal
    (machine : TM n) (output condition : List Bool) (time : ℕ) :
    machine.toOracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity
        output condition time =
      machine.timeBoundedKolmogorovComplexity output time := by
  exact toOracleTM_timeBoundedKolmogorovComplexity_eq_internal machine
    (RandomAccessCondition.oracle condition) output time

end TM

end Complexity
