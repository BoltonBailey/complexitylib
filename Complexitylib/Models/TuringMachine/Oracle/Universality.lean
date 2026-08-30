/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Models.TuringMachine.Oracle.Universality.Defs
public import Complexitylib.Models.TuringMachine.Oracle.Universality.Internal

/-!
# Oracle-uniform universal-machine interfaces

The same finite compiler and simulation clock must work for every Boolean
oracle. Semantic and timed simulations compose, and efficient oracle
universality implies semantic oracle universality.
-/


public section

namespace Complexity

namespace OracleTM

variable {firstTapes secondTapes thirdTapes : ℕ}

/-- Every oracle machine simulates itself under the identity compiler. -/
theorem Simulates.refl (machine : OracleTM firstTapes) :
    machine.Simulates machine id :=
  simulates_refl_internal machine

/-- Oracle-uniform semantic simulations compose. -/
theorem Simulates.comp
    {first : OracleTM firstTapes} {second : OracleTM secondTapes}
    {third : OracleTM thirdTapes}
    {compileFirst compileSecond : List Bool → List Bool}
    (hfirst : first.Simulates second compileFirst)
    (hsecond : second.Simulates third compileSecond) :
    first.Simulates third (compileFirst ∘ compileSecond) :=
  simulates_comp_internal hfirst hsecond

/-- Identity execution has identity oracle-simulation overhead. -/
theorem SimulatesInTime.refl (machine : OracleTM firstTapes) :
    machine.SimulatesInTime machine id (fun _ sourceTime => sourceTime) :=
  simulatesInTime_refl_internal machine

/-- Timed oracle-uniform simulations compose by nesting their clocks. -/
theorem SimulatesInTime.comp
    {first : OracleTM firstTapes} {second : OracleTM secondTapes}
    {third : OracleTM thirdTapes}
    {compileFirst compileSecond : List Bool → List Bool}
    {clockFirst clockSecond : TM.TimeOverhead}
    (hfirst : first.SimulatesInTime second compileFirst clockFirst)
    (hsecond : second.SimulatesInTime third compileSecond clockSecond) :
    first.SimulatesInTime third (compileFirst ∘ compileSecond)
      (fun program sourceTime =>
        clockFirst (compileSecond program) (clockSecond program sourceTime)) :=
  simulatesInTime_comp_internal hfirst hsecond

/-- Efficient oracle universality for any clock policy implies semantic oracle
universality. -/
theorem IsEfficientlyUniversalFor.isUniversal
    {simulator : OracleTM firstTapes}
    {admissible : TM.TimeOverhead → Prop}
    (h : simulator.IsEfficientlyUniversalFor admissible) :
    simulator.IsUniversal :=
  efficientlyUniversalFor_isUniversal_internal h

/-- Polynomially efficient oracle universality implies semantic oracle
universality. -/
theorem IsEfficientlyUniversal.isUniversal
    {simulator : OracleTM firstTapes}
    (h : simulator.IsEfficientlyUniversal) : simulator.IsUniversal :=
  efficientlyUniversalFor_isUniversal_internal h

/-- Weakening the admissible clock policy preserves oracle universality. -/
theorem IsEfficientlyUniversalFor.mono
    {simulator : OracleTM firstTapes}
    {firstPolicy secondPolicy : TM.TimeOverhead → Prop}
    (hpolicy : ∀ clock, firstPolicy clock → secondPolicy clock)
    (h : simulator.IsEfficientlyUniversalFor firstPolicy) :
    simulator.IsEfficientlyUniversalFor secondPolicy :=
  efficientlyUniversalFor_mono_internal hpolicy h

end OracleTM

end Complexity
