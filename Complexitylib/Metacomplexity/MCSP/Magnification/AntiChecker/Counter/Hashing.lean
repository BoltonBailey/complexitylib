/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Hashing.Defs
public import Complexitylib.Classes.Randomized.ApproximateCounting.Relative.OracleProgram
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Hashing.Internal

/-!
# Hashing circuits for anti-checker counters

Any bounded circuit implementing the amplified relative hashing estimator on
the encoded survivor set yields a deterministic correct anti-checker counter.
The random seed is fixed nonuniformly, with exact circuit-size preservation.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- A bounded hashing-estimator circuit yields a deterministic counter that
is accurate on every packed labeled-sample input, at identical size. -/
theorem exists_correct_counter_of_hashingCircuit
    {overhead arity prefixLength internalGates : ℕ}
    (beta : PositiveRationalScale) (harity : arity ≠ 0)
    {circuit : Circuit Basis.andOr2
      (hashingCounterSeedWidth beta arity prefixLength +
        counterInputWidth arity prefixLength)
      (counterOutputWidth beta arity) internalGates}
    (himplements : HashingCircuitImplements beta circuit)
    (hsize : circuit.size ≤ counterSizeBound overhead beta arity) :
    ∃ counter : ApproximateCounterCircuit overhead beta arity prefixLength,
      counter.IsCorrect ∧ counter.circuit.size = circuit.size :=
  exists_correct_counter_of_hashingCircuit_internal
    beta harity himplements hsize

/-- A relative-counting oracle program and an exact polynomial circuit oracle
produce the required deterministic counter once their inlined size meets the
anti-checker bound. -/
theorem exists_correct_counter_of_oracleProgram
    {language : Language}
    {overhead arity prefixLength rounds : ℕ}
    (beta : PositiveRationalScale) (harity : arity ≠ 0)
    (program : AdaptiveOracleProgram
      (hashingCounterSeedWidth beta arity prefixLength +
        counterInputWidth arity prefixLength)
      (counterOutputWidth beta arity) rounds)
    (circuitOracle : PolynomialCircuitOracle language)
    (hprogram : ApproximateCounting.Relative.OracleProgramImplements
      (roundPrecision arity) (counterInputWidth arity prefixLength + 1)
      (encodedSurvivorSet arity (smallThreshold beta arity))
      program circuitOracle.oracle)
    (hsize : (program.inlineCircuitOracle circuitOracle).2.size ≤
      counterSizeBound overhead beta arity) :
    ∃ counter : ApproximateCounterCircuit overhead beta arity prefixLength,
      counter.IsCorrect ∧
        counter.circuit.size =
          (program.inlineCircuitOracle circuitOracle).2.size :=
  exists_correct_counter_of_oracleProgram_internal
    beta harity program circuitOracle hprogram hsize

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
