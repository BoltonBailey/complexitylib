/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Asymptotics
public import Complexitylib.Classes.PPoly.Defs
public import Complexitylib.Models.TuringMachine.Oracle.Defs

/-!
# Polynomial-size circuit oracles -- definitions

This module packages a language-deciding circuit family together with a
polynomial asymptotic size certificate. Its induced Boolean oracle evaluates
the family member selected by the query length.
-/


@[expose] public section

namespace Complexity

/-- A polynomial-size fan-in-two AND/OR circuit family deciding `language`.

The exponent is stored explicitly so downstream circuit-inlining arguments can
track the size of the oracle circuit used at each fixed query width. -/
structure PolynomialCircuitOracle (language : Language) where
  /-- The circuit family supplying one Boolean oracle circuit per query width. -/
  family : CircuitFamily Basis.andOr2
  /-- Exponent in the family's polynomial asymptotic size bound. -/
  exponent : ℕ
  /-- Exact agreement between the family and the oracle language. -/
  decides : family.Decides language
  /-- Polynomial asymptotic size of the circuit family. -/
  size_bigO : family.size =O ((· ^ exponent) : ℕ → ℕ)

namespace PolynomialCircuitOracle

/-- The Boolean oracle induced by evaluating the length-indexed circuit
family on each query. -/
def oracle {language : Language}
    (circuitOracle : PolynomialCircuitOracle language) : BooleanOracle :=
  circuitOracle.family.evalList

end PolynomialCircuitOracle

end Complexity
