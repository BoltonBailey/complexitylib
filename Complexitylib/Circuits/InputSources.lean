/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.InputSources.Defs
public import Complexitylib.Circuits.InputSources.Internal

/-!
# Constant and primary-input source circuits

This module exposes zero-internal-gate circuits whose outputs independently
choose a constant or copy one primary input.
-/


public section

namespace Complexity

namespace Circuit

/-- Source tuples evaluate pointwise to their specified constants or inputs. -/
@[simp] theorem eval_inputSources {inputWidth outputWidth : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (sources : Fin outputWidth → InputSource inputWidth)
    (input : BitString inputWidth) :
    (inputSources sources).eval input =
      fun output => (sources output).eval input :=
  eval_inputSources_internal sources input

/-- An `outputWidth`-source tuple has exactly that many counted output gates. -/
@[simp] theorem size_inputSources {inputWidth outputWidth : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (sources : Fin outputWidth → InputSource inputWidth) :
    (inputSources sources).size = outputWidth := by
  simp only [Circuit.size, Nat.zero_add]

end Circuit

end Complexity
