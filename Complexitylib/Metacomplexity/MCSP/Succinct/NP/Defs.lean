/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Classes.NP.Witness
public import Complexitylib.Metacomplexity.MCSP.Succinct.Normalization.Defs

/-!
# SuccinctMCSP witness-class packaging -- definitions

This layer combines canonical instance decoding, normalized raw-circuit
verification, and the explicit polynomial code cap into one executable Boolean
checker. The later class theorem remains parameterized by a proof that the
paired checker language is in `P`; executability alone is not a machine time
bound.
-/


@[expose] public section

namespace Complexity

namespace SuccinctMCSP

/-- Executable checker for the complete normalized raw witness relation. -/
def verifyRawWitness (bits witness : List Bool) : Bool :=
  match Instance.decode? bits with
  | none => false
  | some inst =>
      inst.normalizeThreshold.verifyRawCircuit witness &&
        decide
          (witness.length ≤
            Instance.rawWitnessLengthPolynomial bits.length)

end SuccinctMCSP

end Complexity
