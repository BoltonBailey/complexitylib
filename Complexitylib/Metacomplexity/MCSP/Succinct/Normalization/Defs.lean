/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Asymptotics.PolyBound
public import Complexitylib.Classes.Pairing
public import Complexitylib.Metacomplexity.MCSP.Succinct.Witness.Defs

/-!
# Threshold normalization for SuccinctMCSP -- definitions

A satisfiable sample list has a direct DNF interpolant whose size is linear in
the number of samples times their arity. Capping the stored threshold at this
bound therefore preserves sampled feasibility and prevents oversized binary
thresholds from inflating circuit witnesses.

The final raw witness relation additionally enforces a polynomial code-length
cap. This matters for an empty sample list at a huge binary-encoded arity: a
one-gate raw circuit could otherwise contain an unnecessarily huge unary wire
reference even though a fixed constant gate is a sufficient witness.
-/


@[expose] public section

namespace Complexity

namespace SuccinctMCSP

namespace Instance

/-- Linear-size upper bound for a circuit interpolating any consistent sample
list. -/
def trivialCircuitSizeBound (inst : Instance) : ℕ :=
  1 + inst.samples.length * (3 * inst.arity + 2)

/-- Threshold capped at the sampled interpolation bound. -/
def effectiveThreshold (inst : Instance) : ℕ :=
  min inst.threshold inst.trivialCircuitSizeBound

/-- Replace only the threshold by its semantics-preserving effective cap. -/
def normalizeThreshold (inst : Instance) : Instance :=
  { inst with threshold := inst.effectiveThreshold }

/-- Polynomial envelope imposed on the canonical raw witness code. -/
def rawWitnessLengthPolynomial (inputLength : ℕ) : ℕ :=
  1 + inputLength * (4 * inputLength + 6)

end Instance

/-- Polynomially balanced raw witness relation for encoded SuccinctMCSP.

The instance is decoded canonically, checked at its normalized threshold, and
the raw code itself must fit the explicit polynomial envelope. -/
def RawWitnessRelation (bits witness : List Bool) : Prop :=
  match Instance.decode? bits with
  | none => False
  | some inst =>
      inst.normalizeThreshold.IsRawCircuitWitness witness ∧
        witness.length ≤ Instance.rawWitnessLengthPolynomial bits.length

end SuccinctMCSP

end Complexity
