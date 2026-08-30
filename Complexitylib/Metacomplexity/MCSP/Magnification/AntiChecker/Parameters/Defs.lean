/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.Parameters.Defs

/-!
# Anti-Checker Lemma parameters -- definitions

This layer fixes natural-number versions of the four scales in Oliveira--Pich--
Santhanam's Anti-Checker Lemma: the hard-function threshold, the smaller circuit
threshold met by the generated samples, the number of samples, and the size of
the multi-output generator circuit.

Thresholds and sample counts round exponents down. The generator's upper size
bound rounds its overhead exponent up, so it does not understate the published
upper bound. The two choices differ by at most a factor of two through the
general `PositiveRationalScale` API.
-/


@[expose] public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- The explicit constant `10` used by the published Anti-Checker Lemma. -/
def fixedConstant : ℕ := 10

/-- GapMCSP parameters at exponent `beta` and the Anti-Checker Lemma's fixed
denominator constant. -/
def gapParameters (beta : PositiveRationalScale) : Parameters where
  beta := beta
  constant := fixedConstant
  constant_pos := by decide

/-- Hard-function cutoff `2^floor(beta*n)`. -/
def hardThreshold (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  (gapParameters beta).noThreshold arity

/-- Small-circuit cutoff `2^floor(beta*n)/(10*n)`. -/
def smallThreshold (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  (gapParameters beta).yesThreshold arity

/-- Floor-rounded sample count `2^floor(10*beta*n)`. -/
def sampleCount (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  beta.powFloor (fixedConstant * arity)

/-- Ceiling-rounded companion to `sampleCount`, used to expose rounding slack. -/
def sampleCountUpper (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  beta.powCeil (fixedConstant * arity)

/-- Number of output bits needed to print all fixed-width sample inputs. -/
def outputBitCount (beta : PositiveRationalScale) (arity : ℕ) : ℕ :=
  sampleCount beta arity * arity

/-- Ceiling-rounded generator size `2^n * 2^ceil(k*beta*n)`. -/
def generatorSizeBound (overhead : ℕ) (beta : PositiveRationalScale)
    (arity : ℕ) : ℕ :=
  2 ^ arity * beta.powCeil (overhead * arity)

instance (beta : PositiveRationalScale) (arity : ℕ) :
    NeZero (sampleCount beta arity) :=
  ⟨by simp [sampleCount, PositiveRationalScale.powFloor]⟩

instance (beta : PositiveRationalScale) (arity : ℕ) [NeZero arity] :
    NeZero (outputBitCount beta arity) :=
  ⟨Nat.ne_of_gt (Nat.mul_pos (NeZero.pos (sampleCount beta arity))
    (NeZero.pos arity))⟩

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
