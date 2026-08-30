/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Succinct.Defs
public import Complexitylib.Metacomplexity.MCSP.Succinct.Internal
public import Complexitylib.Metacomplexity.MCSP.Succinct.Witness

/-!
# Succinct Minimum Circuit Size Problem

This module exposes sampled circuit minimization. A typed instance contains an
arity, a list of input/output samples, and a circuit-size threshold. Repeated
inputs are retained, including contradictory constraints. Positive arities use
the library's exact `Basis.andOr2` convention; zero arity uses an explicit
constant bit of size zero.

The binary codec is exact and total. In particular, malformed pairing,
noncanonical natural fields, wrong-width sample inputs, non-singleton outputs,
and any mismatch between the stored sample count and payload are rejected. Its
raw-circuit verifier checks every sample and is exact for the typed semantics.
-/


public section

namespace Complexity

namespace SuccinctMCSP

namespace Sample

/-- A sample built from `f` is satisfied by `f`. -/
@[simp] theorem matchesFunction_ofFunction {arity : ℕ}
    (f : BitString arity → Bool) (input : BitString arity) :
    (ofFunction f input).MatchesFunction f :=
  matchesFunction_ofFunction_internal f input

/-- Canonical sample encodings decode to their original typed samples. -/
@[simp] theorem decode?_encode {arity : ℕ} (sample : Sample arity) :
    decode? arity sample.encode = some sample :=
  decode?_encode_internal sample

/-- Sample decoding succeeds precisely on the canonical encoding of its result. -/
theorem decode?_eq_some_iff {arity : ℕ}
    (bits : List Bool) (sample : Sample arity) :
    decode? arity bits = some sample ↔ bits = sample.encode :=
  decode?_eq_some_iff_internal bits sample

/-- Exact encoded length of one `arity`-bit sample. -/
@[simp] theorem length_encode {arity : ℕ} (sample : Sample arity) :
    sample.encode.length = 2 * arity + 3 :=
  length_encode_internal sample

end Sample

/-- A canonical right-nested sample list decodes at its exact count. -/
@[simp] theorem decodeSamples?_encodeSamples {arity : ℕ}
    (samples : List (Sample arity)) :
    decodeSamples? arity samples.length (encodeSamples samples) = some samples :=
  decodeSamples?_encodeSamples_internal samples

/-- Successful sample-list decoding characterizes both the exact count and
canonical payload. -/
theorem decodeSamples?_eq_some_iff {arity count : ℕ}
    (bits : List Bool) (samples : List (Sample arity)) :
    decodeSamples? arity count bits = some samples ↔
      samples.length = count ∧ bits = encodeSamples samples :=
  decodeSamples?_eq_some_iff_internal bits samples

/-- The nested payload uses exactly `4 * arity + 8` bits per sample. -/
@[simp] theorem length_encodeSamples {arity : ℕ}
    (samples : List (Sample arity)) :
    (encodeSamples samples).length = samples.length * (4 * arity + 8) :=
  length_encodeSamples_internal samples

namespace Instance

@[simp] theorem arity_ofInputs {arity threshold : ℕ}
    (f : BitString arity → Bool) (inputs : List (BitString arity)) :
    (ofInputs threshold f inputs).arity = arity := rfl

@[simp] theorem threshold_ofInputs {arity threshold : ℕ}
    (f : BitString arity → Bool) (inputs : List (BitString arity)) :
    (ofInputs threshold f inputs).threshold = threshold := rfl

@[simp] theorem length_samples_ofInputs {arity threshold : ℕ}
    (f : BitString arity → Bool) (inputs : List (BitString arity)) :
    (ofInputs threshold f inputs).samples.length = inputs.length := by
  simp [ofInputs]

/-- The function used to label an input list satisfies every resulting sample,
including repeated inputs. -/
theorem samplesFunction_ofInputs {arity threshold : ℕ}
    (f : BitString arity → Bool) (inputs : List (BitString arity)) :
    (ofInputs threshold f inputs).SamplesFunction f :=
  samplesFunction_ofInputs_internal f inputs

/-- Canonical sampled-instance encodings decode to their original instances. -/
@[simp] theorem decode?_encode (inst : Instance) :
    decode? inst.encode = some inst :=
  decode?_encode_internal inst

/-- Instance decoding succeeds precisely on the canonical encoding of its result. -/
theorem decode?_eq_some_iff (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode :=
  decode?_eq_some_iff_internal bits inst

/-- Decoding rejects exactly strings that encode no sampled instance. -/
theorem decode?_eq_none_iff (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode :=
  decode?_eq_none_iff_internal bits

/-- The canonical sampled-instance encoding is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Exact instance-code length, separating the linear sample payload from
binary metadata. -/
@[simp] theorem length_encode (inst : Instance) :
    inst.encode.length =
      inst.samples.length * (4 * inst.arity + 8) +
        2 * inst.arity.size + 2 * inst.threshold.size +
          2 * inst.samples.length.size + 6 :=
  length_encode_internal inst

/-- At arity zero, a sampled instance is feasible exactly when one constant
bit satisfies every listed constraint. -/
theorem hasCircuitAtMost_of_arity_eq_zero_iff (inst : Instance)
    (harity : inst.arity = 0) :
    inst.HasCircuitAtMost ↔
      ∃ output : Bool, inst.SamplesFunction (fun _ => output) :=
  hasCircuitAtMost_of_arity_eq_zero_iff_internal inst harity

/-- At positive arity, feasibility has exactly the advertised sampled-circuit
witness semantics. -/
theorem hasCircuitAtMost_iff_exists_circuit (inst : Instance)
    [NeZero inst.arity] :
    inst.HasCircuitAtMost ↔
      ∃ (internalGates : ℕ)
          (circuit : Circuit Basis.andOr2 inst.arity 1 internalGates),
        circuit.size ≤ inst.threshold ∧
          inst.SamplesFunction (fun input => circuit.eval input 0) :=
  hasCircuitAtMost_iff_exists_circuit_internal inst

/-- Increasing the size threshold preserves sampled yes-instances. -/
theorem HasCircuitAtMost.mono (inst : Instance) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hsmall : ({ inst with threshold := first } : Instance).HasCircuitAtMost) :
    ({ inst with threshold := second } : Instance).HasCircuitAtMost :=
  hasCircuitAtMost_threshold_mono_internal inst hthreshold hsmall

end Instance

end SuccinctMCSP

/-- A canonical sampled-instance code belongs to `SuccinctMCSP` exactly when
its typed instance has a matching circuit within the threshold. -/
@[simp] theorem SuccinctMCSP.mem_encode_iff (inst : SuccinctMCSP.Instance) :
    inst.encode ∈ SuccinctMCSP ↔ inst.HasCircuitAtMost := by
  simp [SuccinctMCSP]

/-- Every malformed sampled-instance code is rejected. -/
theorem SuccinctMCSP.not_mem_of_decode?_eq_none {bits : List Bool}
    (hdecode : SuccinctMCSP.Instance.decode? bits = none) :
    bits ∉ SuccinctMCSP := by
  simp [SuccinctMCSP, hdecode]

/-- Membership exposes the unique decoded sampled instance and its exact
typed feasibility predicate. -/
theorem SuccinctMCSP.mem_iff_exists (bits : List Bool) :
    bits ∈ SuccinctMCSP ↔
      ∃ inst : SuccinctMCSP.Instance,
        SuccinctMCSP.Instance.decode? bits = some inst ∧
          inst.HasCircuitAtMost := by
  cases hdecode : SuccinctMCSP.Instance.decode? bits with
  | none => simp [SuccinctMCSP, hdecode]
  | some inst => simp [SuccinctMCSP, hdecode]

end Complexity
