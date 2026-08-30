/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Defs
public import Complexitylib.Metacomplexity.MCSP.Internal
public import Complexitylib.Metacomplexity.MCSP.Witness

/-!
# The Minimum Circuit Size Problem

This module exposes a canonical, total MCSP syntax and its exact relationship
to the library's Boolean circuit complexity measure.

## Main definitions

- `MCSP.Instance` -- arity, a structurally exact truth table, and threshold
- `MCSP.Instance.encode` / `decode?` -- canonical total binary codec
- `MCSP.Instance.function` -- little-endian truth-table semantics
- `MCSP.Instance.HasCircuitAtMost` -- direct circuit-witness predicate
- `MCSP.Instance.verifyRawCircuit` -- executable canonical witness checker
- `MCSP` -- encoded language, with malformed strings rejected

The zero-arity case is explicit: its one truth-table bit is stored directly and
has size zero, matching `CircuitFamily`. Positive arities use
`Basis.andOr2` and agree exactly with `Circuit.sizeComplexity`.
-/


public section

namespace Complexity

namespace MCSP

namespace Instance

/-- Every instance carries exactly `2^arity` truth-table bits. -/
@[simp] theorem length_tableBits (inst : Instance) :
    inst.tableBits.length = 2 ^ inst.arity :=
  length_tableBits_internal inst

/-- Converting a truth-table index to an input and back recovers the index. -/
@[simp] theorem inputIndex_inputOfIndex {arity : ℕ} (index : Fin (2 ^ arity)) :
    inputIndex (inputOfIndex index) = index :=
  inputIndex_inputOfIndex_internal index

/-- Converting a fixed-length input to its truth-table index and back recovers
the input. -/
@[simp] theorem inputOfIndex_inputIndex {arity : ℕ} (input : BitString arity) :
    inputOfIndex (inputIndex input) = input :=
  inputOfIndex_inputIndex_internal input

/-- Evaluating the represented function on index `k` returns truth-table entry
`k` under the canonical little-endian enumeration. -/
@[simp] theorem function_inputOfIndex (inst : Instance)
    (index : Fin (2 ^ inst.arity)) :
    inst.function (inputOfIndex index) = inst.table index :=
  function_inputOfIndex_internal inst index

/-- Changing the threshold does not change the represented function. -/
@[simp] theorem function_withThreshold (inst : Instance) (threshold : ℕ) :
    (inst.withThreshold threshold).function = inst.function :=
  function_withThreshold_internal inst threshold

/-- Canonical MCSP encodings decode to their original instances. -/
@[simp] theorem decode?_encode (inst : Instance) :
    decode? inst.encode = some inst :=
  decode?_encode_internal inst

/-- Exact decoding accepts precisely canonical encodings. -/
theorem decode?_eq_some_iff (bits : List Bool) (inst : Instance) :
    decode? bits = some inst ↔ bits = inst.encode :=
  decode?_eq_some_iff_internal bits inst

/-- Decoding rejects exactly those strings that are not canonical encodings of
any well-formed MCSP instance. -/
theorem decode?_eq_none_iff (bits : List Bool) :
    decode? bits = none ↔ ¬ ∃ inst : Instance, bits = inst.encode :=
  decode?_eq_none_iff_internal bits

/-- Canonical MCSP instance encoding is injective. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_internal

/-- Exact encoded length, exposing truth-table length `2^n` separately from
the logarithmic-width arity and threshold fields. -/
@[simp] theorem length_encode (inst : Instance) :
    inst.encode.length =
      2 ^ inst.arity + 2 * inst.arity.size +
        2 * inst.threshold.size + 4 :=
  length_encode_internal inst

/-- The truth-table payload is no longer than the complete instance code. -/
theorem tableLength_le_encodeLength (inst : Instance) :
    2 ^ inst.arity ≤ inst.encode.length := by
  rw [length_encode]
  omega

/-- Zero-input Boolean functions use the explicit size-zero family convention. -/
theorem minimumSize_of_arity_eq_zero (inst : Instance)
    (harity : inst.arity = 0) :
    inst.minimumSize = 0 :=
  minimumSize_of_arity_eq_zero_internal inst harity

/-- At every positive arity, MCSP uses exactly the existing fan-in-two circuit
complexity measure. -/
theorem minimumSize_eq_sizeComplexity (inst : Instance)
    [NeZero inst.arity] :
    inst.minimumSize =
      Circuit.sizeComplexity Basis.andOr2 inst.function :=
  minimumSize_eq_sizeComplexity_internal inst

/-- Every zero-arity instance is a yes-instance at every natural threshold. -/
theorem hasCircuitAtMost_of_arity_eq_zero (inst : Instance)
    (harity : inst.arity = 0) : inst.HasCircuitAtMost :=
  hasCircuitAtMost_of_arity_eq_zero_internal inst harity

/-- At positive arity, the direct circuit-witness semantics agrees with the
minimum circuit-size inequality. -/
theorem hasCircuitAtMost_iff_sizeComplexity_le (inst : Instance)
    [NeZero inst.arity] :
    inst.HasCircuitAtMost ↔
      Circuit.sizeComplexity Basis.andOr2 inst.function ≤ inst.threshold :=
  hasCircuitAtMost_iff_sizeComplexity_le_internal inst

/-- The total witness semantics agrees with the total minimum-size convention,
including arity zero. -/
theorem hasCircuitAtMost_iff_minimumSize_le (inst : Instance) :
    inst.HasCircuitAtMost ↔ inst.minimumSize ≤ inst.threshold :=
  hasCircuitAtMost_iff_minimumSize_le_internal inst

/-- Increasing the threshold preserves MCSP yes-instances. -/
theorem HasCircuitAtMost.mono (inst : Instance) {first second : ℕ}
    (hthreshold : first ≤ second)
    (hsmall : (inst.withThreshold first).HasCircuitAtMost) :
    (inst.withThreshold second).HasCircuitAtMost :=
  hasCircuitAtMost_withThreshold_mono_internal inst hthreshold hsmall

end Instance

end MCSP

/-- A canonical instance code belongs to MCSP exactly when the decoded
instance has a circuit at most its threshold. -/
@[simp] theorem MCSP.mem_encode_iff (inst : MCSP.Instance) :
    inst.encode ∈ MCSP ↔ inst.HasCircuitAtMost := by
  simp [MCSP]

/-- Membership of a canonical code is exactly its total minimum-size
inequality, including the explicit zero-arity convention. -/
theorem MCSP.mem_encode_iff_minimumSize_le (inst : MCSP.Instance) :
    inst.encode ∈ MCSP ↔ inst.minimumSize ≤ inst.threshold := by
  rw [MCSP.mem_encode_iff, MCSP.Instance.hasCircuitAtMost_iff_minimumSize_le]

/-- At positive arity, canonical encoded MCSP membership agrees exactly with
the library's existing fan-in-two size complexity. -/
theorem MCSP.mem_encode_iff_sizeComplexity_le (inst : MCSP.Instance)
    [NeZero inst.arity] :
    inst.encode ∈ MCSP ↔
      Circuit.sizeComplexity Basis.andOr2 inst.function ≤ inst.threshold := by
  rw [MCSP.mem_encode_iff, MCSP.Instance.hasCircuitAtMost_iff_sizeComplexity_le]

/-- The canonical code of every zero-arity instance is in MCSP. -/
theorem MCSP.mem_encode_of_arity_eq_zero (inst : MCSP.Instance)
    (harity : inst.arity = 0) : inst.encode ∈ MCSP := by
  rw [MCSP.mem_encode_iff]
  exact MCSP.Instance.hasCircuitAtMost_of_arity_eq_zero inst harity

/-- Every malformed instance code is rejected by the total MCSP language. -/
theorem MCSP.not_mem_of_decode?_eq_none {bits : List Bool}
    (hdecode : MCSP.Instance.decode? bits = none) : bits ∉ MCSP := by
  simp [MCSP, hdecode]

/-- Decoded language membership has an explicit unique-instance witness. -/
theorem MCSP.mem_iff_exists (bits : List Bool) :
    bits ∈ MCSP ↔
      ∃ inst : MCSP.Instance,
        MCSP.Instance.decode? bits = some inst ∧ inst.HasCircuitAtMost := by
  cases hdecode : MCSP.Instance.decode? bits with
  | none => simp [MCSP, hdecode]
  | some inst => simp [MCSP, hdecode]

end Complexity
