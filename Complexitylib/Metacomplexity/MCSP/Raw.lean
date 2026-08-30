/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Gap.Slice
public import Complexitylib.Metacomplexity.MCSP.Raw.Defs
public import Complexitylib.Metacomplexity.MCSP.Raw.Internal

/-!
# Raw truth-table MCSP

This module exposes the input convention used by standard hardness-
magnification statements: an input is exactly an `N = 2^n`-bit truth table,
while the circuit-size thresholds are external parameters. It proves exact
decoder semantics, raw/canonical round trips, and side-preserving maps in both
directions between raw and metadata-bearing GapMCSP slices.

The maps below are semantic `MapReducesVia` witnesses. Their polynomial-time
machine realizations are intentionally separate future obligations.
-/


public section

namespace Complexity

namespace MCSP

/-- A raw truth table of length `2^arity` has recovered arity exactly `arity`. -/
theorem rawArity_eq_of_length_eq_pow (bits : List Bool) {arity : ℕ}
    (hlength : bits.length = 2 ^ arity) :
    rawArity bits = arity :=
  rawArity_eq_of_length_eq_pow_internal bits hlength

/-- Well-formedness is equivalent to the decoder's concrete power-of-two
length check at the recovered arity. -/
theorem isRawTruthTable_iff_length_eq_pow_rawArity (bits : List Bool) :
    IsRawTruthTable bits ↔ bits.length = 2 ^ rawArity bits :=
  isRawTruthTable_iff_length_eq_pow_rawArity_internal bits

/-- Erasing metadata from a canonical instance preserves its arity. -/
@[simp] theorem rawArity_tableBits (inst : Instance) :
    rawArity inst.tableBits = inst.arity :=
  rawArity_tableBits_internal inst

/-- Decoding a canonical instance's raw table reinstalls exactly the externally
chosen threshold. -/
@[simp] theorem rawDecode?_tableBits (threshold : ℕ → ℕ) (inst : Instance) :
    rawDecode? threshold inst.tableBits =
      some (inst.withThreshold (threshold inst.arity)) :=
  rawDecode?_tableBits_internal threshold inst

/-- Exact characterization of successful raw decoding. -/
theorem rawDecode?_eq_some_iff
    (threshold : ℕ → ℕ) (bits : List Bool) (inst : Instance) :
    rawDecode? threshold bits = some inst ↔
      bits = inst.tableBits ∧ inst.threshold = threshold inst.arity :=
  rawDecode?_eq_some_iff_internal threshold bits inst

/-- Raw decoding fails exactly at non-power-of-two lengths. -/
theorem rawDecode?_eq_none_iff (threshold : ℕ → ℕ) (bits : List Bool) :
    rawDecode? threshold bits = none ↔ ¬ IsRawTruthTable bits :=
  rawDecode?_eq_none_iff_internal threshold bits

/-- Adding metadata to canonical table bits only replaces the threshold. -/
@[simp] theorem rawToCanonical_tableBits
    (threshold : ℕ → ℕ) (inst : Instance) :
    rawToCanonical threshold inst.tableBits =
      (inst.withThreshold (threshold inst.arity)).encode :=
  rawToCanonical_tableBits_internal threshold inst

/-- Erasing metadata from an encoded instance recovers its exact truth table. -/
@[simp] theorem canonicalToRaw_encode (inst : Instance) :
    canonicalToRaw inst.encode = inst.tableBits :=
  canonicalToRaw_encode_internal inst

/-- Adding and then erasing metadata is the identity on every raw truth table. -/
theorem canonicalToRaw_rawToCanonical
    (threshold : ℕ → ℕ) {bits : List Bool}
    (hraw : IsRawTruthTable bits) :
    canonicalToRaw (rawToCanonical threshold bits) = bits :=
  canonicalToRaw_rawToCanonical_internal threshold hraw

/-- Erasing and reinstalling metadata preserves the table and installs the
externally chosen threshold. -/
theorem rawToCanonical_canonicalToRaw_encode
    (threshold : ℕ → ℕ) (inst : Instance) :
    rawToCanonical threshold (canonicalToRaw inst.encode) =
      (inst.withThreshold (threshold inst.arity)).encode :=
  rawToCanonical_canonicalToRaw_encode_internal threshold inst

/-- Raw threshold-slice membership has the expected minimum-size semantics. -/
@[simp] theorem mem_rawAtThreshold_tableBits_iff
    (threshold : ℕ → ℕ) (inst : Instance) :
    inst.tableBits ∈ rawAtThreshold threshold ↔
      inst.minimumSize ≤ threshold inst.arity :=
  mem_rawAtThreshold_tableBits_iff_internal threshold inst

/-- Every member of raw `MCSP[threshold]` is exactly a canonical truth table
whose minimum circuit size meets the external threshold. -/
theorem mem_rawAtThreshold_iff_exists
    (threshold : ℕ → ℕ) (bits : List Bool) :
    bits ∈ rawAtThreshold threshold ↔
      ∃ inst : Instance,
        bits = inst.tableBits ∧ inst.minimumSize ≤ threshold inst.arity :=
  mem_rawAtThreshold_iff_exists_internal threshold bits

end MCSP

namespace GapMCSP

/-- Exact yes-side semantics for raw GapMCSP truth tables. -/
@[simp] theorem mem_rawSliceYesLanguage_tableBits_iff
    (parameters : SliceParameters) (inst : MCSP.Instance) :
    inst.tableBits ∈ rawSliceYesLanguage parameters ↔
      inst.minimumSize ≤ parameters.yesThreshold inst.arity :=
  mem_rawSliceYesLanguage_tableBits_iff_internal parameters inst

/-- Exact no-side semantics for raw GapMCSP truth tables. -/
@[simp] theorem mem_rawSliceNoLanguage_tableBits_iff
    (parameters : SliceParameters) (inst : MCSP.Instance) :
    inst.tableBits ∈ rawSliceNoLanguage parameters ↔
      parameters.noThreshold inst.arity < inst.minimumSize :=
  mem_rawSliceNoLanguage_tableBits_iff_internal parameters inst

/-- A pointwise threshold gap makes the raw yes and no languages disjoint. -/
theorem disjoint_rawSliceLanguages
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    Disjoint (rawSliceYesLanguage parameters)
      (rawSliceNoLanguage parameters) :=
  disjoint_rawSliceLanguages_internal parameters hgap

/-- Every raw yes-instance has exactly `2^arity` input bits for some arity. -/
theorem mem_rawSliceYesLanguage_imp_isRawTruthTable
    (parameters : SliceParameters) {bits : List Bool}
    (hmem : bits ∈ rawSliceYesLanguage parameters) :
    MCSP.IsRawTruthTable bits :=
  mem_rawSliceYesLanguage_imp_isRawTruthTable_internal parameters hmem

/-- Every raw no-instance has exactly `2^arity` input bits for some arity. -/
theorem mem_rawSliceNoLanguage_imp_isRawTruthTable
    (parameters : SliceParameters) {bits : List Bool}
    (hmem : bits ∈ rawSliceNoLanguage parameters) :
    MCSP.IsRawTruthTable bits :=
  mem_rawSliceNoLanguage_imp_isRawTruthTable_internal parameters hmem

/-- Raw `GapMCSP[s_yes,s_no]` on bare truth-table inputs. -/
@[expose]
def rawSliceProblem (parameters : SliceParameters)
    (hgap : parameters.IsGap) : PromiseProblem where
  yesInstances := rawSliceYesLanguage parameters
  noInstances := rawSliceNoLanguage parameters
  disjoint := disjoint_rawSliceLanguages parameters hgap

@[simp] theorem rawSliceProblem_yesInstances
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    (rawSliceProblem parameters hgap).yesInstances =
      rawSliceYesLanguage parameters := rfl

@[simp] theorem rawSliceProblem_noInstances
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    (rawSliceProblem parameters hgap).noInstances =
      rawSliceNoLanguage parameters := rfl

/-- Every input in the raw GapMCSP promise has length exactly `2^arity` for
some arity. -/
theorem mem_rawSliceProblem_promise_imp_isRawTruthTable
    (parameters : SliceParameters) (hgap : parameters.IsGap)
    {bits : List Bool} (hmem : bits ∈ (rawSliceProblem parameters hgap).promise) :
    MCSP.IsRawTruthTable bits := by
  rcases hmem with hyes | hno
  · exact mem_rawSliceYesLanguage_imp_isRawTruthTable parameters hyes
  · exact mem_rawSliceNoLanguage_imp_isRawTruthTable parameters hno

/-- Adding canonical metadata preserves both promised sides of a GapMCSP
slice. This is a semantic reduction, not yet an `FP` theorem. -/
theorem rawSliceProblem_mapReducesVia_rawToCanonical
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    (rawSliceProblem parameters hgap).MapReducesVia
      (sliceProblem parameters hgap)
      (MCSP.rawToCanonical parameters.yesThreshold) :=
  rawSliceProblem_mapReducesVia_rawToCanonical_internal parameters hgap

/-- Erasing canonical metadata preserves both promised sides of a GapMCSP
slice. This is a semantic reduction, not yet an `FP` theorem. -/
theorem sliceProblem_mapReducesVia_canonicalToRaw
    (parameters : SliceParameters) (hgap : parameters.IsGap) :
    (sliceProblem parameters hgap).MapReducesVia
      (rawSliceProblem parameters hgap)
      MCSP.canonicalToRaw :=
  sliceProblem_mapReducesVia_canonicalToRaw_internal parameters hgap

end GapMCSP

end Complexity
