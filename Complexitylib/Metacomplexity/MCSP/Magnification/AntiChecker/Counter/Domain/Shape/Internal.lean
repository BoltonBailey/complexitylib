/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain.Shape.Defs
import Complexitylib.Metacomplexity.MCSP.AntiChecker.Enumeration
import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Counter.Domain

/-!
# Finite shapes of bounded circuit codes -- proof internals
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

namespace CandidateCodeShape

theorem card_le_internal (bound threshold : ℕ) :
    Fintype.card (CandidateCodeShape bound threshold) ≤
      threshold * (bound + 1) := by
  calc
    Fintype.card (CandidateCodeShape bound threshold) ≤
        Fintype.card (Fin threshold × Fin (bound + 1)) :=
      Fintype.card_subtype_le _
    _ = threshold * (bound + 1) := by simp

theorem one_le_gateCount_internal {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) :
    1 ≤ shape.gateCount := by
  simp [gateCount]

theorem gateCount_le_threshold_internal {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) :
    shape.gateCount ≤ threshold := by
  have := shape.val.1.isLt
  simp [gateCount]

theorem countPrefix_le_codeLength_internal {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) :
    shape.gateCount + 1 ≤ shape.codeLength := by
  exact shape.property

theorem codeLength_le_bound_internal {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold) :
    shape.codeLength ≤ bound := by
  have := shape.val.2.isLt
  simp [codeLength]
  omega

theorem length_code_internal {bound threshold : ℕ}
    (shape : CandidateCodeShape bound threshold)
    (encoded : BitString (boundedCodeWidth bound)) :
    (shape.code encoded).length = shape.codeLength := by
  have hprefix := countPrefix_le_codeLength_internal shape
  simp only [code, List.length_append, CircuitCode.NatCode.length_encode,
    BitString.length_toList, gateBodyWidth]
  omega

private def ofCircuit {bound threshold : ℕ}
    (circuit : CircuitCode.RawCircuit) (hnonempty : circuit ≠ [])
    (hthreshold : circuit.length ≤ threshold)
    (hbound : circuit.encode.length ≤ bound) :
    CandidateCodeShape bound threshold :=
  ⟨(⟨circuit.length - 1, by
        have hpositive : circuit.length ≠ 0 := by
          intro hzero
          apply hnonempty
          exact List.eq_nil_of_length_eq_zero hzero
        omega⟩,
      ⟨circuit.encode.length, by omega⟩), by
    have hprefix : circuit.length + 1 ≤ circuit.encode.length := by
      simp [CircuitCode.RawCircuit.encode]
    have hpositive : circuit.length ≠ 0 := by
      intro hzero
      apply hnonempty
      exact List.eq_nil_of_length_eq_zero hzero
    change circuit.length - 1 + 2 ≤ circuit.encode.length
    omega⟩

@[simp] private theorem gateCount_ofCircuit {bound threshold : ℕ}
    (circuit : CircuitCode.RawCircuit) (hnonempty : circuit ≠ [])
    (hthreshold : circuit.length ≤ threshold)
    (hbound : circuit.encode.length ≤ bound) :
    (ofCircuit circuit hnonempty hthreshold hbound).gateCount =
      circuit.length := by
  change circuit.length - 1 + 1 = circuit.length
  have hpositive : circuit.length ≠ 0 := by
    intro hzero
    apply hnonempty
    exact List.eq_nil_of_length_eq_zero hzero
  omega

@[simp] private theorem codeLength_ofCircuit {bound threshold : ℕ}
    (circuit : CircuitCode.RawCircuit) (hnonempty : circuit ≠ [])
    (hthreshold : circuit.length ≤ threshold)
    (hbound : circuit.encode.length ≤ bound) :
    (ofCircuit circuit hnonempty hthreshold hbound).codeLength =
      circuit.encode.length := by
  rfl

private theorem gateBodyWidth_ofCircuit {bound threshold : ℕ}
    (circuit : CircuitCode.RawCircuit) (hnonempty : circuit ≠ [])
    (hthreshold : circuit.length ≤ threshold)
    (hbound : circuit.encode.length ≤ bound) :
    (ofCircuit circuit hnonempty hthreshold hbound).gateBodyWidth =
      (circuit.flatMap CircuitCode.RawGate.encode).length := by
  rw [gateBodyWidth, gateCount_ofCircuit, codeLength_ofCircuit,
    CircuitCode.RawCircuit.encode, List.length_append,
    CircuitCode.NatCode.length_encode]
  omega

private theorem toList_gateBody_encodeBoundedCode_ofCircuit
    {bound threshold : ℕ} (circuit : CircuitCode.RawCircuit)
    (hnonempty : circuit ≠ []) (hthreshold : circuit.length ≤ threshold)
    (hbound : circuit.encode.length ≤ bound) :
    ((ofCircuit circuit hnonempty hthreshold hbound).gateBody
        (encodeBoundedCode bound circuit.encode)).toList =
      circuit.flatMap CircuitCode.RawGate.encode := by
  let shape := ofCircuit circuit hnonempty hthreshold hbound
  let body := circuit.flatMap CircuitCode.RawGate.encode
  change
    (shape.gateBody (encodeBoundedCode bound circuit.encode)).toList = body
  have hshapeCount : shape.gateCount = circuit.length := by
    simp [shape]
  have hshapeLength : shape.codeLength = circuit.encode.length := by
    simp [shape]
  have hbodyWidth : shape.gateBodyWidth = body.length := by
    simpa [shape, body] using
      gateBodyWidth_ofCircuit circuit hnonempty hthreshold hbound
  apply List.ext_get
  · simp [hbodyWidth]
  · intro index hleft hright
    have hindex : circuit.length + 1 + index < circuit.encode.length := by
      rw [CircuitCode.RawCircuit.encode, List.length_append,
        CircuitCode.NatCode.length_encode]
      simp only [body] at hright ⊢
      omega
    simp only [BitString.toList, List.get_ofFn]
    change
      encodeBoundedCode bound circuit.encode
          ⟨shape.gateCount + 1 + index, by
            have hcoordinate : index < shape.gateBodyWidth := by omega
            have hprefix := countPrefix_le_codeLength_internal shape
            have hlength := codeLength_le_bound_internal shape
            simp only [gateBodyWidth] at hcoordinate
            simp only [boundedCodeWidth]
            omega⟩ = body[index]
    unfold encodeBoundedCode
    rw [dif_pos (by simpa [hshapeCount] using hindex)]
    calc
      circuit.encode[shape.gateCount + 1 + index] =
          circuit.encode[circuit.length + 1 + index] := by
        congr 1
        omega
      _ = body[index] := by
        change
          (CircuitCode.NatCode.encode circuit.length ++ body)[
              circuit.length + 1 + index] = body[index]
        rw [List.getElem_append_right]
        · simp [CircuitCode.NatCode.length_encode]
        · simp [CircuitCode.NatCode.length_encode]

private theorem code_encodeBoundedCode_ofCircuit
    {bound threshold : ℕ} (circuit : CircuitCode.RawCircuit)
    (hnonempty : circuit ≠ []) (hthreshold : circuit.length ≤ threshold)
    (hbound : circuit.encode.length ≤ bound) :
    (ofCircuit circuit hnonempty hthreshold hbound).code
        (encodeBoundedCode bound circuit.encode) = circuit.encode := by
  rw [code, gateCount_ofCircuit,
    toList_gateBody_encodeBoundedCode_ofCircuit]
  rfl

private theorem matches_encodeBoundedCode_ofCircuit
    {bound threshold : ℕ} (circuit : CircuitCode.RawCircuit)
    (hnonempty : circuit ≠ []) (hthreshold : circuit.length ≤ threshold)
    (hbound : circuit.encode.length ≤ bound) :
    (ofCircuit circuit hnonempty hthreshold hbound).Matches
      (encodeBoundedCode bound circuit.encode) := by
  unfold Matches
  rw [code_encodeBoundedCode_ofCircuit]

private theorem exists_of_isSmallCircuitCode {arity bound threshold : ℕ}
    {code : List Bool}
    (hsmall : AntiChecker.IsSmallCircuitCode arity threshold code)
    (hbound : code.length ≤ bound) :
    ∃ shape : CandidateCodeShape bound threshold,
      shape.Matches (encodeBoundedCode bound code) ∧
        shape.code (encodeBoundedCode bound code) = code := by
  unfold AntiChecker.IsSmallCircuitCode at hsmall
  cases hdecode : CircuitCode.RawCircuit.decode? code with
  | none => simp [hdecode] at hsmall
  | some circuit =>
      simp only [hdecode] at hsmall
      have hcode : code = circuit.encode :=
        (CircuitCode.RawCircuit.decode?_eq_some_iff code circuit).mp hdecode
      subst code
      let shape := ofCircuit circuit hsmall.1.1 hsmall.2 hbound
      refine ⟨shape, ?_, ?_⟩
      · exact matches_encodeBoundedCode_ofCircuit
          circuit hsmall.1.1 hsmall.2 hbound
      · exact code_encodeBoundedCode_ofCircuit
          circuit hsmall.1.1 hsmall.2 hbound

theorem mem_encodedCandidateLabeledSurvivorCodes_iff_exists_shape_internal
    {count arity threshold : ℕ}
    {samples : Fin count → SuccinctMCSP.Sample arity}
    {encoded : BitString (candidateCodeWidth arity threshold)} :
    encoded ∈ encodedCandidateLabeledSurvivorCodes arity threshold samples ↔
      ∃ shape : CandidateCodeShape
          (AntiChecker.codeLengthBound arity threshold) threshold,
        shape.Matches encoded ∧
          AntiChecker.IsSmallCircuitCode arity threshold
            (shape.code encoded) ∧
          CodeMatchesLabeledSamples samples (shape.code encoded) := by
  rw [mem_encodedCandidateLabeledSurvivorCodes_iff]
  constructor
  · rintro ⟨code, hcode, rfl⟩
    have hfilter := Finset.mem_filter.mp hcode
    obtain ⟨hbound, hsmall⟩ :=
      AntiChecker.mem_candidateCodes_iff.mp hfilter.1
    obtain ⟨shape, hmatches, hshapeCode⟩ :=
      exists_of_isSmallCircuitCode hsmall hbound
    refine ⟨shape, hmatches, ?_, ?_⟩
    · simpa [hshapeCode] using hsmall
    · simpa [hshapeCode] using hfilter.2
  · rintro ⟨shape, hmatches, hsmall, hsamples⟩
    refine ⟨shape.code encoded, ?_, hmatches⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply AntiChecker.mem_candidateCodes_iff.mpr
      constructor
      · rw [length_code_internal]
        exact codeLength_le_bound_internal shape
      · exact hsmall
    · exact hsamples

end CandidateCodeShape

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
