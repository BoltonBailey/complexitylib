/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Defs
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Internal
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Selection
public import Complexitylib.Metacomplexity.MCSP.Magnification.AntiChecker.Generator.Round

/-!
# Typed Anti-Checker Lemma generators

This module exposes the exact multi-output generator interface from the
Oliveira--Pich--Santhanam Anti-Checker Lemma. `HasGenerators` is only the
lemma's conclusion; no theorem deriving it from `NP ⊆ PPoly` is asserted here.
-/


public section

namespace Complexity

namespace GapMCSP

namespace Magnification

namespace AntiCheckerLemma

/-- Packed samples use row-major indexing. -/
@[simp] theorem unpackSample_apply {count arity : ℕ}
    (output : BitString (count * arity)) (sample : Fin count)
    (coordinate : Fin arity) :
    unpackSample output sample coordinate =
      output (finProdFinEquiv (sample, coordinate)) :=
  unpackSample_apply_internal output sample coordinate

/-- Unpacking produces exactly the requested number of samples. -/
@[simp] theorem length_unpackSamples {count arity : ℕ}
    (output : BitString (count * arity)) :
    (unpackSamples output).length = count :=
  length_unpackSamples_internal output

/-- Reading sample `i` after unpacking returns row `i` of the packed output. -/
@[simp] theorem getElem_unpackSamples {count arity : ℕ}
    (output : BitString (count * arity)) (sample : Fin count) :
    (unpackSamples output)[sample.val]'(by
      rw [length_unpackSamples output]
      exact sample.isLt) = unpackSample output sample :=
  getElem_unpackSamples_internal output sample

/-- The generator's canonical input table stores the target at its canonical
little-endian input index. -/
@[simp] theorem truthTable_inputIndex {arity : ℕ}
    (target : BitString arity → Bool) (input : BitString arity) :
    truthTable target (MCSP.Instance.inputIndex input) = target input :=
  truthTable_inputIndex_internal target input

/-- Hardness is strict minimum circuit size above the large threshold. -/
theorem isHardAt_iff_minimumSize_gt {arity : ℕ}
    (beta : PositiveRationalScale) (target : BitString arity → Bool) :
    IsHardAt beta target ↔
      hardThreshold beta arity <
        (MCSP.Instance.ofFunction arity
          (hardThreshold beta arity) target).minimumSize :=
  isHardAt_iff_minimumSize_gt_internal beta target

/-- At positive arity, hardness uses the library's exact fan-in-two circuit
complexity measure. -/
theorem isHardAt_iff_sizeComplexity_gt {arity : ℕ}
    [NeZero arity] (beta : PositiveRationalScale)
    (target : BitString arity → Bool) :
    IsHardAt beta target ↔
      hardThreshold beta arity <
        Circuit.sizeComplexity Basis.andOr2 target :=
  isHardAt_iff_sizeComplexity_gt_internal beta target

namespace Generator

/-- Every generator run prints exactly the selected sample count. -/
@[simp] theorem length_inputs {overhead arity : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (generator : Generator overhead beta arity)
    (table : BitString (2 ^ arity)) :
    (generator.inputs table).length = sampleCount beta arity :=
  length_inputs_internal generator table

/-- Target-specialized generation preserves the exact sample count. -/
@[simp] theorem length_inputsFor {overhead arity : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (generator : Generator overhead beta arity)
    (target : BitString arity → Bool) :
    (generator.inputsFor target).length = sampleCount beta arity :=
  length_inputsFor_internal generator target

/-- Merely printing the packed outputs already consumes no more gates than the
generator's stated size bound. -/
theorem outputBitCount_le_sizeBound {overhead arity : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (generator : Generator overhead beta arity) :
    outputBitCount beta arity ≤
      generatorSizeBound overhead beta arity :=
  outputBitCount_le_sizeBound_internal generator

/-- Exact encoded SuccinctMCSP form of the generator's anti-checker contract. -/
theorem isCorrect_iff_encode_not_mem {overhead arity : ℕ}
    {beta : PositiveRationalScale} [NeZero arity]
    (generator : Generator overhead beta arity) :
    generator.IsCorrect ↔
      ∀ target, IsHardAt beta target →
        (SuccinctMCSP.Instance.ofInputs (smallThreshold beta arity)
          target (generator.inputsFor target)).encode ∉
            Complexity.SuccinctMCSP :=
  isCorrect_iff_encode_not_mem_internal generator

end Generator

/-- At a nonzero arity, the total existence predicate is the expected typed
generator existence statement. -/
theorem existsCorrectGeneratorAt_iff_of_ne
    (overhead : ℕ) (beta : PositiveRationalScale) {arity : ℕ}
    (harity : arity ≠ 0) :
    ExistsCorrectGeneratorAt overhead beta arity ↔
      letI : NeZero arity := ⟨harity⟩
      ∃ generator : Generator overhead beta arity, generator.IsCorrect :=
  existsCorrectGeneratorAt_iff_of_ne_internal overhead beta harity

/-- Cutoff form of the small-positive-`beta` quantifier, retaining the
independent sufficiently-large-arity quantifier. -/
theorem hasGenerators_iff_cutoff :
    HasGenerators ↔
      ∃ (overhead : ℕ) (cutoff : PositiveRationalScale),
        ∀ beta ≤ cutoff,
          ∀ᶠ arity in Filter.atTop,
            ExistsCorrectGeneratorAt overhead beta arity :=
  hasGenerators_iff_cutoff_internal

end AntiCheckerLemma

end Magnification

end GapMCSP

end Complexity
