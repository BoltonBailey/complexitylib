/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Chain.Defs
import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Internal

/-!
# Time-bounded description composition -- proof internals
-/


public section

namespace Complexity

theorem TimeBoundedProgramCompositionAt.restrict_bounds_internal
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {compile : List Bool → List Bool → List Bool}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime jointTime firstBound secondBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine compile firstOutput secondOutput firstTime secondTime
      jointTime firstBound secondBound)
    {smallerFirstBound smallerSecondBound : ℕ}
    (hfirst : smallerFirstBound ≤ firstBound)
    (hsecond : smallerSecondBound ≤ secondBound) :
    TimeBoundedProgramCompositionAt jointMachine firstMachine secondMachine
      compile firstOutput secondOutput firstTime secondTime jointTime
      smallerFirstBound smallerSecondBound := by
  intro firstProgram secondProgram hfirstLength hsecondLength
    hfirstProduce hsecondProduce
  exact hcompose firstProgram secondProgram
    (hfirstLength.trans hfirst) (hsecondLength.trans hsecond)
    hfirstProduce hsecondProduce

theorem TimeBoundedProgramCompositionAt.mono_jointTime_internal
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {compile : List Bool → List Bool → List Bool}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime firstJointTime secondJointTime firstBound secondBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine compile firstOutput secondOutput firstTime secondTime
      firstJointTime firstBound secondBound)
    (hjoint : firstJointTime ≤ secondJointTime) :
    TimeBoundedProgramCompositionAt jointMachine firstMachine secondMachine
      compile firstOutput secondOutput firstTime secondTime secondJointTime
      firstBound secondBound := by
  intro firstProgram secondProgram hfirstLength hsecondLength
    hfirstProduce hsecondProduce
  exact (hcompose firstProgram secondProgram hfirstLength hsecondLength
    hfirstProduce hsecondProduce).mono hjoint

theorem timeBoundedKolmogorovComplexity_pair_le_of_composition_internal
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {compile : List Bool → List Bool → List Bool}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime jointTime firstBound secondBound combinedBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine compile firstOutput secondOutput firstTime secondTime
      jointTime firstBound secondBound)
    (hlength : ∀ firstProgram secondProgram,
      firstProgram.length ≤ firstBound →
      secondProgram.length ≤ secondBound →
      (compile firstProgram secondProgram).length ≤ combinedBound)
    (hfirst : firstMachine.timeBoundedKolmogorovComplexity
      firstOutput firstTime ≤ (firstBound : WithTop ℕ))
    (hsecond : secondMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        secondOutput firstOutput secondTime ≤ (secondBound : WithTop ℕ)) :
    jointMachine.timeBoundedKolmogorovComplexity
        (pair firstOutput secondOutput) jointTime ≤
      (combinedBound : WithTop ℕ) := by
  obtain ⟨firstProgram, hfirstLength, hfirstProduce⟩ :=
    (TM.timeBoundedKolmogorovComplexity_le_coe_iff_internal
      firstMachine firstOutput firstTime firstBound).mp hfirst
  obtain ⟨secondProgram, hsecondLength, hsecondProduce⟩ :=
    (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
        secondMachine secondOutput firstOutput secondTime secondBound).mp hsecond
  exact le_trans
    (TM.timeBoundedKolmogorovComplexity_le_internal
      (hcompose firstProgram secondProgram hfirstLength hsecondLength
        hfirstProduce hsecondProduce))
    (WithTop.coe_le_coe.mpr
      (hlength firstProgram secondProgram hfirstLength hsecondLength))

theorem timeBoundedKolmogorovComplexity_pair_le_of_pair_composition_internal
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime jointTime firstBound secondBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine pair firstOutput secondOutput firstTime secondTime
      jointTime firstBound secondBound)
    (hfirst : firstMachine.timeBoundedKolmogorovComplexity
      firstOutput firstTime ≤ (firstBound : WithTop ℕ))
    (hsecond : secondMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        secondOutput firstOutput secondTime ≤ (secondBound : WithTop ℕ)) :
    jointMachine.timeBoundedKolmogorovComplexity
        (pair firstOutput secondOutput) jointTime ≤
      (2 * firstBound + 2 + secondBound : ℕ) := by
  apply timeBoundedKolmogorovComplexity_pair_le_of_composition_internal
    hcompose _ hfirst hsecond
  intro firstProgram secondProgram hfirstLength hsecondLength
  rw [pair_length]
  omega

theorem timeBoundedKolmogorovComplexity_pair_le_of_reverse_pair_composition_internal
    {jointTapes firstTapes secondTapes : ℕ}
    {jointMachine : TM jointTapes} {firstMachine : TM firstTapes}
    {secondMachine : OracleTM secondTapes}
    {firstOutput secondOutput : List Bool}
    {firstTime secondTime jointTime firstBound secondBound : ℕ}
    (hcompose : TimeBoundedProgramCompositionAt jointMachine firstMachine
      secondMachine (fun firstProgram secondProgram =>
        pair secondProgram firstProgram) firstOutput secondOutput
      firstTime secondTime jointTime firstBound secondBound)
    (hfirst : firstMachine.timeBoundedKolmogorovComplexity
      firstOutput firstTime ≤ (firstBound : WithTop ℕ))
    (hsecond : secondMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        secondOutput firstOutput secondTime ≤ (secondBound : WithTop ℕ)) :
    jointMachine.timeBoundedKolmogorovComplexity
        (pair firstOutput secondOutput) jointTime ≤
      (2 * secondBound + 2 + firstBound : ℕ) := by
  apply timeBoundedKolmogorovComplexity_pair_le_of_composition_internal
    hcompose _ hfirst hsecond
  intro firstProgram secondProgram hfirstLength hsecondLength
  rw [pair_length]
  omega

end Complexity
