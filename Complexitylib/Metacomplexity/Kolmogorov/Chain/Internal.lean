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

theorem TimeBoundedConditionalPairCompositionAt.restrict_bounds_internal
    {jointTapes conditionTapes resultTapes : ℕ}
    {jointMachine : TM jointTapes} {conditionMachine : TM conditionTapes}
    {resultMachine : OracleTM resultTapes}
    {compile : List Bool → List Bool → List Bool}
    {result condition : List Bool}
    {conditionTime resultTime jointTime conditionBound resultBound : ℕ}
    (hcompose : TimeBoundedConditionalPairCompositionAt jointMachine
      conditionMachine resultMachine compile result condition conditionTime
      resultTime jointTime conditionBound resultBound)
    {smallerConditionBound smallerResultBound : ℕ}
    (hcondition : smallerConditionBound ≤ conditionBound)
    (hresult : smallerResultBound ≤ resultBound) :
    TimeBoundedConditionalPairCompositionAt jointMachine conditionMachine
      resultMachine compile result condition conditionTime resultTime jointTime
      smallerConditionBound smallerResultBound := by
  intro conditionProgram resultProgram hconditionLength hresultLength
    hconditionProduce hresultProduce
  exact hcompose conditionProgram resultProgram
    (hconditionLength.trans hcondition) (hresultLength.trans hresult)
    hconditionProduce hresultProduce

theorem TimeBoundedConditionalPairCompositionAt.mono_jointTime_internal
    {jointTapes conditionTapes resultTapes : ℕ}
    {jointMachine : TM jointTapes} {conditionMachine : TM conditionTapes}
    {resultMachine : OracleTM resultTapes}
    {compile : List Bool → List Bool → List Bool}
    {result condition : List Bool}
    {conditionTime resultTime firstJointTime secondJointTime
      conditionBound resultBound : ℕ}
    (hcompose : TimeBoundedConditionalPairCompositionAt jointMachine
      conditionMachine resultMachine compile result condition conditionTime
      resultTime firstJointTime conditionBound resultBound)
    (hjoint : firstJointTime ≤ secondJointTime) :
    TimeBoundedConditionalPairCompositionAt jointMachine conditionMachine
      resultMachine compile result condition conditionTime resultTime
      secondJointTime conditionBound resultBound := by
  intro conditionProgram resultProgram hconditionLength hresultLength
    hconditionProduce hresultProduce
  exact (hcompose conditionProgram resultProgram hconditionLength hresultLength
    hconditionProduce hresultProduce).mono hjoint

theorem timeBoundedKolmogorovComplexity_pair_le_add_of_conditional_composition_internal
    {jointTapes conditionTapes resultTapes : ℕ}
    {jointMachine : TM jointTapes} {conditionMachine : TM conditionTapes}
    {resultMachine : OracleTM resultTapes}
    {compile : List Bool → List Bool → List Bool}
    {result condition : List Bool}
    {conditionTime resultTime jointTime conditionBound resultBound constant : ℕ}
    (hcompose : TimeBoundedConditionalPairCompositionAt jointMachine
      conditionMachine resultMachine compile result condition conditionTime
      resultTime jointTime conditionBound resultBound)
    (hlength : ∀ conditionProgram resultProgram,
      conditionProgram.length ≤ conditionBound →
      resultProgram.length ≤ resultBound →
      (compile conditionProgram resultProgram).length ≤
        resultProgram.length + conditionProgram.length + constant)
    (hconditionFinite : conditionMachine.timeBoundedKolmogorovComplexity
      condition conditionTime ≠ ⊤)
    (hresultFinite :
      resultMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        result condition resultTime ≠ ⊤)
    (hconditionBound : conditionMachine.timeBoundedKolmogorovComplexity
      condition conditionTime ≤ (conditionBound : WithTop ℕ))
    (hresultBound :
      resultMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
        result condition resultTime ≤ (resultBound : WithTop ℕ)) :
    jointMachine.timeBoundedKolmogorovComplexity
        (pair result condition) jointTime ≤
      resultMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
            result condition resultTime +
          conditionMachine.timeBoundedKolmogorovComplexity
            condition conditionTime +
        (constant : WithTop ℕ) := by
  obtain ⟨conditionProgram, hconditionValue, hconditionProduce⟩ :=
    TM.timeBoundedKolmogorovComplexity_witness_internal
      conditionMachine condition conditionTime hconditionFinite
  obtain ⟨resultProgram, hresultValue, hresultProduce⟩ :=
    OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_witness_internal
      resultMachine result condition resultTime hresultFinite
  have hconditionLength : conditionProgram.length ≤ conditionBound := by
    have hbound := hconditionBound
    rw [← hconditionValue] at hbound
    exact (WithTop.coe_le_coe (α := ℕ)).mp hbound
  have hresultLength : resultProgram.length ≤ resultBound := by
    have hbound := hresultBound
    rw [← hresultValue] at hbound
    exact (WithTop.coe_le_coe (α := ℕ)).mp hbound
  calc
    jointMachine.timeBoundedKolmogorovComplexity
          (pair result condition) jointTime ≤
        ((compile conditionProgram resultProgram).length : ℕ) :=
      TM.timeBoundedKolmogorovComplexity_le_internal <|
        hcompose conditionProgram resultProgram hconditionLength hresultLength
          hconditionProduce hresultProduce
    _ ≤ (resultProgram.length + conditionProgram.length + constant : ℕ) :=
      WithTop.coe_le_coe.mpr <|
        hlength conditionProgram resultProgram hconditionLength hresultLength
    _ = resultMachine.randomAccessConditionalTimeBoundedKolmogorovComplexity
              result condition resultTime +
            conditionMachine.timeBoundedKolmogorovComplexity
              condition conditionTime +
          (constant : WithTop ℕ) := by
      rw [← hresultValue, ← hconditionValue]
      rfl

end Complexity
