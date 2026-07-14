/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Finalization
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Initialization
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Program
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Tableau.Defs
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Generator.Transition.Step
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Padded
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Serializer.Finalization
import Complexitylib.Classes.PPoly.Uniform.Unrolling.Stream
import Complexitylib.Models.TuringMachine.Experimental.BinaryRoutine.InputLength

/-!
# Complete direct-unrolling generator -- proof internals

This file first verifies the outer transition-layer loop. Its pure trajectory
keeps the step scratch convention reusable, preserves the horizon, and advances
the dedicated layer counter exactly once per emitted packed step.
-/

namespace Complexity

namespace CircuitUnrolling

namespace Serializer

namespace DirectGenerator

private theorem stepLoopValues_invariant (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (count : ℕ) :
    let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
      values count
    StepClean current ∧ current Work.horizon = values Work.horizon ∧
      current Work.loop₂ = values Work.loop₂ + count := by
  induction count with
  | zero => simp [BinaryRoutine.binaryForValues, hclean]
  | succ count ih =>
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      have hcurrentClean : StepClean current := ih.1
      have hcurrentHorizon : current Work.horizon = values Work.horizon := ih.2.1
      have hcurrentLoop : current Work.loop₂ = values Work.loop₂ + count :=
        ih.2.2
      have hhorizonCurrent : 0 < current Work.horizon := by
        simpa [hcurrentHorizon] using hhorizon
      have hstepClean : StepClean ((emitStep tm).effect current) :=
        emitStep_preserves_clean tm current hcurrentClean hhorizonCurrent
      have hnextClean : StepClean
          (Function.update ((emitStep tm).effect current) Work.loop₂
            (current Work.loop₂ + 1)) :=
        hstepClean.updateOuter_forEffect_internal _ Work.loop₂ _
          (Or.inr (Or.inr (Or.inr rfl)))
      have hstepHorizon :
          (emitStep tm).effect current Work.horizon = current Work.horizon := by
        rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
        simp [Work.available, Work.configBase, Work.gateBound, Work.gateCount,
          Work.horizon]
      change StepClean
          (BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current) ∧
        BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current
            Work.horizon = values Work.horizon ∧
        BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current
            Work.loop₂ = values Work.loop₂ + (count + 1)
      refine ⟨hnextClean, ?_, ?_⟩
      · exact hstepHorizon.trans hcurrentHorizon
      · calc
          current Work.loop₂ + 1 =
              (values Work.loop₂ + count) + 1 := by rw [hcurrentLoop]
          _ = values Work.loop₂ + (count + 1) := by omega

private theorem stepLoopValues_frontier (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (count : ℕ) :
    BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ values count
        Work.frontier = values Work.frontier := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      have hinvariant := stepLoopValues_invariant tm values hclean hhorizon count
      have hcurrentClean : StepClean current := hinvariant.1
      have hcurrentHorizon : current Work.horizon = values Work.horizon :=
        hinvariant.2.1
      have hhorizonCurrent : 0 < current Work.horizon := by
        simpa [hcurrentHorizon] using hhorizon
      rw [BinaryRoutine.binaryForValues]
      change Function.update ((emitStep tm).effect current) Work.loop₂
          (current Work.loop₂ + 1) Work.frontier = values Work.frontier
      rw [Function.update_of_ne (by decide),
        emitStep_effect tm current hcurrentClean hhorizonCurrent]
      simpa [Work.available, Work.configBase, Work.gateBound, Work.gateCount,
        Work.frontier] using ih

private theorem stepScheduleSize_eq_directStepSizeInternal (tm : NTM k)
    (T configBase : ℕ) :
    stepScheduleSize (transitionCases tm).length (Fintype.card tm.Q) k T
        (stepAtomKindAt tm T) (stepAtomEffectSelectedAt tm T)
        (effectCaseChoiceAt tm) = directStepSize tm T := by
  rw [← stepFragmentSize_eq_stepScheduleSize tm T configBase 0,
    stepFragmentSize_eq_directStepSize]

private theorem initializationEndpoint (tm : TM k) (q : Polynomial ℕ)
    (n : ℕ) :
    let values := preambleValues tm q
      (BinaryRoutine.inputLengthValues Work.inputLength n)
    let T := (TM.directSerializerHorizonPolynomial q).eval n
    let final := (initialization tm).effect values
    StepClean final ∧ final Work.horizon = T ∧ final Work.loop₂ = 0 ∧
      final Work.frontier = n + tm.directUnrollingGateBound
        (TM.directSerializerHorizonPolynomial q).eval n ∧
      final Work.configBase = n ∧
      final Work.available = n + configWidth tm.toNTM T := by
  dsimp only
  rw [initialization_effect_preambleValues]
  have hclean : StepClean
      (Function.update
        (Function.update
          (preambleValues tm q
            (BinaryRoutine.inputLengthValues Work.inputLength n))
          Work.available
          (n + Fintype.card tm.Q +
            ((TM.directSerializerHorizonPolynomial q).eval n + 1) *
              (k + 2) + 4 +
            4 * ((TM.directSerializerHorizonPolynomial q).eval n + 1) +
            (4 + 4 *
              ((TM.directSerializerHorizonPolynomial q).eval n + 1)) *
                (k + 1)))
        Work.limit₀ 0) := by
    constructor
    · constructor
      · constructor
        · constructor <;>
            simp [preambleValues, BinaryRoutine.inputLengthValues,
              Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
              Work.available, Work.configBase, Work.limit₀, Work.position,
              Work.loop₀, Work.reference₀, Work.reference₁,
              Work.emitCounter, Work.copyCounter, Work.multiplyCounter,
              Work.addCounter, Work.temporary₀, Work.temporary₁,
              Work.temporary₂]
        all_goals
          simp [preambleValues, BinaryRoutine.inputLengthValues,
            Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
            Work.available, Work.configBase, Work.limit₀, Work.position,
            Work.loop₃, Work.temporary₃, Work.polynomialScratch,
            Work.tapeIndex, Work.symbolIndex]
      all_goals
        simp [preambleValues, BinaryRoutine.inputLengthValues,
          Work.inputLength, Work.horizon, Work.frontier, Work.gateCount,
          Work.available, Work.configBase, Work.limit₀,
          Work.limit₂, Work.loop₁, Work.savedOutput, Work.direction,
          Work.atomKind]
    · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
        Work.horizon, Work.frontier, Work.gateCount, Work.available,
        Work.configBase, Work.limit₀, Work.position]
    · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
        Work.horizon, Work.frontier, Work.gateCount, Work.available,
        Work.configBase, Work.limit₀, Work.limit₁]
  refine ⟨hclean, ?_, ?_, ?_, ?_, ?_⟩
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀]
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀, Work.loop₂]
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀]
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀]
  · simp [preambleValues, BinaryRoutine.inputLengthValues, Work.inputLength,
      Work.horizon, Work.frontier, Work.gateCount, Work.available,
      Work.configBase, Work.limit₀, configWidth]
    have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
    rw [hcard]
    ring

private theorem stepScheduleOutputBase_eq_nextInternal (tm : TM k)
    (T n count available configBase : ℕ)
    (havailable : available = n + configWidth tm.toNTM T +
      count * directStepSize tm.toNTM T) :
    stepScheduleOutputBase (transitionCases tm.toNTM).length
        (Fintype.card tm.Q) k T available (stepAtomKindAt tm.toNTM T)
        (stepAtomEffectSelectedAt tm.toNTM T) (effectCaseChoiceAt tm.toNTM) =
      n + (count + 1) * directStepSize tm.toNTM T := by
  have hcard : Fintype.card tm.toNTM.Q = Fintype.card tm.Q := rfl
  rw [← hcard]
  rw [← stepOutputBase_eq_stepScheduleOutputBase tm.toNTM T configBase 0
    available]
  have hend := stepOutputEnd_eq tm.toNTM T configBase 0 available
  rw [stepFragmentSize_eq_directStepSize] at hend
  have hrhs : available + directStepSize tm.toNTM T =
      (n + (count + 1) * directStepSize tm.toNTM T) +
        configWidth tm.toNTM T := by
    rw [havailable]
    ring
  rw [hrhs] at hend
  exact Nat.add_right_cancel hend

private theorem stepLoopValues_numeric_invariant (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n count : ℕ)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
      values count
    StepClean current ∧ current Work.horizon = values Work.horizon ∧
      current Work.loop₂ = count ∧
      current Work.configBase =
        n + count * directStepSize tm.toNTM (values Work.horizon) ∧
      current Work.available =
        n + configWidth tm.toNTM (values Work.horizon) +
          count * directStepSize tm.toNTM (values Work.horizon) := by
  have hbasic := stepLoopValues_invariant tm values hclean hhorizon count
  have hnumeric :
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      current Work.configBase =
          n + count * directStepSize tm.toNTM (values Work.horizon) ∧
        current Work.available =
          n + configWidth tm.toNTM (values Work.horizon) +
            count * directStepSize tm.toNTM (values Work.horizon) := by
    induction count with
    | zero =>
        simp [BinaryRoutine.binaryForValues, hconfigBase, havailable]
    | succ count ih =>
        let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
          values count
        have hcountInvariant :=
          stepLoopValues_invariant tm values hclean hhorizon count
        have hcurrentClean : StepClean current := hcountInvariant.1
        have hcurrentHorizon : current Work.horizon = values Work.horizon :=
          hcountInvariant.2.1
        have hhorizonCurrent : 0 < current Work.horizon := by
          simpa [hcurrentHorizon] using hhorizon
        have ihNumeric := ih hcountInvariant
        have hcurrentBase : current Work.configBase =
            n + count * directStepSize tm.toNTM (values Work.horizon) :=
          ihNumeric.1
        have hcurrentAvailable : current Work.available =
            n + configWidth tm.toNTM (values Work.horizon) +
              count * directStepSize tm.toNTM (values Work.horizon) :=
          ihNumeric.2
        have hsize :
            stepScheduleSize (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (current Work.horizon)
                (stepAtomKindAt tm.toNTM (current Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
                (effectCaseChoiceAt tm.toNTM) =
              directStepSize tm.toNTM (values Work.horizon) := by
          rw [hcurrentHorizon]
          exact stepScheduleSize_eq_directStepSizeInternal tm.toNTM
            (values Work.horizon) (current Work.configBase)
        have hbase :
            stepScheduleOutputBase (transitionCases tm.toNTM).length
                (Fintype.card tm.Q) k (current Work.horizon)
                (current Work.available)
                (stepAtomKindAt tm.toNTM (current Work.horizon))
                (stepAtomEffectSelectedAt tm.toNTM (current Work.horizon))
                (effectCaseChoiceAt tm.toNTM) =
              n + (count + 1) *
                directStepSize tm.toNTM (values Work.horizon) := by
          rw [hcurrentHorizon]
          exact stepScheduleOutputBase_eq_nextInternal tm
            (values Work.horizon) n count (current Work.available)
            (current Work.configBase) hcurrentAvailable
        change
          BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current
                Work.configBase =
              n + (count + 1) *
                directStepSize tm.toNTM (values Work.horizon) ∧
            BinaryRoutine.binaryForStep (emitStep tm) Work.loop₂ current
                Work.available =
              n + configWidth tm.toNTM (values Work.horizon) +
                (count + 1) * directStepSize tm.toNTM (values Work.horizon)
        constructor
        · change (emitStep tm).effect current Work.configBase = _
          rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
          simpa [Work.available, Work.configBase, Work.gateBound,
            Work.gateCount] using hbase
        · change (emitStep tm).effect current Work.available = _
          rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
          rw [hsize, hcurrentAvailable]
          simp [Work.available, Work.configBase,
            Work.gateBound, Work.gateCount]
          ring
  refine ⟨hbasic.1, hbasic.2.1, ?_, hnumeric⟩
  simpa [hloop] using hbasic.2.2

private theorem stepLoopEmitted_eq_prefix (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n count : ℕ)
    (hcount : count ≤ values Work.horizon)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    BinaryRoutine.binaryForEmitted (emitStep tm) Work.loop₂ values count =
      (((List.finRange (values Work.horizon)).take count).flatMap
        (tm.directStepFragment (values Work.horizon) n)).flatMap
          CircuitCode.RawGate.encode := by
  induction count with
  | zero => simp [BinaryRoutine.binaryForEmitted]
  | succ count ih =>
      have hindex : count < values Work.horizon := by omega
      have hprefix := ih (by omega)
      let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
        values count
      have hinvariant := stepLoopValues_numeric_invariant tm values hclean
        hhorizon n count hloop hconfigBase havailable
      have hcurrentClean : StepClean current := hinvariant.1
      have hcurrentHorizon : current Work.horizon = values Work.horizon :=
        hinvariant.2.1
      have hhorizonCurrent : 0 < current Work.horizon := by
        simpa [hcurrentHorizon] using hhorizon
      have hcurrentBase : current Work.configBase =
          n + count * directStepSize tm.toNTM (values Work.horizon) :=
        hinvariant.2.2.2.1
      have hcurrentAvailable : current Work.available =
          n + configWidth tm.toNTM (values Work.horizon) +
            count * directStepSize tm.toNTM (values Work.horizon) :=
        hinvariant.2.2.2.2
      have hlistIndex : count < (List.finRange (values Work.horizon)).length := by
        simpa using hindex
      have hget : (List.finRange (values Work.horizon))[count]'hlistIndex =
          (⟨count, hindex⟩ : Fin (values Work.horizon)) := by
        apply Fin.ext
        simp
      have htake :
          (List.finRange (values Work.horizon)).take (count + 1) =
            (List.finRange (values Work.horizon)).take count ++
              [(⟨count, hindex⟩ : Fin (values Work.horizon))] := by
        rw [List.take_succ_eq_append_getElem hlistIndex, hget]
      rw [BinaryRoutine.binaryForEmitted, hprefix,
        emitStep_emitted tm current hcurrentClean hhorizonCurrent, htake,
        List.flatMap_append]
      simp [TM.directStepFragment, hcurrentHorizon, hcurrentBase,
        hcurrentAvailable]

theorem emitTransitionSteps_sound_internal (tm : TM k) :
    (emitTransitionSteps tm).Sound :=
  ((emitStep_sound tm).binaryFor Work.loop₂ Work.horizon).seq
    (BinaryRoutine.clear_sound Work.loop₂)

theorem emitTransitionSteps_requires_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hloop : values Work.loop₂ = 0)
    (hhorizon : 0 < values Work.horizon) :
    (emitTransitionSteps tm).requires values := by
  unfold emitTransitionSteps
  constructor
  · refine ⟨by decide, by omega, ?_⟩
    intro count hcount
    let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂
      values count
    have hinvariant := stepLoopValues_invariant tm values hclean hhorizon count
    have hcurrentClean : StepClean current := hinvariant.1
    have hcurrentHorizon : current Work.horizon = values Work.horizon :=
      hinvariant.2.1
    have hhorizonCurrent : 0 < current Work.horizon := by
      simpa [hcurrentHorizon] using hhorizon
    refine ⟨emitStep_requires tm current hcurrentClean hhorizonCurrent, ?_, ?_⟩
    · change (emitStep tm).effect current Work.loop₂ = current Work.loop₂
      rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
      simp [Work.available, Work.configBase, Work.gateBound, Work.gateCount,
        Work.loop₂]
    · change (emitStep tm).effect current Work.horizon = current Work.horizon
      rw [emitStep_effect tm current hcurrentClean hhorizonCurrent]
      simp [Work.available, Work.configBase, Work.gateBound, Work.gateCount,
        Work.horizon]
  · trivial

theorem tableauTransitionSteps_sound_internal (tm : TM k) :
    (tableauTransitionSteps tm).Sound :=
  (emitTransitionSteps_sound_internal tm).restrict (TransitionEntry tm)
    fun values hentry =>
      emitTransitionSteps_requires_internal tm values hentry.clean
        hentry.loop₂ hentry.horizon

theorem tableauFinalization_sound_internal (tm : TM k) :
    (tableauFinalization tm).Sound :=
  (finalization_sound tm).restrict FinalizationEntry fun values hentry =>
    finalization_requires tm values hentry.emitCounter hentry.copyCounter
      hentry.addCounter hentry.multiplyCounter hentry.available

theorem emitTransitionSteps_effect_internal (tm : TM k)
    (values : BinaryValues WorkCount) :
    (emitTransitionSteps tm).effect values =
      Function.update
        (BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ values
          (values Work.horizon - values Work.loop₂)) Work.loop₂ 0 := by
  rfl

theorem emitTransitionSteps_emitted_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hloop : values Work.loop₂ = 0) :
    (emitTransitionSteps tm).emitted values =
      BinaryRoutine.binaryForEmitted (emitStep tm) Work.loop₂ values
        (values Work.horizon) := by
  simp [emitTransitionSteps, BinaryRoutine.seq, BinaryRoutine.binaryFor,
    BinaryRoutine.clear, BinaryRoutine.binaryForCount, hloop]

theorem emitTransitionSteps_endpoint_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n : ℕ)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    let final := (emitTransitionSteps tm).effect values
    StepClean final ∧ final Work.horizon = values Work.horizon ∧
      final Work.loop₂ = 0 ∧
      final Work.frontier = values Work.frontier ∧
      final Work.configBase = n + values Work.horizon *
        directStepSize tm.toNTM (values Work.horizon) ∧
      final Work.available =
        n + configWidth tm.toNTM (values Work.horizon) +
          values Work.horizon *
            directStepSize tm.toNTM (values Work.horizon) := by
  let current := BinaryRoutine.binaryForValues (emitStep tm) Work.loop₂ values
    (values Work.horizon)
  have hinvariant := stepLoopValues_numeric_invariant tm values hclean hhorizon n
    (values Work.horizon) hloop hconfigBase havailable
  have hfinalClean : StepClean (Function.update current Work.loop₂ 0) :=
    hinvariant.1.updateOuter_forEffect_internal _ Work.loop₂ _
      (Or.inr (Or.inr (Or.inr rfl)))
  rw [emitTransitionSteps_effect_internal, hloop, Nat.sub_zero]
  refine ⟨hfinalClean, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Work.loop₂, Work.horizon] using hinvariant.2.1
  · simp
  · rw [Function.update_of_ne (by decide)]
    exact stepLoopValues_frontier tm values hclean hhorizon
      (values Work.horizon)
  · simpa [Work.loop₂, Work.configBase] using hinvariant.2.2.2.1
  · simpa [Work.loop₂, Work.available] using hinvariant.2.2.2.2

theorem emitTransitionSteps_emitted_exact_internal (tm : TM k)
    (values : BinaryValues WorkCount) (hclean : StepClean values)
    (hhorizon : 0 < values Work.horizon) (n : ℕ)
    (hloop : values Work.loop₂ = 0)
    (hconfigBase : values Work.configBase = n)
    (havailable : values Work.available =
      n + configWidth tm.toNTM (values Work.horizon)) :
    (emitTransitionSteps tm).emitted values =
      ((List.finRange (values Work.horizon)).flatMap
        (tm.directStepFragment (values Work.horizon) n)).flatMap
          CircuitCode.RawGate.encode := by
  rw [emitTransitionSteps_emitted_internal tm values hloop,
    stepLoopEmitted_eq_prefix tm values hclean hhorizon n
      (values Work.horizon) le_rfl hloop hconfigBase havailable]
  rw [List.take_of_length_le (by simp)]

theorem positiveTableauBody_sound_internal (tm : TM k) :
    (positiveTableauBody tm).Sound :=
  (initialization_sound tm).seq
    ((tableauTransitionSteps_sound_internal tm).seq
      (tableauFinalization_sound_internal tm))

set_option maxHeartbeats 2000000 in
theorem positiveTableauBody_requires_internal (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) (hn : 0 < n) :
    (positiveTableauBody tm).requires
      (preambleValues tm q
        (BinaryRoutine.inputLengthValues Work.inputLength n)) := by
  let entry := preambleValues tm q
    (BinaryRoutine.inputLengthValues Work.inputLength n)
  let afterInit := (initialization tm).effect entry
  let afterSteps := (emitTransitionSteps tm).effect afterInit
  let T := (TM.directSerializerHorizonPolynomial q).eval n
  let f := (TM.directSerializerHorizonPolynomial q).eval
  have hinit : StepClean afterInit ∧ afterInit Work.horizon = T ∧
      afterInit Work.loop₂ = 0 ∧
      afterInit Work.frontier = n + tm.directUnrollingGateBound f n ∧
      afterInit Work.configBase = n ∧
      afterInit Work.available = n + configWidth tm.toNTM T := by
    simpa only [afterInit, entry, T, f] using initializationEndpoint tm q n
  have hhorizon : 0 < afterInit Work.horizon := by
    have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
    rw [hinit.2.1]
    omega
  have hinitAvailable : afterInit Work.available =
      n + configWidth tm.toNTM (afterInit Work.horizon) := by
    rw [hinit.2.1]
    exact hinit.2.2.2.2.2
  have hstepsRaw := emitTransitionSteps_endpoint_internal tm afterInit hinit.1
    hhorizon n hinit.2.2.1 hinit.2.2.2.2.1 hinitAvailable
  have hsteps : StepClean afterSteps ∧
      afterSteps Work.horizon = afterInit Work.horizon ∧
      afterSteps Work.loop₂ = 0 ∧
      afterSteps Work.frontier = afterInit Work.frontier ∧
      afterSteps Work.configBase = n + afterInit Work.horizon *
        directStepSize tm.toNTM (afterInit Work.horizon) ∧
      afterSteps Work.available =
        n + configWidth tm.toNTM (afterInit Work.horizon) +
          afterInit Work.horizon *
            directStepSize tm.toNTM (afterInit Work.horizon) := by
    simpa only [afterSteps] using hstepsRaw
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hrawBound := tm.directUnrollingRawCircuit_length_le_gateBound f n
  rw [directUnrollingRawCircuit_length_eq_original] at hrawBound
  have hfinalBound : afterSteps Work.available + 1 ≤
      afterSteps Work.frontier := by
    rw [hsteps.2.2.2.2.2, hsteps.2.2.2.1, hinit.2.2.2.1,
      hinit.2.1]
    unfold directOriginalRawGateCount at hrawBound
    dsimp only [f, T] at hrawBound ⊢
    omega
  have htransition : TransitionEntry tm afterInit :=
    ⟨hinit.1, hinit.2.2.1, hhorizon⟩
  have hfinal : FinalizationEntry afterSteps :=
    ⟨hsteps.1.movedHeadClean.caseClean.toReadFormulaClean.emitCounter,
      hsteps.1.movedHeadClean.caseClean.toReadFormulaClean.copyCounter,
      hsteps.1.movedHeadClean.caseClean.toReadFormulaClean.addCounter,
      hsteps.1.movedHeadClean.caseClean.toReadFormulaClean.multiplyCounter,
      hfinalBound⟩
  have hinitRequires : (initialization tm).requires entry :=
    initialization_requires_preambleValues tm q n hn
  unfold positiveTableauBody tableauTransitionSteps tableauFinalization
    BinaryRoutine.restrict
  exact ⟨hinitRequires, htransition, hfinal⟩

set_option maxHeartbeats 2000000 in
theorem positiveTableauBody_emitted_internal (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) [NeZero n] (hn : 0 < n) :
    (positiveTableauBody tm).emitted
        (preambleValues tm q
          (BinaryRoutine.inputLengthValues Work.inputLength n)) =
      (tm.paddedDirectUnrollingRawCircuit
        (TM.directSerializerHorizonPolynomial q).eval n).flatMap
          CircuitCode.RawGate.encode := by
  let entry := preambleValues tm q
    (BinaryRoutine.inputLengthValues Work.inputLength n)
  let afterInit := (initialization tm).effect entry
  let afterSteps := (emitTransitionSteps tm).effect afterInit
  let T := (TM.directSerializerHorizonPolynomial q).eval n
  let f := (TM.directSerializerHorizonPolynomial q).eval
  let original := directOriginalRawGateCount tm T
  let bound := tm.directUnrollingGateBound f n
  have hinit : StepClean afterInit ∧ afterInit Work.horizon = T ∧
      afterInit Work.loop₂ = 0 ∧
      afterInit Work.frontier = n + bound ∧
      afterInit Work.configBase = n ∧
      afterInit Work.available = n + configWidth tm.toNTM T := by
    simpa only [afterInit, entry, T, f, bound] using
      initializationEndpoint tm q n
  have hhorizon : 0 < afterInit Work.horizon := by
    have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
    rw [hinit.2.1]
    omega
  have hinitAvailable : afterInit Work.available =
      n + configWidth tm.toNTM (afterInit Work.horizon) := by
    rw [hinit.2.1]
    exact hinit.2.2.2.2.2
  have hstepsRaw := emitTransitionSteps_endpoint_internal tm afterInit hinit.1
    hhorizon n hinit.2.2.1 hinit.2.2.2.2.1 hinitAvailable
  have hsteps : StepClean afterSteps ∧
      afterSteps Work.horizon = afterInit Work.horizon ∧
      afterSteps Work.loop₂ = 0 ∧
      afterSteps Work.frontier = afterInit Work.frontier ∧
      afterSteps Work.configBase = n + afterInit Work.horizon *
        directStepSize tm.toNTM (afterInit Work.horizon) ∧
      afterSteps Work.available =
        n + configWidth tm.toNTM (afterInit Work.horizon) +
          afterInit Work.horizon *
            directStepSize tm.toNTM (afterInit Work.horizon) := by
    simpa only [afterSteps] using hstepsRaw
  have hinitEmitted := initialization_emitted_preambleValues tm q n
  have hstepsEmitted := emitTransitionSteps_emitted_exact_internal tm afterInit
    hinit.1 hhorizon n hinit.2.2.1 hinit.2.2.2.2.1
      hinitAvailable
  rw [hinit.2.1] at hstepsEmitted
  have havailable : afterSteps Work.available = n + original - 1 := by
    rw [hsteps.2.2.2.2.2]
    rw [hinit.2.1]
    dsimp only [original, T]
    unfold directOriginalRawGateCount
    omega
  have hfrontier : afterSteps Work.frontier = n + bound := by
    rw [hsteps.2.2.2.1, hinit.2.2.2.1]
  have hhorizonFinal : afterSteps Work.horizon = T := by
    rw [hsteps.2.1, hinit.2.1]
  have hconfigFinal : afterSteps Work.configBase =
      n + T * directStepSize tm.toNTM T := by
    rw [hsteps.2.2.2.2.1, hinit.2.1]
  have hfinalEmitted := finalization_emitted_eq_numericSchedule tm afterSteps
    n original bound T (n + T * directStepSize tm.toNTM T) hn havailable
      hfrontier hhorizonFinal hconfigFinal
  have hinputBound := TM.directSerializerHorizonPolynomial_input_le q n
  have hschedule := paddedDirectUnrollingRawCircuit_eq_numericSchedule tm f n
    hinputBound
  simp only [positiveTableauBody, tableauTransitionSteps,
    tableauFinalization, BinaryRoutine.restrict, BinaryRoutine.seq]
  rw [hinitEmitted, hstepsEmitted, hfinalEmitted, hschedule]
  dsimp only [entry, T, f, original, bound] at *
  simp only [List.flatMap_append, List.flatMap_singleton]
  simp [directFinalizationSuffix, List.append_assoc]

theorem paddedDirectUnrollingProgram_sound_internal (tm : TM k)
    (q : Polynomial ℕ) : (paddedDirectUnrollingProgram tm q).Sound :=
  program_sound tm q (positiveTableauBody_sound_internal tm)

theorem paddedDirectUnrollingProgram_requires_inputLengthValues_internal
    (tm : TM k) (q : Polynomial ℕ) (n : ℕ) :
    (paddedDirectUnrollingProgram tm q).requires
      (BinaryRoutine.inputLengthValues Work.inputLength n) := by
  apply program_requires_inputLengthValues tm q (positiveTableauBody tm)
  intro length hlength
  exact positiveTableauBody_requires_internal tm q length hlength

theorem paddedDirectUnrollingProgram_emitted_internal (tm : TM k)
    (q : Polynomial ℕ) (n : ℕ) :
    (paddedDirectUnrollingProgram tm q).emitted
        (BinaryRoutine.inputLengthValues Work.inputLength n) =
      tm.paddedDirectUnrollingCode
        (TM.directSerializerHorizonPolynomial q).eval n := by
  cases n with
  | zero =>
      unfold paddedDirectUnrollingProgram
      rw [program_emitted]
      simp [TM.paddedDirectUnrollingCode,
        BinaryRoutine.inputLengthValues, Work.inputLength]
  | succ n =>
      unfold paddedDirectUnrollingProgram
      rw [program_emitted]
      simp only [BinaryRoutine.inputLengthValues, Work.inputLength,
        Function.update_self, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte]
      have hbody := positiveTableauBody_emitted_internal tm q (n + 1)
        (by omega)
      simp only [BinaryRoutine.inputLengthValues, Work.inputLength] at hbody
      rw [hbody]
      simp [TM.paddedDirectUnrollingCode, CircuitCode.RawCircuit.encode,
        TM.directSerializerGateCountPolynomial_eval,
        tm.paddedDirectUnrollingRawCircuit_length]

theorem paddedDirectUnrollingGenerator_computesInSpace_internal
    (tm : TM k) (q : Polynomial ℕ) :
    (BinaryRoutine.afterInputLength Work.inputLength
      (paddedDirectUnrollingProgram tm q)).ComputesInSpace
        (fun input => tm.paddedDirectUnrollingCode
          (TM.directSerializerHorizonPolynomial q).eval input.length)
        (BinaryRoutine.afterInputLengthSpace Work.inputLength
          (paddedDirectUnrollingProgram tm q)) := by
  have hcomputes := BinaryRoutine.Sound.afterInputLength_computesInSpace
    (paddedDirectUnrollingProgram_sound_internal tm q) Work.inputLength
    (paddedDirectUnrollingProgram_requires_inputLengthValues_internal tm q)
  convert hcomputes using 1
  funext input
  simpa only [BinaryRoutine.afterInputLengthFunction] using
    (paddedDirectUnrollingProgram_emitted_internal tm q input.length).symm

end DirectGenerator

end Serializer

end CircuitUnrolling

end Complexity
