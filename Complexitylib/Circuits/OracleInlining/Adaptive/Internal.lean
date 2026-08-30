/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Circuits.OracleInlining.Adaptive.Defs
public import Complexitylib.Circuits.OracleInlining
public import Complexitylib.Circuits.Composition
public import Complexitylib.Circuits.InputProjection

/-!
# Fixed-round adaptive oracle circuit programs -- proof internals
-/


public section

namespace Complexity

namespace AdaptiveOracleProgram

private theorem finCastSelf {width : ℕ} (h : width = width)
    (index : Fin width) : Fin.cast h index = index := by
  cases h
  rfl

/-- Internal correctness of every compiled history prefix. -/
theorem inlineHistory_eval_internal
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program)
    {oracle : BooleanOracle} (himplementation : implementation.Implements oracle)
    (input : BitString inputWidth) (completed : ℕ) (hcompleted : completed ≤ rounds) :
    (program.inlineHistory implementation completed hcompleted).2.eval input =
      program.history oracle input completed hcompleted := by
  induction completed with
  | zero =>
      simp [inlineHistory, history, Function.comp_def]
  | succ completed ih =>
      simp only [inlineHistory, Circuit.eval_appendOracleAnswer]
      rw [ih]
      simp only [history]
      funext index
      refine Fin.addCases ?_ ?_ index
      · intro priorIndex
        rw [finCastSelf, Fin.append_left, Fin.append_left]
      · intro answerIndex
        rw [finCastSelf, Fin.append_right]
        have hanswer : answerIndex = 0 := Subsingleton.elim _ _
        subst answerIndex
        calc
          _ = oracle ((program.query ⟨completed, by omega⟩).eval
                (program.history oracle input completed (by omega))).toList := by
            simpa only using himplementation ⟨completed, by omega⟩
              ((program.query ⟨completed, by omega⟩).eval
                (program.history oracle input completed (by omega)))
          _ = _ := by
            symm
            exact Fin.append_right _ _ 0

/-- Internal exact size of every compiled history prefix. -/
theorem inlineHistory_size_internal
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program)
    (completed : ℕ) (hcompleted : completed ≤ rounds) :
    (program.inlineHistory implementation completed hcompleted).2.size =
      program.inlineHistorySize implementation completed hcompleted := by
  induction completed with
  | zero =>
      simp [inlineHistory, inlineHistorySize]
  | succ completed ih =>
      simp only [inlineHistory, Circuit.size_appendOracleAnswer,
        inlineHistorySize]
      rw [ih]
      rfl

/-- Internal semantic correctness of the fully inlined circuit. -/
theorem inline_eval_internal
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program)
    {oracle : BooleanOracle} (himplementation : implementation.Implements oracle)
    (input : BitString inputWidth) :
    (program.inline implementation).2.eval input = program.eval oracle input := by
  simp only [inline, Circuit.eval_compose, eval]
  rw [program.inlineHistory_eval_internal implementation himplementation]

/-- Internal exact size of the fully inlined circuit. -/
theorem inline_size_internal
    {inputWidth outputWidth rounds : ℕ}
    [NeZero inputWidth] [NeZero outputWidth]
    (program : AdaptiveOracleProgram inputWidth outputWidth rounds)
    (implementation : OracleCircuitImplementation program) :
    (program.inline implementation).2.size =
      program.inlineHistorySize implementation rounds le_rfl +
        program.final.size := by
  simp only [inline, Circuit.size_compose]
  rw [program.inlineHistory_size_internal implementation]

end AdaptiveOracleProgram

end Complexity
