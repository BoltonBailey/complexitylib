/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Circuits.BarringtonCodeGenerator.Defs
import Complexitylib.Circuits.BarringtonCompiler
import Complexitylib.Circuits.BranchingProgramEncoding
import Complexitylib.Circuits.FormulaEncoding

/-!
# Pure Barrington code-generator internals
-/

namespace Complexity

private theorem BP.forall_var_inverse_internal {w bound : ℕ}
    (program : BP w)
    (hvars : ∀ instruction ∈ program, instruction.var ≤ bound) :
    ∀ instruction ∈ BP.inverse program, instruction.var ≤ bound := by
  intro instruction hinstruction
  simp only [BP.inverse, List.mem_reverse, List.mem_map] at hinstruction
  obtain ⟨source, hsource, rfl⟩ := hinstruction
  exact hvars source hsource

private theorem BP.forall_var_postMul_internal {w bound : ℕ}
    (program : BP w) (permutation : Equiv.Perm (Fin w))
    (hvars : ∀ instruction ∈ program, instruction.var ≤ bound) :
    ∀ instruction ∈ BP.postMul program permutation,
      instruction.var ≤ bound := by
  induction program using List.reverseRecOn with
  | nil =>
      intro instruction hinstruction
      simp [BP.postMul, BPInstr.const] at hinstruction
      subst instruction
      exact Nat.zero_le bound
  | append_singleton program last ih =>
      intro instruction hinstruction
      have hnonempty : program ++ [last] ≠ [] := by simp
      simp only [BP.postMul, if_neg hnonempty,
        List.modifyLast_concat, List.mem_append,
        List.mem_singleton] at hinstruction
      rcases hinstruction with hprefix | rfl
      · exact hvars instruction (List.mem_append_left _ hprefix)
      · exact hvars last (by simp)

private theorem BP.forall_var_commutatorProgram_internal
    {bound : ℕ} (left right : BP 5)
    (hleft : ∀ instruction ∈ left, instruction.var ≤ bound)
    (hright : ∀ instruction ∈ right, instruction.var ≤ bound) :
    ∀ instruction ∈ BP.commutatorProgram left right,
      instruction.var ≤ bound := by
  have hleftInverse := BP.forall_var_inverse_internal left hleft
  have hrightInverse := BP.forall_var_inverse_internal right hright
  intro instruction hinstruction
  simp only [BP.commutatorProgram, List.mem_append] at hinstruction
  rcases hinstruction with hinstruction | hinstruction
  · rcases hinstruction with hinstruction | hinstruction
    · rcases hinstruction with hinstruction | hinstruction
      · exact hleft instruction hinstruction
      · exact hright instruction hinstruction
    · exact hleftInverse instruction hinstruction
  · exact hrightInverse instruction hinstruction

/-- Internal variable-locality theorem for the executable compiler. -/
theorem barringtonCompile_var_bound_internal
    (formula : BoolFormula) (target : Equiv.Perm (Fin 5)) (bound : ℕ)
    (hvars : ∀ index ∈ formula.vars, index ≤ bound) :
    ∀ instruction ∈ barringtonCompile formula target,
      instruction.var ≤ bound := by
  induction formula generalizing target with
  | var index =>
      intro instruction hinstruction
      simp only [barringtonCompile, List.mem_singleton] at hinstruction
      subst instruction
      exact hvars index (by simp [BoolFormula.vars])
  | tru =>
      intro instruction hinstruction
      simp [barringtonCompile, BPInstr.const] at hinstruction
      subst instruction
      exact Nat.zero_le bound
  | fls => simp [barringtonCompile]
  | neg formula ih =>
      exact BP.forall_var_postMul_internal _ _
        (ih target⁻¹ (by simpa only [BoolFormula.vars] using hvars))
  | conj left right ihLeft ihRight =>
      apply BP.forall_var_commutatorProgram_internal
      · apply ihLeft
        intro index hindex
        exact hvars index (Finset.mem_union_left _ hindex)
      · apply ihRight
        intro index hindex
        exact hvars index (Finset.mem_union_right _ hindex)
  | disj left right ihLeft ihRight =>
      simp only [barringtonCompile]
      apply BP.forall_var_postMul_internal
      apply BP.forall_var_commutatorProgram_internal
      · apply BP.forall_var_postMul_internal
        apply ihLeft
        intro index hindex
        exact hvars index (Finset.mem_union_left _ hindex)
      · apply BP.forall_var_postMul_internal
        apply ihRight
        intro index hindex
        exact hvars index (Finset.mem_union_right _ hindex)

/-- Internal bound placing every referenced variable below the formula-code
length. -/
theorem formula_variable_le_code_length_internal
    (formula : BoolFormula) (index : ℕ) (hindex : index ∈ formula.vars) :
    index ≤ (FormulaCode.encode formula).length := by
  induction formula with
  | var sourceIndex =>
      simp only [BoolFormula.vars, Finset.mem_singleton] at hindex
      subst index
      simp [FormulaCode.length_encode, FormulaCode.tokens,
        FormulaCode.Token.codeLength, BoolFormula.size]
      omega
  | tru => simp [BoolFormula.vars] at hindex
  | fls => simp [BoolFormula.vars] at hindex
  | neg formula ih =>
      have hsub : index ≤ (FormulaCode.encode formula).length :=
        ih (by simpa only [BoolFormula.vars] using hindex)
      apply hsub.trans
      simp [FormulaCode.length_encode, FormulaCode.tokens,
        FormulaCode.Token.codeLength, BoolFormula.size]
      omega
  | conj left right ihLeft ihRight =>
      simp only [BoolFormula.vars, Finset.mem_union] at hindex
      rcases hindex with hleft | hright
      · apply (ihLeft hleft).trans
        simp [FormulaCode.length_encode, FormulaCode.tokens,
          FormulaCode.Token.codeLength, BoolFormula.size]
        omega
      · apply (ihRight hright).trans
        simp [FormulaCode.length_encode, FormulaCode.tokens,
          FormulaCode.Token.codeLength, BoolFormula.size]
        omega
  | disj left right ihLeft ihRight =>
      simp only [BoolFormula.vars, Finset.mem_union] at hindex
      rcases hindex with hleft | hright
      · apply (ihLeft hleft).trans
        simp [FormulaCode.length_encode, FormulaCode.tokens,
          FormulaCode.Token.codeLength, BoolFormula.size]
        omega
      · apply (ihRight hright).trans
        simp [FormulaCode.length_encode, FormulaCode.tokens,
          FormulaCode.Token.codeLength, BoolFormula.size]
        omega

/-- Internal exact action of the code generator on a canonical formula code. -/
theorem barringtonCompileCode_encode_internal (formula : BoolFormula) :
    barringtonCompileCode (FormulaCode.encode formula) =
      BPCode.Program.encode
        (barringtonCompile formula barringtonTargetBase) := by
  simp [barringtonCompileCode]

/-- Internal decoding theorem for generated program code. -/
theorem decode?_barringtonCompileCode_encode_internal
    (formula : BoolFormula) :
    BPCode.Program.decode?
        (barringtonCompileCode (FormulaCode.encode formula)) =
      some (barringtonCompile formula barringtonTargetBase) := by
  rw [barringtonCompileCode_encode_internal]
  exact BPCode.Program.decode?_encode _

/-- Internal exact output-code length on canonical formula input. -/
theorem length_barringtonCompileCode_encode_internal
    (formula : BoolFormula) :
    (barringtonCompileCode (FormulaCode.encode formula)).length =
      (barringtonCompile formula barringtonTargetBase).length + 1 +
        (((barringtonCompile formula barringtonTargetBase).map
          fun instruction => instruction.var + 15).sum) := by
  rw [barringtonCompileCode_encode_internal]
  exact BPCode.Program.length_encode _

/-- Internal serialized-output bound in terms of formula-code length and depth.
The extra factor comes from the terminated-unary variable field in each
instruction. -/
theorem length_barringtonCompileCode_encode_le_internal
    (formula : BoolFormula) :
    (barringtonCompileCode (FormulaCode.encode formula)).length ≤
      4 ^ formula.depth + 1 +
        4 ^ formula.depth * ((FormulaCode.encode formula).length + 15) := by
  let program := barringtonCompile formula barringtonTargetBase
  have hvariables :
      ∀ instruction ∈ program,
        instruction.var ≤ (FormulaCode.encode formula).length := by
    apply barringtonCompile_var_bound_internal
    intro index hindex
    exact formula_variable_le_code_length_internal formula index hindex
  have hprogram :=
    BPCode.Program.length_encode_le program
      (FormulaCode.encode formula).length hvariables
  have hlength : program.length ≤ 4 ^ formula.depth :=
    barringtonCompile_length_le formula barringtonTargetBase
  have hscaled := Nat.mul_le_mul_right
    ((FormulaCode.encode formula).length + 15) hlength
  rw [barringtonCompileCode_encode_internal]
  exact hprogram.trans (by omega)

/-- Internal combined semantic and program-length specification of generated
code on canonical formula input. -/
theorem barringtonCompileCode_spec_internal (formula : BoolFormula) :
    barringtonTargetBase ≠ 1 ∧
      (∀ assignment,
        BP.eval assignment
          (barringtonCompile formula barringtonTargetBase) =
            if BoolFormula.eval assignment formula then
              barringtonTargetBase else 1) ∧
      (barringtonCompile formula barringtonTargetBase).length ≤
        4 ^ formula.depth ∧
      BPCode.Program.decode?
          (barringtonCompileCode (FormulaCode.encode formula)) =
        some (barringtonCompile formula barringtonTargetBase) := by
  obtain ⟨htarget, hsemantics, hlength⟩ :=
    barringtonCompile_representation formula
  exact ⟨htarget, hsemantics, hlength,
    decode?_barringtonCompileCode_encode_internal formula⟩

end Complexity
