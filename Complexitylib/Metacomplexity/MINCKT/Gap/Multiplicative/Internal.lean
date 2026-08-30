/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Multiplicative.Defs
public import Complexitylib.Metacomplexity.MINCKT.Gap.Internal
import Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal

/-!
# Multiplicative-gap conditional MinKT -- proof internals
-/


public section

namespace Complexity

namespace GapMINCKT

namespace Multiplicative

theorem isNo_iff_no_relaxedWitness_internal
    {conditionalTapes : ℕ} (inst : GapMINCKT.Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ) :
    IsNo inst conditionalMachine parameters factor ↔
      ¬∃ program,
        IsRelaxedWitness inst conditionalMachine parameters factor program := by
  constructor
  · intro hno ⟨program, hlength, hproduce⟩
    have hcomplexity :=
      (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_internal
        hproduce).trans (WithTop.coe_le_coe.mpr hlength)
    exact (not_lt_of_ge hcomplexity) hno
  · intro hnone
    apply lt_of_not_ge
    intro hcomplexity
    obtain ⟨program, hlength, hproduce⟩ :=
      (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
        conditionalMachine inst.output inst.condition
          (inst.laterTime parameters)
          (factor inst.output.length * inst.threshold +
            inst.logSlack parameters)).mp hcomplexity
    exact hnone ⟨program, hlength, hproduce⟩

theorem isNo_implies_additive_internal
    {conditionalTapes : ℕ} {inst : GapMINCKT.Instance}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : GapMINCKT.Parameters} {factor : ℕ → ℕ}
    (hfactor : 1 ≤ factor inst.output.length)
    (hno : IsNo inst conditionalMachine parameters factor) :
    inst.IsNo conditionalMachine parameters := by
  have hthreshold : inst.threshold ≤
      factor inst.output.length * inst.threshold :=
    Nat.le_mul_of_pos_left inst.threshold (by omega)
  exact lt_of_le_of_lt
    (WithTop.coe_le_coe.mpr
      (Nat.add_le_add_right hthreshold (inst.logSlack parameters))) hno

theorem isNo_factor_anti_internal
    {conditionalTapes : ℕ} {inst : GapMINCKT.Instance}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : GapMINCKT.Parameters} {first second : ℕ → ℕ}
    (hfactor : first inst.output.length ≤ second inst.output.length)
    (hno : IsNo inst conditionalMachine parameters second) :
    IsNo inst conditionalMachine parameters first := by
  exact lt_of_le_of_lt
    (WithTop.coe_le_coe.mpr <|
      Nat.add_le_add_right
        (Nat.mul_le_mul_right inst.threshold hfactor)
        (inst.logSlack parameters)) hno

theorem not_isNo_of_isYes_internal
    {ordinaryTapes conditionalTapes : ℕ}
    (inst : GapMINCKT.Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : 1 ≤ factor inst.output.length)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    ¬IsNo inst conditionalMachine parameters factor := by
  intro hno
  exact GapMINCKT.Instance.not_isNo_of_isYes_internal inst ordinaryMachine
    conditionalMachine parameters hwidening hyes
      (isNo_implies_additive_internal hfactor hno)

theorem noLanguage_mem_encode_iff_internal
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (inst : GapMINCKT.Instance) :
    inst.encode ∈ noLanguage conditionalMachine parameters factor ↔
      IsNo inst conditionalMachine parameters factor := by
  simp [noLanguage, GapMINCKT.Instance.decode?_encode_internal]

theorem noLanguage_subset_additive_internal
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hfactor : ∀ length, 1 ≤ factor length) :
    noLanguage conditionalMachine parameters factor ⊆
      GapMINCKT.noLanguage conditionalMachine parameters := by
  intro bits hno
  cases hdecode : GapMINCKT.Instance.decode? bits with
  | none => simp [noLanguage, hdecode] at hno
  | some inst =>
      have hno' : IsNo inst conditionalMachine parameters factor := by
        simpa [noLanguage, hdecode] using hno
      have hadditive := isNo_implies_additive_internal
        (hfactor inst.output.length) hno'
      simpa [GapMINCKT.noLanguage, hdecode] using hadditive

theorem noLanguage_factor_anti_internal
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) {first second : ℕ → ℕ}
    (hfactor : ∀ length, first length ≤ second length) :
    noLanguage conditionalMachine parameters second ⊆
      noLanguage conditionalMachine parameters first := by
  intro bits hno
  cases hdecode : GapMINCKT.Instance.decode? bits with
  | none => simp [noLanguage, hdecode] at hno
  | some inst =>
      have hno' : IsNo inst conditionalMachine parameters second := by
        simpa [noLanguage, hdecode] using hno
      have hfirst := isNo_factor_anti_internal
        (hfactor inst.output.length) hno'
      simpa [noLanguage, hdecode] using hfirst

theorem noLanguage_one_internal
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) :
    noLanguage conditionalMachine parameters (fun _length => 1) =
      GapMINCKT.noLanguage conditionalMachine parameters := by
  ext bits
  cases hdecode : GapMINCKT.Instance.decode? bits with
  | none => simp [noLanguage, GapMINCKT.noLanguage, hdecode]
  | some inst =>
      simp [noLanguage, GapMINCKT.noLanguage, IsNo, GapMINCKT.Instance.IsNo,
        hdecode]

theorem disjoint_yesLanguage_noLanguage_internal
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length) :
    Disjoint (yesLanguage ordinaryMachine conditionalMachine parameters)
      (noLanguage conditionalMachine parameters factor) := by
  exact Set.disjoint_of_subset_right
    (noLanguage_subset_additive_internal conditionalMachine parameters factor
      hfactor)
    (GapMINCKT.disjoint_yesLanguage_noLanguage_internal ordinaryMachine
      conditionalMachine parameters hwidening)

end Multiplicative

end GapMINCKT

end Complexity
