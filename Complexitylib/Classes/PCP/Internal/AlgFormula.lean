/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.SAT.ThreeSAT.Completeness
public import Complexitylib.Classes.PCP.Internal.AlgUniform

/-!
# Every NP language, as a formula

Cook--Levin and Tseitin already reduce any `NP` language to encoded 3SAT. What
the gap reduction needs is slightly more: not a string that *lies in* 3SAT, but
the *formula itself*, so that the constraint graph can be built from it.

The Tseitin reduction is total — malformed inputs go to a fixed unsatisfiable
formula — so the formula is always there to be named: `redCNF` names it, and
`reduction_eq_encode` says the reduction writes exactly its encoding.

## Main definitions

- `Complexity.redCNF` — the 3CNF a string reduces to

## Main results

- `Complexity.exists_reduction_cnf` — every `NP` language is the satisfiability
  of an `FP` family of 3CNFs
-/

@[expose] public section

namespace Complexity

open SAT SAT.ThreeSAT

/-- The exact 3-CNF that the total Tseitin reduction produces. -/
noncomputable def redCNF (z : List Bool) : CNF :=
  match CNF.decode? z with
  | some φ => (CNF.to3Aux (z.length + 1) φ).1
  | none => falseFormula

theorem reduction_eq_encode (z : List Bool) : reduction z = (redCNF z).encode := by
  rw [reduction, redCNF]
  cases CNF.decode? z with
  | none => rfl
  | some φ => rfl

theorem redCNF_is3CNF (z : List Bool) : (redCNF z).Is3CNF := by
  rw [redCNF]
  cases CNF.decode? z with
  | none => exact falseFormula_is3CNF
  | some φ => exact CNF.to3Aux_is3CNF _ φ

theorem satisfiable_redCNF_iff (z : List Bool) :
    (redCNF z).Satisfiable ↔ z ∈ CNFSAT.language := by
  cases hdecode : CNF.decode? z with
  | none =>
      have hz : z ∉ CNFSAT.language := by
        rw [CNFSAT.mem_language_iff_decode]
        rintro ⟨φ, hφ, _⟩
        rw [hdecode] at hφ
        exact absurd hφ (by simp)
      rw [show redCNF z = falseFormula by rw [redCNF, hdecode]]
      simp only [hz, iff_false]
      exact falseFormula_not_satisfiable
  | some φ =>
      have hz : z = φ.encode := CNF.decode?_sound hdecode
      have hfresh : φ.maxVar < z.length + 1 := by
        have hmax := CNF.maxVar_le_encode_length φ
        rw [hz]
        omega
      rw [show redCNF z = (CNF.to3Aux (z.length + 1) φ).1 by rw [redCNF, hdecode],
        CNF.to3Aux_satisfiable_iff _ φ hfresh, CNFSAT.mem_language_iff_decode]
      constructor
      · exact fun h => ⟨φ, hdecode, h⟩
      · rintro ⟨ψ, hψ, hsat⟩
        rw [hdecode] at hψ
        exact (Option.some.inj hψ) ▸ hsat

/-- **Every `NP` language is the satisfiability of an `FP` family of exact
3-CNFs.** -/
theorem exists_reduction_cnf {L : Language} (hL : L ∈ NP) :
    ∃ (E : List Bool → List Bool) (Φ : List Bool → CNF), E ∈ FP
      ∧ (∀ x, E x = (Φ x).encode) ∧ (∀ x, (Φ x).Is3CNF)
      ∧ (∀ x, x ∈ L ↔ (Φ x).Satisfiable) := by
  obtain ⟨f, hf, hiff⟩ := SAT.NPHard_language L hL
  refine ⟨fun x => reduction (f x), fun x => redCNF (f x), ?_, fun x => reduction_eq_encode _,
    fun x => redCNF_is3CNF _, fun x => ?_⟩
  · exact mem_FP_of_eq (mem_FP_comp hf ThreeSAT.reduction_mem_FP) fun x => rfl
  · rw [hiff x, ← satisfiable_redCNF_iff (f x)]

end Complexity
