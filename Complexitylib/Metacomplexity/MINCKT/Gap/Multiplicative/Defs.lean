/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MINCKT.Gap.Defs

/-!
# Multiplicative-gap conditional MinKT -- definitions

This is the exact machine-relative promise from Definition 6.5 of Hirahara's
*Symmetry of Information from Meta-Complexity*. It retains the same
depth-adjusted yes side as `GapMINCKT`, but replaces the no threshold by

`sigma(|x|) * s + log_2(tau(|x|,|y|,t))`.

The canonical `(x,y,1^t,1^s)` codec and trivariate clock parameters are reused
verbatim. The factor is an explicit function of the output length.
-/


@[expose] public section

namespace Complexity

namespace GapMINCKT

namespace Multiplicative

/-- Definition 6.5's multiplicative no condition. -/
def IsNo {conditionalTapes : ℕ} (inst : GapMINCKT.Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ) : Prop :=
  (factor inst.output.length * inst.threshold + inst.logSlack parameters : ℕ) <
    (inst.base.withTime (inst.laterTime parameters)).complexity
      conditionalMachine

/-- A concrete transformed-clock program forbidden by the multiplicative no
condition. -/
def IsRelaxedWitness {conditionalTapes : ℕ}
    (inst : GapMINCKT.Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (program : List Bool) : Prop :=
  program.length ≤
      factor inst.output.length * inst.threshold + inst.logSlack parameters ∧
    conditionalMachine.ProducesInTime
      (RandomAccessCondition.oracle inst.condition) program inst.output
        (inst.laterTime parameters)

/-- Definition 6.5 has exactly the additive promise's depth-adjusted yes side. -/
def yesLanguage {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) : Language :=
  GapMINCKT.yesLanguage ordinaryMachine conditionalMachine parameters

/-- Canonically encoded multiplicative no language. -/
def noLanguage {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ) : Language :=
  {bits | match GapMINCKT.Instance.decode? bits with
    | some inst => IsNo inst conditionalMachine parameters factor
    | none => False}

end Multiplicative

end GapMINCKT

end Complexity
