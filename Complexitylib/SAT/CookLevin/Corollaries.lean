/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.CookLevin.Assembly
public import Complexitylib.Classes.NP.CoNP
public import Complexitylib.Classes.NP.Closure

/-!
# Corollaries of Cook–Levin

Structural consequences of the NP-completeness of SAT
(`SAT.NPComplete_language`):

* `SAT.coNPComplete_compl_language` — the complement of the SAT language is
  coNP-complete, by dualizing through `NPComplete.compl`.
* `SAT.language_mem_P_iff_P_eq_NP` — SAT is decidable in deterministic
  polynomial time iff `P = NP`.

Note that `languageᶜ` is the complement *as a set of bit-strings*: it
contains the encodings of unsatisfiable CNF formulas together with all
strings that are not well-formed formula encodings. This is the standard
convention — completeness of the complement holds regardless, because the
ill-formed strings are polynomial-time recognizable.
-/


public section

namespace Complexity

namespace SAT

/-- **The complement of SAT is coNP-complete.** Immediate dual of the
    Cook–Levin theorem `NPComplete_language`. -/
theorem coNPComplete_compl_language : coNPComplete languageᶜ :=
  NPComplete_language.compl

/-- **SAT is in `P` iff `P = NP`.** Deciding satisfiability in deterministic
    polynomial time is equivalent to the collapse of `NP` to `P`. -/
theorem language_mem_P_iff_P_eq_NP : language ∈ P ↔ P = NP :=
  NPComplete_language.mem_P_iff_P_eq_NP

/-- **SAT is in `coNP` iff `NP = coNP`.** A coNP certificate for
    satisfiability would collapse `NP` and `coNP`. -/
theorem language_mem_coNP_iff_NP_eq_coNP : language ∈ coNP ↔ NP = coNP :=
  NPComplete_language.mem_coNP_iff_NP_eq_coNP

end SAT

end Complexity
