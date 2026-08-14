/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.SAT.CookLevin.Assembly
public import Complexitylib.Classes.NP.CoNP

/-!
# The complement of SAT is coNP-complete

Dualizing Cook–Levin (`SAT.NPComplete_language`) through
`NPComplete.compl` shows that the complement of the SAT language is
coNP-complete.

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

end SAT

end Complexity
