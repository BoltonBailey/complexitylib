/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics

/-!
# Base space complexity classes

This file defines the parametric space complexity classes `DSPACE(S)` and
`NSPACE(S)`, the building blocks from which polynomial and log-space classes
are derived.

Space is measured on work tapes only. The input tape is read-only (structurally
in our model) and does not count. The output tape is unrestricted in these base
definitions; classes where the output tape could serve as extra workspace (e.g.
L, NL) add the transducer constraint (`IsTransducer`) at the class level.
-/

namespace Complexity


/-- `DSPACE(S)` is the class of languages decidable by a deterministic TM using
    `O(S(n))` space on work tapes. -/
def DSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.DecidesInSpace L f ∧ f =O S}

/-- `NSPACE(S)` is the class of languages decidable by a nondeterministic TM
    using `O(S(n))` space on work tapes. -/
def NSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInSpace L f ∧ f =O S}

end Complexity
