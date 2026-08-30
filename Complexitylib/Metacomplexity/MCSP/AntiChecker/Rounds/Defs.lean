/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.MCSP.AntiChecker.Selection.Defs

/-!
# Anti-checker shrink rounds -- definitions

This layer records a sequence of samples built by repeatedly consing a valid
survivor-shrinking input onto the prefix already constructed.
-/


@[expose] public section

namespace Complexity

namespace AntiChecker

/-- Every input in the list, read from tail to head, satisfies the requested
shrink contract relative to the prefix constructed before it. -/
def IsShrinkTrace {arity : ℕ} (denominator : ℕ)
    (target : BitString arity → Bool) (threshold : ℕ) :
    List (BitString arity) → Prop
  | [] => True
  | input :: inputs =>
      IsShrinkTrace denominator target threshold inputs ∧
        IsShrinkExtension denominator target threshold inputs input

end AntiChecker

end Complexity
