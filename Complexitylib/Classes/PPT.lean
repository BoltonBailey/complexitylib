import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics

/-!
# Probabilistic polynomial time (PPT)

This file defines the predicate `NTM.IsPPT`: an NTM is a probabilistic
polynomial-time machine if its running time is `O(n^k)` for some `k`, with
every computation path halting within the bound. This is the central notion
in cryptographic security definitions — nearly every definition quantifies
"for all PPT adversaries A."
-/

open Complexity

/-- An NTM is **probabilistic polynomial-time (PPT)** if there exist a time
    bound `f` and degree `d` such that every computation path halts within
    `f(|x|)` steps and `f(n) = O(n^d)`. -/
def NTM.IsPPT (tm : NTM n) : Prop :=
  ∃ (f : ℕ → ℕ) (d : ℕ), tm.AllPathsHaltIn f ∧ f =O (· ^ d)
