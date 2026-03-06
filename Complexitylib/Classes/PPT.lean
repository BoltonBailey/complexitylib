import Complexitylib.Models.TuringMachine
import Complexitylib.Classes.Polynomial

/-!
# Probabilistic polynomial time (PPT)

This file defines the predicate `NTM.IsPPT`: an NTM is a probabilistic
polynomial-time machine if there exists a polynomial bound within which every
computation path halts. This is the central notion in Katz-Lindell's security
definitions — nearly every definition quantifies "for all PPT adversaries A."
-/

/-- An NTM is **probabilistic polynomial-time (PPT)** if there exists a
    polynomially bounded function `T` such that for every input `x`, every
    computation path of length `T(|x|)` reaches `qhalt`.

    This is the standard notion from Katz-Lindell: a PPT machine always halts
    in polynomial time regardless of its random choices. -/
def NTM.IsPPT (tm : NTM n) : Prop :=
  ∃ T, IsPolyBounded T ∧
    ∀ x (choices : Fin (T x.length) → Bool),
      tm.halted (tm.trace (T x.length) choices (tm.initCfg x))
