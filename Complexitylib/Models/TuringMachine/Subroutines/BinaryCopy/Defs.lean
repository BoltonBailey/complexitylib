/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd.Defs

/-!
# Copying canonical binary naturals

This definitions layer composes work-tape clearing with canonical binary
addition. The source and addition scratch tapes are preserved, while the
destination is replaced by an exact copy of the source.
-/

namespace Complexity

namespace TM

/-- Clear `dstIdx`, then copy the canonical binary natural on `srcIdx` into it.
The distinct `counterIdx` is the zero scratch used by binary addition. -/
def binaryCopyIntoTM {n : ℕ}
    (srcIdx dstIdx counterIdx : Fin n) : TM n :=
  seqTM (clearWorkTM dstIdx)
    (binaryAddIntoTM srcIdx dstIdx counterIdx)

/-- Compositional running-time bound for canonical binary copying. -/
def binaryCopyTime (srcValue dstValue : ℕ) : ℕ :=
  clearWorkTimeBound dstValue.size + 1 + binaryAddTime srcValue 0

/-- All-prefix auxiliary-space bound for canonical binary copying. -/
def binaryCopySpace (initialSpace srcValue dstValue : ℕ) : ℕ :=
  max (initialSpace + clearWorkTimeBound dstValue.size)
    (binaryAddSpace initialSpace srcValue 0)

end TM

end Complexity
