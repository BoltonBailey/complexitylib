/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Internal

/-!
# Copying canonical binary naturals

This module exposes a literal-frame copy operation assembled from work-tape
clearing and binary addition. The source is preserved, the destination becomes
an exact copy, and the private addition counter is restored to canonical zero.

## Main results

- `TM.binaryCopyIntoTM_hoareTime_frame` gives the literal endpoint and time bound.
- `TM.binaryCopyIntoTM_hoareTimeSpace_frame` adds an all-prefix width bound.
- `TM.binaryCopyIntoTM_isTransducer` proves append-only-output safety.
-/

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Binary copying changes only the destination tape. The source, zero
counter, input, output, and every unrelated work tape are preserved literally. -/
theorem binaryCopyIntoTM_hoareTime_frame
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dstIdx
          ((Tape.init (srcValue.bits.map Γ.ofBool)).move Dir3.right) ∧
        out = out₀)
      (binaryCopyTime srcValue dstValue) :=
  binaryCopyIntoTM_hoareTime_frame_internal srcIdx dstIdx counterIdx
    hsrcDst hsrcCounter hdstCounter srcValue dstValue inp₀ work₀ out₀
    hsrc hdst hcounter hinp hother hout

/-- Time-and-space form of canonical binary copying. Every reachable
configuration stays within the maximum of the clearing and addition bounds. -/
theorem binaryCopyIntoTM_hoareTimeSpace_frame
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dstIdx
          ((Tape.init (srcValue.bits.map Γ.ofBool)).move Dir3.right) ∧
        out = out₀)
      (binaryCopyTime srcValue dstValue) inputLength
      (binaryCopySpace initialSpace srcValue dstValue) :=
  binaryCopyIntoTM_hoareTimeSpace_frame_internal srcIdx dstIdx counterIdx
    hsrcDst hsrcCounter hdstCounter srcValue dstValue inputLength
    initialSpace inp₀ work₀ out₀ hsrc hdst hcounter hinp hother hout
    hworkSpace hinputSpace

/-- Canonical binary copying never moves the output head left. -/
theorem binaryCopyIntoTM_isTransducer
    (srcIdx dstIdx counterIdx : Fin n) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).IsTransducer :=
  binaryCopyIntoTM_isTransducer_internal srcIdx dstIdx counterIdx

end TM

end Complexity
