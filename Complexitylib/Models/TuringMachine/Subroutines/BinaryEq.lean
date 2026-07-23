/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Subroutines.BinaryEq.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinaryEq.Internal
import Complexitylib.Models.TuringMachine.Hoare.Space

/-!
# Binary work-tape equality

This module exposes a framed linear-time correctness theorem for the concrete
binary equality routine used by RAM register-store scans.
-/

namespace Complexity

namespace TM

/-- Two canonical binary strings are compared in linear time. The Boolean
answer is appended to `resultIdx`; input, output, unrelated tapes, and all
binary contents are preserved. -/
theorem binaryEqTM_reachesIn_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c' t,
      t ≤ binaryEqTime lhs rhs ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).reachesIn t
        { state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (binaryEqTM lhsIdx rhsIdx resultIdx).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
      (c'.work lhsIdx).HasBinaryContent lhs ∧
      1 ≤ (c'.work lhsIdx).head ∧
      (c'.work rhsIdx).HasBinaryContent rhs ∧
      1 ≤ (c'.work rhsIdx).head ∧
      (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
        c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  binaryEqTM_reachesIn_frame_internal lhsIdx rhsIdx resultIdx hdistinct
    lhs rhs inp₀ work₀ out₀ hlhs hrhs hresult hinput hother houtput

/-- Compositional time-bounded form of `binaryEqTM_reachesIn_frame`. -/
theorem binaryEqTM_hoareTime_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
        (work lhsIdx).HasBinaryContent lhs ∧
        1 ≤ (work lhsIdx).head ∧
        (work rhsIdx).HasBinaryContent rhs ∧
        1 ≤ (work rhsIdx).head ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryEqTime lhs rhs) :=
  binaryEqTM_hoareTime_frame_internal lhsIdx rhsIdx resultIdx hdistinct lhs rhs
    inp₀ work₀ out₀ hlhs hrhs hresult hinput hother houtput

/-- Time-and-space form of canonical binary equality. -/
theorem binaryEqTM_hoareTimeSpace_frame {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n)
    (hdistinct : BinaryEqDistinct lhsIdx rhsIdx resultIdx)
    (lhs rhs : List Bool) (inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hlhs : (work₀ lhsIdx).HasBinaryString lhs)
    (hrhs : (work₀ rhsIdx).HasBinaryString rhs)
    (hresult : (work₀ resultIdx).HasBinaryPrefix [])
    (hinput : inp₀.read ≠ Γ.start)
    (hother : ∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
      (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start)
    (hinitial :
      ({ state := (binaryEqTM lhsIdx rhsIdx resultIdx).qstart,
         input := inp₀,
         work := work₀,
         output := out₀ } :
        Cfg n (binaryEqTM lhsIdx rhsIdx resultIdx).Q).WithinAuxSpace
          inputLength initialSpace) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        (work resultIdx).HasBinaryPrefix [decide (lhs = rhs)] ∧
        (work lhsIdx).HasBinaryContent lhs ∧
        1 ≤ (work lhsIdx).head ∧
        (work rhsIdx).HasBinaryContent rhs ∧
        1 ≤ (work rhsIdx).head ∧
        (∀ i, i ≠ lhsIdx → i ≠ rhsIdx → i ≠ resultIdx →
          work i = work₀ i) ∧
        out = out₀)
      (binaryEqTime lhs rhs) inputLength
      (initialSpace + binaryEqTime lhs rhs) :=
  binaryEqTM_hoareTimeSpace_frame_internal lhsIdx rhsIdx resultIdx hdistinct
    lhs rhs inputLength initialSpace inp₀ work₀ out₀ hlhs hrhs hresult hinput
    hother houtput hinitial

/-- Binary equality preserves one-way output safety. -/
theorem binaryEqTM_isTransducer {n : ℕ}
    (lhsIdx rhsIdx resultIdx : Fin n) :
    (binaryEqTM lhsIdx rhsIdx resultIdx).IsTransducer :=
  binaryEqTM_isTransducer_internal lhsIdx rhsIdx resultIdx

end TM

end Complexity
