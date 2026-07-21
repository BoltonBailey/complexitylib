/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode.Defs
import
  Complexitylib.Models.RandomAccessMachine.Simulation.RegisterStore.Machine.EntryDecode.Internal

/-!
# RAM sparse-entry decoder

This module exposes the exact framed semantics of the concrete two-word sparse
address/value decoder.
-/

namespace Complexity

namespace RAM

namespace RegisterStore

namespace Machine

/-- Decode one canonical sparse address/value entry exactly, leaving the next
encoded entry under the source head and preserving every unrelated tape. -/
theorem entryDecodeTM_reachesIn_frame {n : ℕ}
    (tapes : EntryDecodeTapes n) (entry : Entry) (rest : List Bool)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsource : (work₀ tapes.source).HasBinarySuffix (Entry.encode entry ++ rest))
    (haddress : (work₀ tapes.address).HasBinaryPrefix [])
    (hvalue : (work₀ tapes.value).HasBinaryPrefix [])
    (haddressStart : (work₀ tapes.address).cells 0 = Γ.start)
    (hvalueStart : (work₀ tapes.value).cells 0 = Γ.start)
    (haddressCounter : (work₀ tapes.addressCounter).HasBinaryNat 0)
    (haddressWidth : (work₀ tapes.addressWidth).HasBinaryNat 0)
    (hvalueCounter : (work₀ tapes.valueCounter).HasBinaryNat 0)
    (hvalueWidth : (work₀ tapes.valueWidth).HasBinaryNat 0)
    (hinput : inp₀.read ≠ Γ.start)
    (hreads : ∀ i, (work₀ i).read ≠ Γ.start)
    (houtput : out₀.read ≠ Γ.start) :
    ∃ c',
      (entryDecodeTM tapes).reachesIn (entryDecodeTime entry.1 entry.2)
        { state := (entryDecodeTM tapes).qstart
          input := inp₀
          work := work₀
          output := out₀ } c' ∧
      (entryDecodeTM tapes).halted c' ∧
      c'.input = inp₀ ∧
      (c'.work tapes.source).HasBinarySuffix rest ∧
      (c'.work tapes.address).HasBinaryPrefix entry.1.bits ∧
      (c'.work tapes.address).cells 0 = Γ.start ∧
      (c'.work tapes.value).HasBinaryPrefix entry.2.bits ∧
      (c'.work tapes.value).cells 0 = Γ.start ∧
      (c'.work tapes.addressCounter).HasBinaryNat (bitlen entry.1) ∧
      (c'.work tapes.addressWidth).HasBinaryNat (bitlen entry.1) ∧
      (c'.work tapes.valueCounter).HasBinaryNat (bitlen entry.2) ∧
      (c'.work tapes.valueWidth).HasBinaryNat (bitlen entry.2) ∧
      (∀ i, i ≠ tapes.source → i ≠ tapes.address → i ≠ tapes.value →
        i ≠ tapes.addressCounter → i ≠ tapes.addressWidth →
        i ≠ tapes.valueCounter → i ≠ tapes.valueWidth →
        c'.work i = work₀ i) ∧
      c'.output = out₀ :=
  entryDecodeTM_reachesIn_frame_internal tapes entry rest inp₀ work₀ out₀
    hsource haddress hvalue haddressStart hvalueStart haddressCounter
      haddressWidth hvalueCounter hvalueWidth hinput hreads houtput

/-- Coarse all-prefix auxiliary-space envelope for entry decoding. -/
theorem entryDecodeTM_prefix_withinAuxSpace {n : ℕ}
    (tapes : EntryDecodeTapes n) (address value : ℕ)
    (inputLength initialSpace time : ℕ)
    (start current : Complexity.Cfg n (entryDecodeTM tapes).Q)
    (hinitial : start.WithinAuxSpace inputLength initialSpace)
    (hreach : (entryDecodeTM tapes).reachesIn time start current)
    (htime : time ≤ entryDecodeTime address value) :
    current.WithinAuxSpace inputLength
      (initialSpace + entryDecodeTime address value) :=
  (hinitial.reachesIn hreach).mono le_rfl (by omega)

/-- Entry decoding preserves one-way output safety. -/
theorem entryDecodeTM_isTransducer {n : ℕ} (tapes : EntryDecodeTapes n) :
    (entryDecodeTM tapes).IsTransducer := by
  unfold entryDecodeTM
  exact (wordDecodeTM_isTransducer tapes.source tapes.address
    tapes.addressCounter tapes.addressWidth).seqTM
      (wordDecodeTM_isTransducer tapes.source tapes.value tapes.valueCounter
        tapes.valueWidth)

end Machine

end RegisterStore

end RAM

end Complexity
