/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine

/-!
# Binary string encodings on Turing-machine tapes

Generic predicates and lemmas for tapes containing canonical binary strings.
`Tape.HasBinaryPrefix` describes a string being written from left to right,
`Tape.HasBinaryString` describes the same contents after rewinding the head to
cell one, and `Tape.HasBinarySuffix` describes a read cursor at the beginning
of a remaining suffix. These shapes are shared by deterministic and
nondeterministic machine constructions.
-/

namespace Complexity

namespace Tape

/-- A tape while a binary string is being written: cells `1..|bits|` contain
    the bits, the head is at the next cell, and the remaining tail is blank. -/
def HasBinaryPrefix (t : Tape) (bits : List Bool) : Prop :=
  t.head = bits.length + 1 ∧
  (∀ i, (h : i < bits.length) → t.cells (i + 1) = Γ.ofBool (bits[i]'h)) ∧
  (∀ i, bits.length ≤ i → t.cells (i + 1) = Γ.blank)

/-- A completed binary string: the bits are present and the head has been
    rewound to cell one. -/
def HasBinaryString (t : Tape) (bits : List Bool) : Prop :=
  t.head = 1 ∧
  (∀ i, (h : i < bits.length) → t.cells (i + 1) = Γ.ofBool (bits[i]'h)) ∧
  (∀ i, bits.length ≤ i → t.cells (i + 1) = Γ.blank)

/-- A read cursor at the beginning of a remaining binary suffix. The suffix
starts under the current off-marker head, is followed immediately by blank,
and the tape has no stray left markers. -/
def HasBinarySuffix (t : Tape) (bits : List Bool) : Prop :=
  t.head ≥ 1 ∧
  (∀ i, (h : i < bits.length) →
    t.cells (t.head + i) = Γ.ofBool (bits[i]'h)) ∧
  t.cells (t.head + bits.length) = Γ.blank ∧
  (∀ j, j ≥ 1 → t.cells j ≠ Γ.start)

/-- A completed binary string whose length is at most `B`. -/
def HasBoundedBinaryString (t : Tape) (B : ℕ) : Prop :=
  ∃ bits : List Bool, bits.length ≤ B ∧ t.HasBinaryString bits

/-- A completed binary tape encodes exactly `bits` as its output string. -/
theorem hasOutput_of_hasBinaryString {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) : t.HasOutput bits :=
  ⟨h.2.1, h.2.2 bits.length le_rfl⟩

/-- A completed binary tape never contains `▷` after the left-end marker. -/
theorem cells_ne_start_of_hasBinaryString {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start := by
  intro j hj
  let i := j - 1
  have hj_eq : j = i + 1 := by omega
  by_cases hi : i < bits.length
  · rw [hj_eq, h.2.1 i hi]
    cases bits[i]'hi <;> simp [Γ.ofBool]
  · have hge : bits.length ≤ i := by omega
    rw [hj_eq, h.2.2 i hge]
    decide

/-- A completed binary tape with the left marker at cell `0` is exactly the
    standard initialized tape for those bits, moved to cell `1`. -/
theorem eq_init_move_right_of_hasBinaryString {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) (h0 : t.cells 0 = Γ.start) :
    t = (Tape.init (bits.map Γ.ofBool)).move Dir3.right := by
  cases t with
  | mk head cells =>
    simp only [HasBinaryString] at h
    rcases h with ⟨hhead, hbits, htail⟩
    simp only at h0 hbits htail
    subst head
    simp only [Tape.move]
    congr
    funext j
    by_cases hj0 : j = 0
    · subst hj0
      simp [Tape.init, h0]
    · let i := j - 1
      have hj : j = i + 1 := by omega
      rw [hj]
      by_cases hi : i < bits.length
      · rw [hbits i hi, Tape.init_ofBool_cells_lt bits i hi]
      · have hge : bits.length ≤ i := by omega
        rw [htail i hge, Tape.init_ofBool_cells_ge bits i hge]

/-- Bounded completed binary tapes expose exact initialized tape shape for
    some string whose length satisfies the same bound. -/
theorem exists_eq_init_move_right_of_hasBoundedBinaryString {t : Tape} {B : ℕ}
    (h : t.HasBoundedBinaryString B) (h0 : t.cells 0 = Γ.start) :
    ∃ bits : List Bool, bits.length ≤ B ∧
      t = (Tape.init (bits.map Γ.ofBool)).move Dir3.right := by
  obtain ⟨bits, hlen, hbits⟩ := h
  exact ⟨bits, hlen, eq_init_move_right_of_hasBinaryString hbits h0⟩

/-- A freshly initialized empty tape, moved right past `▷`, is an empty
    binary prefix. -/
theorem init_nil_move_right_hasBinaryPrefix_nil :
    ((Tape.init []).move Dir3.right).HasBinaryPrefix [] := by
  simp [HasBinaryPrefix, Tape.init, Tape.move]

/-- A freshly initialized binary tape starts with its whole string as the
remaining suffix. -/
theorem init_move_right_hasBinarySuffix (bits : List Bool) :
    ((Tape.init (bits.map Γ.ofBool)).move Dir3.right).HasBinarySuffix bits := by
  refine ⟨by simp [Tape.move, Tape.init], ?_, ?_, ?_⟩
  · intro i hi
    simpa [Tape.move, Tape.init, Nat.add_comm] using
      Tape.init_ofBool_cells_lt bits i hi
  · simp [Tape.move, Tape.init, Nat.add_comm]
  · intro j hj
    simp [Tape.move]
    exact Tape.init_ofBool_cells_ne_start bits j hj

/-- A completed binary string exposes the same bits as its remaining suffix. -/
theorem HasBinaryString.hasBinarySuffix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryString bits) : t.HasBinarySuffix bits := by
  refine ⟨by rw [h.1], ?_, ?_, cells_ne_start_of_hasBinaryString h⟩
  · intro i hi
    rw [h.1]
    simpa [Nat.add_comm] using h.2.1 i hi
  · rw [h.1]
    simpa [Nat.add_comm] using h.2.2 bits.length le_rfl

/-- The first symbol of a nonempty binary suffix is under the tape head. -/
theorem HasBinarySuffix.read_cons {t : Tape} {bit : Bool} {bits : List Bool}
    (h : t.HasBinarySuffix (bit :: bits)) :
    t.read = Γ.ofBool bit := by
  have hzero := h.2.1 0 (by simp)
  simpa [Tape.read] using hzero

/-- Moving right after reading the first bit exposes the remaining suffix. -/
theorem HasBinarySuffix.move_right_cons {t : Tape} {bit : Bool}
    {bits : List Bool} (h : t.HasBinarySuffix (bit :: bits)) :
    (t.move Dir3.right).HasBinarySuffix bits := by
  refine ⟨by simp [Tape.move], ?_, ?_, ?_⟩
  · intro i hi
    have hcell := h.2.1 (i + 1) (by simpa using hi)
    simpa [Tape.move, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcell
  · have hcell := h.2.2.1
    simpa [Tape.move, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcell
  · intro j hj
    simpa [Tape.move_cells] using h.2.2.2 j hj

/-- An empty remaining suffix reads the terminating blank. -/
theorem HasBinarySuffix.read_nil {t : Tape} (h : t.HasBinarySuffix []) :
    t.read = Γ.blank := by
  simpa [Tape.read] using h.2.2.1

/-- A binary suffix cursor never reads the left-end marker. -/
theorem HasBinarySuffix.read_ne_start {t : Tape} {bits : List Bool}
    (h : t.HasBinarySuffix bits) : t.read ≠ Γ.start :=
  h.2.2.2 t.head h.1

/-- Writing the next bit extends a binary prefix by one cell. -/
theorem hasBinaryPrefix_write_bit {t : Tape} {bits : List Bool} (bit : Bool)
    (h : t.HasBinaryPrefix bits) :
    (t.writeAndMove (Γ.ofBool bit) Dir3.right).HasBinaryPrefix (bits ++ [bit]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Tape.writeAndMove, Tape.write, Tape.move, h.1]
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    by_cases hidx : i = bits.length
    · have hcellidx : i + 1 = t.head := by rw [h.1, hidx]
      have hget : (bits ++ [bit])[i]'hi = bit := by
        subst hidx
        simp
      rw [hcellidx, Function.update_self, hget]
    · have hi_bits : i < bits.length := by
        rw [List.length_append, List.length_singleton] at hi
        omega
      have hcell := h.2.1 i hi_bits
      have hget : (bits ++ [bit])[i]'hi = bits[i]'hi_bits := by
        exact List.getElem_append_left (as := bits) (bs := [bit]) hi_bits
      have hne : t.head ≠ i + 1 := by rw [h.1]; omega
      rw [Function.update_of_ne (Ne.symm hne), hcell, hget]
  · intro i hi
    unfold Tape.writeAndMove
    simp only [Tape.move]
    unfold Tape.write
    have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
    simp only [hhead_ne, ↓reduceIte]
    have hne : t.head ≠ i + 1 := by
      rw [List.length_append, List.length_singleton] at hi
      rw [h.1]
      omega
    rw [Function.update_of_ne (Ne.symm hne)]
    exact h.2.2 i (by
      rw [List.length_append, List.length_singleton] at hi
      omega)

/-- Writing the next bit preserves the left-end marker cell. -/
theorem hasBinaryPrefix_write_bit_cell0 {t : Tape} {bits : List Bool} (bit : Bool)
    (h : t.HasBinaryPrefix bits) (h0 : t.cells 0 = Γ.start) :
    (t.writeAndMove (Γ.ofBool bit) Dir3.right).cells 0 = Γ.start := by
  unfold Tape.writeAndMove
  rw [Tape.move_cells]
  unfold Tape.write
  have hhead_ne : ¬t.head = 0 := by rw [h.1]; omega
  simp only [hhead_ne, ↓reduceIte]
  have hne : t.head ≠ 0 := by rw [h.1]; omega
  rw [Function.update_of_ne (Ne.symm hne)]
  exact h0

/-- A binary prefix never contains `▷` after the left-end marker. -/
theorem cells_ne_start_of_hasBinaryPrefix {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) :
    ∀ j, j ≥ 1 → t.cells j ≠ Γ.start := by
  intro j hj
  let i := j - 1
  have hj_eq : j = i + 1 := by omega
  by_cases hi : i < bits.length
  · rw [hj_eq, h.2.1 i hi]
    cases bits[i]'hi <;> simp [Γ.ofBool]
  · have hge : bits.length ≤ i := by omega
    rw [hj_eq, h.2.2 i hge]
    decide

/-- Moving a completed binary string's head to the first blank, without
    changing its cells, yields the corresponding appendable prefix. -/
theorem hasBinaryPrefix_of_hasBinaryString {t t' : Tape} {bits : List Bool}
    (hstring : t.HasBinaryString bits)
    (hhead : t'.head = bits.length + 1)
    (hcells : t'.cells = t.cells) :
    t'.HasBinaryPrefix bits := by
  refine ⟨hhead, ?_, ?_⟩
  · intro i hi
    rw [hcells]
    exact hstring.2.1 i hi
  · intro i hi
    rw [hcells]
    exact hstring.2.2 i hi

/-- Rewinding a binary prefix to cell one yields a completed binary string. -/
theorem hasBinaryString_of_hasBinaryPrefix {t t' : Tape} {bits : List Bool}
    (hprefix : t.HasBinaryPrefix bits)
    (hhead : t'.head = 1)
    (hcells : t'.cells = t.cells) :
    t'.HasBinaryString bits := by
  refine ⟨hhead, ?_, ?_⟩
  · intro i hi
    rw [hcells]
    exact hprefix.2.1 i hi
  · intro i hi
    rw [hcells]
    exact hprefix.2.2 i hi

end Tape

end Complexity
