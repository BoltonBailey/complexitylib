/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.CodeSearch
public import Complexitylib.Models.TuringMachine.GuessStream
public import Complexitylib.Classes.Containments.Internal.WitnessEnum

/-!
# Fixed-width bit layouts

⚠️ Unreviewed by Bolton

A machine that searches the configuration space of another machine has to hold configurations in
registers and step a counter through all of them. Both want the same thing: a **fixed-width**
bit layout, so that a register is a fixed number of cells and the enumeration is one binary
counter.

`Complexity.BitCodec` is that layout, packaged so it can be built up field by field. Each codec
carries its width, an encoder, a decoder that is total on every bitstring, and the two facts a
caller needs: the encoding has the declared width, and decoding inverts it. The combinators —
`Complexity.BitCodec.prod`, `Complexity.BitCodec.fn`, `Complexity.BitCodec.equiv` — discharge
those obligations once, so a record layout is assembled rather than proved.

The decoder being total matters. The machine enumerates *all* bitstrings of the layout's width,
not just the ones in the image, so every register value must denote something; the ones outside
the image simply denote a configuration that no walk ever reaches.

So does where the head positions go. A machine reads a register by scanning it, so a head stored
as a number in its own field would be useless — to check the cell it points at, the scan would
have to turn around. `Complexity.tapeCodec` therefore stores the head as a **marker beside each
cell**: the scan learns at every cell whether the head is there, which is what makes a
`Complexity.Scanner` able to check a transition of the simulated machine without ever counting.

## Main definitions

- `Complexity.BitCodec` — a fixed-width bit layout
- `Complexity.BitCodec.fin`, `.gamma`, `.bool`, `.prod`, `.fn`, `.equiv` — the combinators
- `Complexity.tapeCodec` — a tape window, with the head marked beside the cell it is on
- `Complexity.codeCodec` — the layout of a configuration code

## Main results

- `Complexity.BitCodec.enc_injective` — a layout distinguishes what it encodes
- `Complexity.codeCodec_width` — the width of a configuration code
-/

@[expose] public section

namespace Complexity

/-- A fixed-width bit layout for `α`: an encoder of constant width, and a decoder that is total
on every bitstring and inverts it. -/
structure BitCodec (α : Type) where
  /-- The number of bits an encoded value occupies. -/
  width : ℕ
  /-- The encoder. -/
  enc : α → List Bool
  /-- The decoder, total on every bitstring. -/
  dec : List Bool → α
  /-- Encodings have the declared width. -/
  enc_length : ∀ a, (enc a).length = width
  /-- Decoding inverts encoding. -/
  dec_enc : ∀ a, dec (enc a) = a

namespace BitCodec

theorem enc_injective {α : Type} (c : BitCodec α) : Function.Injective c.enc := by
  intro a b h
  rw [← c.dec_enc a, ← c.dec_enc b, h]

/-! ## Leaves -/

/-- A bounded index, little-endian in `w` bits. -/
def fin (m w : ℕ) [NeZero m] (h : m ≤ 2 ^ w) : BitCodec (Fin m) where
  width := w
  enc i := bitsOfLenLE w i.val
  dec l := ⟨binValLE (l.take w) % m, Nat.mod_lt _ (NeZero.pos m)⟩
  enc_length _ := bitsOfLenLE_length _ _
  dec_enc i := by
    have hlen : (bitsOfLenLE w i.val).length = w := bitsOfLenLE_length _ _
    have htake : (bitsOfLenLE w i.val).take w = bitsOfLenLE w i.val := by
      rw [List.take_of_length_le (le_of_eq hlen)]
    have hval : binValLE (bitsOfLenLE w i.val) = i.val :=
      binValLE_bitsOfLenLE w i.val (lt_of_lt_of_le i.isLt h)
    apply Fin.ext
    show binValLE ((bitsOfLenLE w i.val).take w) % m = i.val
    rw [htake, hval, Nat.mod_eq_of_lt i.isLt]

/-- A tape symbol, in two bits. -/
def gamma : BitCodec Γ where
  width := 2
  enc g :=
    match g with
    | .zero => [false, false]
    | .one => [true, false]
    | .blank => [false, true]
    | .start => [true, true]
  dec l :=
    match l.take 2 with
    | [false, false] => .zero
    | [true, false] => .one
    | [false, true] => .blank
    | _ => .start
  enc_length g := by cases g <;> rfl
  dec_enc g := by cases g <;> rfl

/-- A single bit. -/
def bool : BitCodec Bool where
  width := 1
  enc b := [b]
  dec l := l.headI
  enc_length _ := rfl
  dec_enc _ := rfl

/-! ## Reading a value out of a scan

A scan puts a register's leading bits into a table (`Complexity.Scanner.bitsStep`). This reads the
value they encode back out, which is how a check recovers, say, the simulated machine's state from
the parameters it was handed. -/

/-- The value a table of bits encodes. -/
def ofTable {α : Type} (c : BitCodec α) (f : Fin c.width → Bool) : α :=
  c.dec (List.ofFn f)

theorem ofTable_eq {α : Type} (c : BitCodec α) (a : α) (f : Fin c.width → Bool)
    (h : ∀ i : Fin c.width,
      f i = (c.enc a)[i.val]'(by rw [c.enc_length]; exact i.isLt)) :
    c.ofTable f = a := by
  have hlist : List.ofFn f = c.enc a := by
    refine List.ext_getElem (by simp [c.enc_length]) ?_
    intro i h1 h2
    have hi : i < c.width := by simpa using h1
    rw [List.getElem_ofFn]
    exact h ⟨i, hi⟩
  rw [ofTable, hlist, c.dec_enc]

/-! ## Combinators -/

/-- Two layouts side by side. -/
def prod {α β : Type} (c : BitCodec α) (d : BitCodec β) : BitCodec (α × β) where
  width := c.width + d.width
  enc p := c.enc p.1 ++ d.enc p.2
  dec l := (c.dec (l.take c.width), d.dec (l.drop c.width))
  enc_length p := by
    rw [List.length_append, c.enc_length, d.enc_length]
  dec_enc p := by
    have h1 : (c.enc p.1 ++ d.enc p.2).take c.width = c.enc p.1 := by
      rw [List.take_append_of_le_length (le_of_eq (c.enc_length p.1).symm),
        List.take_of_length_le (le_of_eq (c.enc_length p.1))]
    have h2 : (c.enc p.1 ++ d.enc p.2).drop c.width = d.enc p.2 := by
      rw [← c.enc_length p.1, List.drop_left]
    rw [h1, h2, c.dec_enc, d.dec_enc]

/-- Transport a layout along an equivalence. -/
def equiv {α β : Type} (e : α ≃ β) (c : BitCodec β) : BitCodec α where
  width := c.width
  enc a := c.enc (e a)
  dec l := e.symm (c.dec l)
  enc_length a := c.enc_length _
  dec_enc a := by rw [c.dec_enc, Equiv.symm_apply_apply]

/-- The `i`-th fixed-width chunk of a concatenation. -/
theorem take_drop_flatten {α : Type} (w : ℕ) :
    ∀ (L : List (List α)), (∀ l ∈ L, l.length = w) →
      ∀ (i : ℕ), (hi : i < L.length) → ((L.flatten).drop (i * w)).take w = L[i] := by
  intro L
  induction L with
  | nil => intro _ i hi; simp at hi
  | cons l L ih =>
      intro hlen i hi
      cases i with
      | zero =>
          have hl : l.length = w := hlen l (by simp)
          simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons]
          rw [List.take_append_of_le_length (le_of_eq hl.symm),
            List.take_of_length_le (le_of_eq hl)]
          rfl
      | succ i =>
          have hl : l.length = w := hlen l (by simp)
          have hdrop : ((l :: L).flatten).drop ((i + 1) * w) = (L.flatten).drop (i * w) := by
            have h1 : (l ++ L.flatten).drop (l.length + i * w) = (L.flatten).drop (i * w) := by
              rw [← List.drop_drop, List.drop_left]
            rw [List.flatten_cons, show (i + 1) * w = l.length + i * w by rw [hl]; ring]
            exact h1
          rw [hdrop, ih (fun x hx => hlen x (by simp [hx])) i (by simpa using hi)]
          rfl

/-- A fixed number of copies of a layout, side by side. -/
def fn {α : Type} (m : ℕ) (c : BitCodec α) : BitCodec (Fin m → α) where
  width := m * c.width
  enc f := ((List.finRange m).map (fun i => c.enc (f i))).flatten
  dec l := fun i => c.dec ((l.drop (i.val * c.width)).take c.width)
  enc_length f := by
    rw [List.length_flatten]
    have : ((List.finRange m).map (fun i => c.enc (f i))).map List.length
        = (List.finRange m).map (fun _ => c.width) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => c.enc_length (f i))
    rw [this]
    simp
  dec_enc f := by
    funext i
    have hlen : ∀ l ∈ (List.finRange m).map (fun i => c.enc (f i)), l.length = c.width := by
      intro l hl
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hl
      exact c.enc_length _
    have hi : i.val < ((List.finRange m).map (fun i => c.enc (f i))).length := by
      simp [i.isLt]
    rw [take_drop_flatten c.width _ hlen i.val hi]
    simp [c.dec_enc]

end BitCodec

/-! ## The layout of a configuration code -/

/-- Bits enough to index `m` values. -/
def bitWidth (m : ℕ) : ℕ := Nat.clog 2 m

theorem le_two_pow_bitWidth (m : ℕ) : m ≤ 2 ^ bitWidth m :=
  Nat.le_pow_clog (by norm_num) m

/-- The layout of a bounded index. -/
def finCodec (m : ℕ) [NeZero m] : BitCodec (Fin m) :=
  BitCodec.fin m (bitWidth m) (le_two_pow_bitWidth m)

@[simp] theorem finCodec_width (m : ℕ) [NeZero m] : (finCodec m).width = bitWidth m := rfl

/-- The layout of a machine state. -/
noncomputable def qCodec (Q : Type) [Fintype Q] [Nonempty Q] : BitCodec Q :=
  haveI : NeZero (Fintype.card Q) := ⟨Fintype.card_ne_zero⟩
  BitCodec.equiv (Fintype.equivFin Q) (finCodec (Fintype.card Q))

/-! ## Marking a head position where the scan will meet it

A machine reads a register by scanning it, so a head position stored as a number in its own field
is useless: to check the cell it points at, the scan would have to come back. Storing it as a
**marker beside each cell** makes the head local — the scan learns, at each cell, whether the head
is there. -/

/-- Where the marker sits, or `0` if there is none. -/
def markIdx {m : ℕ} (f : Fin m → Bool × Γ) : ℕ :=
  NTM.searchIdx (fun q => if h : q < m then (f ⟨q, h⟩).1 else false) m

/-- Mark the cell the head is on. The marker comes first in the chunk, so that a scan knows
whether the head is on a cell before it reads that cell's symbol. -/
def mark {m : ℕ} (p : Fin m × (Fin m → Γ)) : Fin m → Bool × Γ :=
  fun i => (decide (i = p.1), p.2 i)

/-- Read the head position back off the markers. Total: with no marker, or several, it reads the
head as sitting at the first cell. -/
def unmark {m : ℕ} [NeZero m] (f : Fin m → Bool × Γ) : Fin m × (Fin m → Γ) :=
  (⟨min (markIdx f) (m - 1), by
      have hm : 0 < m := Nat.pos_of_neZero m
      omega⟩,
    fun i => (f i).2)

theorem markIdx_mark {m : ℕ} (p : Fin m × (Fin m → Γ)) : markIdx (mark p) = p.1.val := by
  refine NTM.searchIdx_eq p.1.isLt ?_ ?_
  · simp [mark, p.1.isLt]
  · intro q hq
    by_cases h : q < m
    · have hqp : (⟨q, h⟩ : Fin m) = p.1 := by simpa [mark, h] using hq
      exact congrArg Fin.val hqp
    · simp [h] at hq

@[simp] theorem unmark_mark {m : ℕ} [NeZero m] (p : Fin m × (Fin m → Γ)) :
    unmark (mark p) = p := by
  have hm : 0 < m := Nat.pos_of_neZero m
  refine Prod.ext ?_ rfl
  apply Fin.ext
  show min (markIdx (mark p)) (m - 1) = p.1.val
  rw [markIdx_mark]
  have := p.1.isLt
  omega

/-- The two bits a symbol occupies. -/
def gammaBits : Γ → Bool × Bool
  | .zero => (false, false)
  | .one => (true, false)
  | .blank => (false, true)
  | .start => (true, true)

theorem gamma_enc_eq (g : Γ) :
    BitCodec.gamma.enc g = [(gammaBits g).1, (gammaBits g).2] := by
  cases g <;> rfl

/-- The layout of one work tape's window: each cell beside a bit saying whether the head is on
it. -/
def tapeCodec (m : ℕ) [NeZero m] : BitCodec (Fin m × (Fin m → Γ)) where
  width := m * 3
  enc p := (BitCodec.fn m (BitCodec.bool.prod BitCodec.gamma)).enc (mark p)
  dec l := unmark ((BitCodec.fn m (BitCodec.bool.prod BitCodec.gamma)).dec l)
  enc_length p := (BitCodec.fn m (BitCodec.bool.prod BitCodec.gamma)).enc_length _
  dec_enc p := by
    rw [(BitCodec.fn m (BitCodec.bool.prod BitCodec.gamma)).dec_enc, unmark_mark]

/-- **One chunk of an encoded window**: the head marker, then the cell's two symbol bits. -/
theorem tapeCodec_enc_chunk {m : ℕ} [NeZero m] (hd : Fin m) (cl : Fin m → Γ) (p : Fin m) :
    (((tapeCodec m).enc (hd, cl)).drop (p.val * 3)).take 3
      = [decide (p = hd), (gammaBits (cl p)).1, (gammaBits (cl p)).2] := by
  have hlen : ∀ l ∈ (List.finRange m).map
      (fun i => (BitCodec.bool.prod BitCodec.gamma).enc (mark (hd, cl) i)), l.length = 3 := by
    intro l hl
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
    exact (BitCodec.bool.prod BitCodec.gamma).enc_length _
  have hi : p.val < ((List.finRange m).map
      (fun i => (BitCodec.bool.prod BitCodec.gamma).enc (mark (hd, cl) i))).length := by
    simp [p.isLt]
  have hchunk := BitCodec.take_drop_flatten 3 _ hlen p.val hi
  rw [show (tapeCodec m).enc (hd, cl) = ((List.finRange m).map
      (fun i => (BitCodec.bool.prod BitCodec.gamma).enc (mark (hd, cl) i))).flatten from rfl,
    hchunk]
  simp only [List.getElem_map, List.getElem_finRange]
  show (BitCodec.bool.enc (mark (hd, cl) _).1) ++ (BitCodec.gamma.enc (mark (hd, cl) _).2) = _
  rw [gamma_enc_eq]
  rfl

/-- **The layout of a configuration code.** -/
noncomputable def codeCodec (Q : Type) [Fintype Q] [Nonempty Q] (k nn S : ℕ) :
    BitCodec (Code Q k nn S) :=
  (qCodec Q).prod ((finCodec (nn + S + 2)).prod
    ((BitCodec.fn k (tapeCodec (S + 1))).prod (tapeCodec (S + 2))))

/-- The width of a configuration code: a constant for the state, a pointer into the input, and
the window itself. -/
theorem codeCodec_width (Q : Type) [Fintype Q] [Nonempty Q] (k nn S : ℕ) :
    (codeCodec Q k nn S).width =
      bitWidth (Fintype.card Q) + (bitWidth (nn + S + 2) +
        (k * ((S + 1) * 3) + (S + 2) * 3)) := rfl

/-! ## The layout is logarithmically wide -/

theorem bitWidth_le {m w : ℕ} (h : m ≤ 2 ^ w) : bitWidth m ≤ w :=
  Nat.clog_le_of_le_pow h

theorem bitWidth_le_self (m : ℕ) : bitWidth m ≤ m :=
  bitWidth_le (le_of_lt (Nat.lt_two_pow_self))

/-- **A configuration code is logarithmically wide.** Every field is either a constant, a pointer
into the input, or a piece of the window, so the whole layout fits in a logarithmic window of its
own — which is what lets a machine hold two of them at once and still be a log-space machine. -/
theorem codeCodec_width_le (Q : Type) [Fintype Q] [Nonempty Q] (k C D : ℕ) :
    ∃ C' D' : ℕ, ∀ nn : ℕ,
      (codeCodec Q k nn (logWindow C D nn)).width ≤ logWindow C' D' nn := by
  refine ⟨C + 1 + 3 * k * C + 3 * C,
    bitWidth (Fintype.card Q) + 4 * D + 3 * k * D + 3 * k + 10, fun nn => ?_⟩
  set L := Nat.log 2 nn with hL
  set S := logWindow C D nn with hS
  have hSval : S = C * L + D := by rw [hS, logWindow, hL]
  have hin : nn + S + 2 ≤ 2 ^ (L + S + 4) := by
    have h1 : nn ≤ 2 ^ (L + 1) := le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) nn)
    have h2 : S + 2 ≤ 2 ^ (S + 2) := le_of_lt (Nat.lt_two_pow_self)
    have h3 : (2 : ℕ) ^ (L + 1) ≤ 2 ^ (L + S + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (2 : ℕ) ^ (S + 2) ≤ 2 ^ (L + S + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : (2 : ℕ) ^ (L + S + 3) + 2 ^ (L + S + 3) = 2 ^ (L + S + 4) := by ring
    omega
  have h2 : bitWidth (nn + S + 2) ≤ L + S + 4 := bitWidth_le hin
  rw [codeCodec_width, logWindow]
  calc bitWidth (Fintype.card Q) + (bitWidth (nn + S + 2) + (k * ((S + 1) * 3) + (S + 2) * 3))
      ≤ bitWidth (Fintype.card Q) + ((L + S + 4) + (k * ((S + 1) * 3) + (S + 2) * 3)) := by
        gcongr
    _ = (C + 1 + 3 * k * C + 3 * C) * L +
        (bitWidth (Fintype.card Q) + 4 * D + 3 * k * D + 3 * k + 10) := by
        rw [hSval]; ring

/-! ## Combining logarithmic bounds

The machine's space is the largest of its registers, and each register has its own logarithmic
bound; these say the family is closed under the operations the accounting needs. -/

theorem logWindow_mono {C C' D D' : ℕ} (hC : C ≤ C') (hD : D ≤ D') (n : ℕ) :
    logWindow C D n ≤ logWindow C' D' n := by
  rw [logWindow, logWindow]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hC) hD

theorem logWindow_add (C₁ D₁ C₂ D₂ n : ℕ) :
    logWindow C₁ D₁ n + logWindow C₂ D₂ n = logWindow (C₁ + C₂) (D₁ + D₂) n := by
  rw [logWindow, logWindow, logWindow]
  ring

theorem logWindow_mul (a C D n : ℕ) : a * logWindow C D n = logWindow (a * C) (a * D) n := by
  rw [logWindow, logWindow]
  ring

theorem max_logWindow_le (C₁ D₁ C₂ D₂ n : ℕ) :
    max (logWindow C₁ D₁ n) (logWindow C₂ D₂ n) ≤ logWindow (max C₁ C₂) (max D₁ D₂) n :=
  max_le (logWindow_mono (le_max_left _ _) (le_max_left _ _) n)
    (logWindow_mono (le_max_right _ _) (le_max_right _ _) n)

/-- **A polynomial counter is logarithmically wide.** The search counts rounds and codes up to
`A * (n + 1) ^ B`, so its counters fit in a logarithmic number of cells — which is what keeps the
whole machine inside a logarithmic window. -/
theorem bitWidth_poly_le (A B : ℕ) :
    ∀ n : ℕ, bitWidth (A * (n + 1) ^ B + 1) ≤ logWindow B (A + B + 1) n := by
  intro n
  set L := Nat.log 2 n with hL
  have h1 : n + 1 ≤ 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : (n + 1) ^ B ≤ (2 ^ (L + 1)) ^ B := Nat.pow_le_pow_left h1 B
  have h3 : ((2 : ℕ) ^ (L + 1)) ^ B = 2 ^ (B * (L + 1)) := by
    rw [← pow_mul, Nat.mul_comm]
  have h4 : A ≤ 2 ^ A := le_of_lt Nat.lt_two_pow_self
  have h5 : A * (n + 1) ^ B ≤ 2 ^ A * 2 ^ (B * (L + 1)) :=
    Nat.mul_le_mul h4 (by rw [← h3]; exact h2)
  have h6 : (2 : ℕ) ^ A * 2 ^ (B * (L + 1)) = 2 ^ (A + B * (L + 1)) := by rw [← pow_add]
  have h7 : (1 : ℕ) ≤ 2 ^ (A + B * (L + 1)) := Nat.one_le_two_pow
  have h8 : (2 : ℕ) ^ (A + B * (L + 1) + 1) = 2 ^ (A + B * (L + 1)) + 2 ^ (A + B * (L + 1)) := by
    rw [pow_succ]; ring
  have hle : A * (n + 1) ^ B + 1 ≤ 2 ^ (A + B * (L + 1)) + 1 := by omega
  have hfin : A * (n + 1) ^ B + 1 ≤ 2 ^ (A + B * (L + 1) + 1) := by omega
  have hb := bitWidth_le hfin
  rw [logWindow, ← hL]
  calc bitWidth (A * (n + 1) ^ B + 1) ≤ A + B * (L + 1) + 1 := hb
    _ = B * L + (A + B + 1) := by ring

end Complexity
