import Complexitylib.Models.TuringMachine

/-!
# Single-tape simulation — encoding internals

Foundations for `NTM.singleTapeSim` (see `docs/A4-SingleTapeSimulation.md`):
the binary symbol codec and the block-index arithmetic for laying `k` work
tapes onto one. These are **path-independent**: any single-work-tape encoding
over the fixed alphabet `Γ = {0,1,□,▷}` needs a binary code (so that literal
`□` can serve as the end-of-used-region sentinel) and a per-position block
layout. Proof internals only — correctness of the full simulation is
established downstream.
-/

namespace NTM.SingleTape

/-! ## Binary symbol codec

A writable symbol `Γw = {0,1,□}` is stored in two cells over `{0,1}` (never
`□`), so that a literal `□` inside the used region is impossible and can mark
its end. Code: `□ ↦ 00`, `0 ↦ 01`, `1 ↦ 10`. -/

/-- Encode a writable symbol as a 2-cell binary code. -/
def encSym : Γw → Γ × Γ
  | .blank => (Γ.zero, Γ.zero)
  | .zero  => (Γ.zero, Γ.one)
  | .one   => (Γ.one, Γ.zero)

/-- Decode a 2-cell code back to a writable symbol (any non-code pair ↦ `□`). -/
def decSym : Γ → Γ → Γw
  | Γ.zero, Γ.one => .zero
  | Γ.one,  Γ.zero => .one
  | _,      _      => .blank

/-- The codec round-trips. -/
@[simp] theorem decSym_encSym (s : Γw) :
    decSym (encSym s).1 (encSym s).2 = s := by
  cases s <;> rfl

/-- No active code cell is `□`: encoded symbols use only `{0,1}`. This is what
    lets a literal `□` mark the end of the used region. -/
theorem encSym_ne_blank (s : Γw) :
    (encSym s).1 ≠ Γ.blank ∧ (encSym s).2 ≠ Γ.blank := by
  cases s <;> exact ⟨by decide, by decide⟩

/-- An encoded code cell is never `▷` either, so the global `▷` at cell 0 stays
    unique within the work tape. -/
theorem encSym_ne_start (s : Γw) :
    (encSym s).1 ≠ Γ.start ∧ (encSym s).2 ≠ Γ.start := by
  cases s <;> exact ⟨by decide, by decide⟩

/-! ## Block layout

Position-major: super-position `p ≥ 1` occupies a block of `blockWidth k = 3*k`
cells starting at `blockStart k p = 1 + (p-1)*3k`. Within a block, tape `j`
uses offsets `3j, 3j+1` (symbol code) and `3j+2` (head-present bit). Cell 0 is
the global `▷`. -/

/-- Cells per super-position block: 2 symbol cells + 1 head bit, per tape. -/
def blockWidth (k : ℕ) : ℕ := 3 * k

/-- First cell of the block for super-position `p ≥ 1`. -/
def blockStart (k p : ℕ) : ℕ := 1 + (p - 1) * blockWidth k

@[simp] theorem blockStart_one (k : ℕ) : blockStart k 1 = 1 := by
  simp [blockStart]

/-- Consecutive blocks are exactly `blockWidth k` apart. -/
theorem blockStart_succ (k p : ℕ) (hp : 1 ≤ p) :
    blockStart k (p + 1) = blockStart k p + blockWidth k := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  show 1 + ((1 + q + 1) - 1) * blockWidth k
      = 1 + ((1 + q) - 1) * blockWidth k + blockWidth k
  have e1 : (1 + q + 1) - 1 = q + 1 := by omega
  have e2 : (1 + q) - 1 = q := by omega
  rw [e1, e2, Nat.add_mul, one_mul]
  omega

/-- Blocks start at or after cell 1 (never the `▷` cell 0). -/
theorem one_le_blockStart (k p : ℕ) : 1 ≤ blockStart k p := by
  simp only [blockStart]; omega

/-- For positive width, block starts are strictly increasing in the position. -/
theorem blockStart_lt_blockStart {k : ℕ} (hk : 1 ≤ k) {p q : ℕ}
    (hp : 1 ≤ p) (hpq : p < q) : blockStart k p < blockStart k q := by
  simp only [blockStart]
  have hbw : 1 ≤ blockWidth k := by simp only [blockWidth]; omega
  have hlt : (p - 1) + 1 ≤ q - 1 := by omega
  have hmono : ((p - 1) + 1) * blockWidth k ≤ (q - 1) * blockWidth k :=
    Nat.mul_le_mul hlt (le_refl _)
  rw [Nat.add_mul, one_mul] at hmono
  omega

/-- The cell holding tape `j`'s head-present bit within block `p`. -/
def headBitCell (k p : ℕ) (j : Fin k) : ℕ := blockStart k p + 3 * j.val + 2

/-- The first (high) symbol cell of tape `j` within block `p`. -/
def symCell (k p : ℕ) (j : Fin k) : ℕ := blockStart k p + 3 * j.val

/-- Within a block, tape `j`'s three cells stay inside `[blockStart, blockStart+3k)`. -/
theorem headBitCell_lt_next (k p : ℕ) (j : Fin k) (hp : 1 ≤ p) :
    headBitCell k p j < blockStart k (p + 1) := by
  rw [blockStart_succ k p hp]
  have hj : j.val < k := j.isLt
  simp only [headBitCell, blockWidth]
  omega

end NTM.SingleTape
