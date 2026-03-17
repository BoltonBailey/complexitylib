import Complexitylib.Models.TuringMachine

/-!
# UTM Foundation: State Normalization

This file provides state normalization for Turing machines, converting any
`TM n` with finite state type `Q` to use states `Fin (Fintype.card Q)`.

## Main definitions

- `TM.normalize` — convert any `TM n` to use states `Fin (Fintype.card Q)`
- `TM.normalizeCfg` — embed a config into the normalized state space
- `TM.normalize_step_comm` — stepping commutes with normalization
- `TM.normalize_decidesInTime` — behavioral equivalence

## Design

Normalization is needed because the UTM must decode an arbitrary TM from its
binary description. By normalizing states to `Fin k`, we can represent states
as binary numbers of known width.
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- State normalization
-- ════════════════════════════════════════════════════════════════════════

/-- The canonical equivalence between a TM's states and `Fin k`. -/
noncomputable def stateEquiv (tm : TM n) : tm.Q ≃ Fin (Fintype.card tm.Q) :=
  @Fintype.equivFin tm.Q tm.finQ

/-- Normalize a TM's state type to `Fin (Fintype.card Q)` via the canonical
    equivalence. This preserves all computational behavior.
    Noncomputable because `Fintype.equivFin` uses choice. -/
noncomputable def normalize (tm : TM n) : TM n where
  Q := Fin (@Fintype.card tm.Q tm.finQ)
  qstart := tm.stateEquiv tm.qstart
  qhalt := tm.stateEquiv tm.qhalt
  δ := fun q iHead wHeads oHead =>
    let (q', wW, oW, iD, wD, oD) := tm.δ (tm.stateEquiv.symm q) iHead wHeads oHead
    (tm.stateEquiv q', wW, oW, iD, wD, oD)
  δ_right_of_start := fun q iHead wHeads oHead =>
    tm.δ_right_of_start (tm.stateEquiv.symm q) iHead wHeads oHead

/-- Configuration embedding: map a config with original states to normalized states. -/
noncomputable def normalizeCfg (tm : TM n) (c : Cfg n tm.Q) : Cfg n (tm.normalize.Q) where
  state := tm.stateEquiv c.state
  input := c.input
  work := c.work
  output := c.output

/-- Stepping the normalized TM commutes with the state equivalence. -/
theorem normalize_step_comm (tm : TM n) (c : Cfg n tm.Q) :
    tm.normalize.step (tm.normalizeCfg c) =
      (tm.step c).map tm.normalizeCfg := by
  simp only [step, normalize, normalizeCfg]
  by_cases h : c.state = tm.qhalt
  · simp [h, stateEquiv]
  · have hne : tm.stateEquiv c.state ≠ tm.stateEquiv tm.qhalt := by
      intro heq; exact h (tm.stateEquiv.injective heq)
    simp only [h, hne, ↓reduceIte, Option.map, Equiv.symm_apply_apply, normalizeCfg]

/-- Multi-step simulation: normalized TM mirrors original TM. -/
theorem normalize_reachesIn (tm : TM n) {t : ℕ} {c c' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') :
    tm.normalize.reachesIn t (tm.normalizeCfg c) (tm.normalizeCfg c') := by
  induction h with
  | zero => exact .zero
  | step hstep _ ih =>
    exact .step (by rw [normalize_step_comm, hstep]; rfl) ih

/-- Halting is preserved by normalization. -/
theorem normalize_halted (tm : TM n) (c : Cfg n tm.Q) :
    tm.normalize.halted (tm.normalizeCfg c) ↔ tm.halted c := by
  simp only [halted, Cfg.isHalted, normalizeCfg, normalize, stateEquiv]
  constructor
  · intro h; exact tm.stateEquiv.injective h
  · intro h; rw [h]

/-- Output is preserved by normalization. -/
theorem normalize_output (tm : TM n) (c : Cfg n tm.Q) :
    (tm.normalizeCfg c).output = c.output := rfl

/-- The initial config normalizes correctly. -/
theorem normalize_initCfg (tm : TM n) (x : List Bool) :
    tm.normalizeCfg (tm.initCfg x) = tm.normalize.initCfg x := by
  simp [normalizeCfg, initCfg, Cfg.init, normalize]

/-- Normalized TM decides the same language in the same time. -/
theorem normalize_decidesInTime (tm : TM n) {L : Language} {T : ℕ → ℕ}
    (h : tm.DecidesInTime L T) :
    tm.normalize.DecidesInTime L T := by
  intro x
  obtain ⟨c', t, ht, hreach, hhalt, hmem, hnmem⟩ := h x
  refine ⟨tm.normalizeCfg c', t, ht, ?_, ?_, ?_, ?_⟩
  · rw [← normalize_initCfg]; exact normalize_reachesIn tm hreach
  · rwa [normalize_halted]
  · intro hx; rw [normalize_output]; exact hmem hx
  · intro hx; rw [normalize_output]; exact hnmem hx

end TM

-- ════════════════════════════════════════════════════════════════════════
-- Binary encoding primitives
-- ════════════════════════════════════════════════════════════════════════

/-- Encode a tape symbol as 2 bits: 0→00, 1→01, □→10, ▷→11. -/
def Γ.encode : Γ → List Bool
  | .zero  => [false, false]
  | .one   => [false, true]
  | .blank => [true, false]
  | .start => [true, true]

/-- Decode 2 bits back to a tape symbol. -/
def Γ.decode : List Bool → Option Γ
  | [false, false] => some .zero
  | [false, true]  => some .one
  | [true, false]  => some .blank
  | [true, true]   => some .start
  | _              => none

/-- Encode a write symbol as 2 bits: 0→00, 1→01, □→10. -/
def Γw.encode : Γw → List Bool
  | .zero  => [false, false]
  | .one   => [false, true]
  | .blank => [true, false]

/-- Encode a direction as 2 bits: L→00, R→01, S→10. -/
def Dir3.encode : Dir3 → List Bool
  | .left  => [false, false]
  | .right => [false, true]
  | .stay  => [true, false]

theorem Γ.encode_length (g : Γ) : g.encode.length = 2 := by cases g <;> rfl
theorem Γw.encode_length (g : Γw) : g.encode.length = 2 := by cases g <;> rfl
theorem Dir3.encode_length (d : Dir3) : d.encode.length = 2 := by cases d <;> rfl

/-- Roundtrip: decode ∘ encode = some. -/
theorem Γ.decode_encode (g : Γ) : Γ.decode (Γ.encode g) = some g := by
  cases g <;> rfl

/-- Γ encoding is injective. -/
theorem Γ.encode_injective : Function.Injective Γ.encode := by
  intro a b h; cases a <;> cases b <;> simp_all [Γ.encode]

-- ════════════════════════════════════════════════════════════════════════
-- Fixed-width binary encoding of natural numbers
-- ════════════════════════════════════════════════════════════════════════

/-- Encode a natural number as a big-endian binary list of exactly `w` bits.
    Numbers larger than `2^w - 1` are truncated (mod 2^w). -/
def Nat.toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, val => (val / 2 ^ w % 2 == 1) :: Nat.toBits w val

theorem Nat.toBits_length : ∀ (w val : ℕ), (Nat.toBits w val).length = w
  | 0, _ => rfl
  | w + 1, val => by simp [Nat.toBits, Nat.toBits_length w]

/-- Decode a big-endian binary list to a natural number. -/
def Nat.fromBits : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) * 2 ^ rest.length + Nat.fromBits rest

-- ════════════════════════════════════════════════════════════════════════
-- Enumeration of all Fin n → Γ functions
-- ════════════════════════════════════════════════════════════════════════

/-- All 4 tape symbols in canonical order. -/
def allΓ : List Γ := [.zero, .one, .blank, .start]

/-- Enumerate all functions `Fin n → Γ` in canonical (lexicographic) order. -/
def allΓFuncs : (n : ℕ) → List (Fin n → Γ)
  | 0 => [Fin.elim0]
  | n + 1 => (allΓFuncs n).flatMap fun f =>
      allΓ.map fun g =>
        fun i : Fin (n + 1) =>
          if h : i.val < n then f ⟨i.val, h⟩ else g

-- ════════════════════════════════════════════════════════════════════════
-- Full TM encoding
-- ════════════════════════════════════════════════════════════════════════

namespace TMEncoding

/-- Encode a single self-describing transition entry: includes both the input
    pattern (for matching) and the output (for applying the transition).

    Format:
    - Input pattern: q (one-hot, k bits) ++ iHead (2b) ++ wHeads (2n bits) ++ oHead (2b)
    - Separator: [false] (1 bit)
    - Output: q' (one-hot, k bits) ++ wWrites (2n bits) ++ oWrite (2b)
              ++ iDir (2b) ++ wDirs (2n bits) ++ oDir (2b)

    Total width per entry: 2k + 4n + 4 + 1 + k + 4n + 6 = 3k + 8n + 11 bits.

    The input pattern enables linear-scan lookup: the UTM can compare the
    current (state, symbols) against each entry's prefix without needing
    index arithmetic. -/
def encodeEntry (k n : ℕ) (q : Fin k) (iH : Γ) (wH : Fin n → Γ) (oH : Γ)
    (q' : Fin k) (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3) : List Bool :=
  -- Input pattern
  (List.finRange k).map (fun i => i == q) ++
  iH.encode ++
  (List.finRange n).flatMap (fun i => (wH i).encode) ++
  oH.encode ++
  -- Separator
  [false] ++
  -- Output
  (List.finRange k).map (fun i => i == q') ++
  (List.finRange n).flatMap (fun i => (wW i).encode) ++
  oW.encode ++ iD.encode ++
  (List.finRange n).flatMap (fun i => (wD i).encode) ++
  oD.encode

/-- Encode just the input pattern portion of a self-describing entry:
    q (one-hot, k bits) ++ iHead (2b) ++ wHeads (2n bits) ++ oHead (2b). -/
def encodeInputPattern (k n : ℕ) (q : Fin k) (iH : Γ) (wH : Fin n → Γ) (oH : Γ) : List Bool :=
  (List.finRange k).map (fun i => i == q) ++
  iH.encode ++
  (List.finRange n).flatMap (fun i => (wH i).encode) ++
  oH.encode

/-- Encode just the transition output portion of a self-describing entry:
    q' (one-hot, k bits) ++ wWrites (2n bits) ++ oWrite (2b)
    ++ iDir (2b) ++ wDirs (2n bits) ++ oDir (2b). -/
def encodeTransOutput (k n : ℕ) (q' : Fin k) (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3) : List Bool :=
  (List.finRange k).map (fun i => i == q') ++
  (List.finRange n).flatMap (fun i => (wW i).encode) ++
  oW.encode ++ iD.encode ++
  (List.finRange n).flatMap (fun i => (wD i).encode) ++
  oD.encode

/-- Width of the input pattern portion of a self-describing entry. -/
def inputPatternWidth (k n : ℕ) : ℕ := k + 2 + 2 * n + 2

/-- Width of the output portion of a self-describing entry. -/
def outputWidth (k n : ℕ) : ℕ := k + 2 * n + 2 + 2 + 2 * n + 2

/-- Total width of one self-describing entry (input + separator + output). -/
def entryWidth (k n : ℕ) : ℕ := inputPatternWidth k n + 1 + outputWidth k n

/-- Encode the full transition table using self-describing entries.
    Each entry includes its input pattern for linear-scan lookup. -/
noncomputable def encodeTransTable {n : ℕ} (tm : TM n)
    (e : tm.Q ≃ Fin (Fintype.card tm.Q)) : List Bool :=
  let k := Fintype.card tm.Q
  (List.finRange k).flatMap fun q =>
    allΓ.flatMap fun iH =>
      (allΓFuncs n).flatMap fun wH =>
        allΓ.flatMap fun oH =>
          let (q', wW, oW, iD, wD, oD) := tm.δ (e.symm q) iH wH oH
          encodeEntry k n q iH wH oH (e q') wW oW iD wD oD

/-- Encode a state as a one-hot pattern (k bits).
    Bit i is true iff i = e(q). -/
noncomputable def encodeStateOneHot {n : ℕ} (tm : TM n)
    (e : tm.Q ≃ Fin (Fintype.card tm.Q)) (q : tm.Q) : List Bool :=
  let k := Fintype.card tm.Q
  (List.finRange k).map (fun i => i == e q)

/-- Full TM encoding with self-describing entries.
    Header:
    - k ones + [false]                  (number of states in unary)
    - n ones + [false]                  (number of work tapes in unary)
    - qhalt one-hot (k bits) + [false]  (halt state position)
    - qstart one-hot (k bits) + [false] (start state position)
    Body: self-describing transition table entries in canonical order. -/
noncomputable def encodeTM {n : ℕ} (tm : TM n) : List Bool :=
  let k := @Fintype.card tm.Q tm.finQ
  let e := tm.stateEquiv
  List.replicate k true ++ [false] ++
  List.replicate n true ++ [false] ++
  encodeStateOneHot tm e tm.qhalt ++ [false] ++
  encodeStateOneHot tm e tm.qstart ++ [false] ++
  encodeTransTable tm e

/-- Offset in the description where the qhalt one-hot starts (0-indexed into bits). -/
def qhaltOffset (k n : ℕ) : ℕ := k + 1 + n + 1

/-- Offset where the qstart one-hot starts. -/
def qstartOffset (k n : ℕ) : ℕ := qhaltOffset k n + k + 1

/-- Offset where the transition table starts. -/
def tableOffset (k n : ℕ) : ℕ := qstartOffset k n + k + 1

/-- Length of the description for a normalized TM with k states and n work tapes. -/
noncomputable def descLen {n : ℕ} (tm : TM n) : ℕ :=
  (encodeTM tm).length

end TMEncoding

-- ════════════════════════════════════════════════════════════════════════
-- UTM input encoding
-- ════════════════════════════════════════════════════════════════════════

/-- Encode the UTM's input as a `List Γ`: TM description bits (mapped through
    `Γ.ofBool`), then a `Γ.blank` separator, then the input x (also mapped
    through `Γ.ofBool`).

    The description and x both use only `Γ.zero` and `Γ.one`, so the `Γ.blank`
    separator is unambiguous. The `copyInputToWorkTM` machine (which copies
    input until reading `Γ.blank`) naturally stops at the separator, giving us
    a clean split between desc and x on the work tapes.

    Input tape layout (via `initTape`):
    ```
    cell 0: ▷
    cells 1..descLen: desc[0] .. desc[L-1]  (Γ.ofBool)
    cell descLen+1: Γ.blank                 (separator)
    cells descLen+2..descLen+1+|x|: x[0] .. x[|x|-1]  (Γ.ofBool)
    cells descLen+2+|x|..: Γ.blank          (initTape default)
    ``` -/
noncomputable def encodeUTMInput {n : ℕ} (tm : TM n) (x : List Bool) : List Γ :=
  (TMEncoding.encodeTM tm).map Γ.ofBool ++ [Γ.blank] ++ x.map Γ.ofBool

-- ════════════════════════════════════════════════════════════════════════
-- Super-cell encoding definitions (for simulation tape)
-- ════════════════════════════════════════════════════════════════════════

namespace SuperCell

/-- Width of a super-cell: 3 cells per simulated tape (1 head marker + 2 symbol bits).
    The simulated machine has n work tapes + 1 input tape + 1 output tape = n + 2 tapes. -/
def width (numTapes : ℕ) : ℕ := 3 * numTapes

/-- Total number of simulated tapes: n work tapes + input + output. -/
def totalTapes (n : ℕ) : ℕ := n + 2

/-- Encode a Γ symbol as two cells (high bit, low bit) on the simulation tape.

    Design: `Γ.blank` maps to `(Γ.blank, Γ.blank)` so that uninitialized UTM
    sim tape cells (which default to `Γ.blank`) automatically represent
    "blank content". This enables `superCellsCorrect` to quantify over all
    positions without requiring the init machine to write infinitely many cells. -/
def symToCellPair (g : Γ) : Γ × Γ :=
  match g with
  | .zero  => (.zero, .zero)
  | .one   => (.zero, .one)
  | .blank => (.blank, .blank)
  | .start => (.one, .one)

/-- Decode two cells back to a Γ symbol. -/
def cellPairToSym : Γ → Γ → Option Γ
  | .zero, .zero   => some .zero
  | .zero, .one    => some .one
  | .blank, .blank => some .blank
  | .one, .one     => some .start
  | _, _           => none

/-- The base position on the simulation tape for position `pos` of simulated tape `tapeIdx`,
    given `numTapes` total simulated tapes.
    Each simulated position maps to a super-cell of width `3 * numTapes`.
    Within a super-cell, tape `tapeIdx` occupies offsets `3 * tapeIdx`, `3 * tapeIdx + 1`,
    `3 * tapeIdx + 2` (head marker, sym_hi, sym_lo). -/
def simTapeOffset (numTapes : ℕ) (pos : ℕ) (tapeIdx : ℕ) : ℕ :=
  1 + pos * width numTapes + 3 * tapeIdx

end SuperCell
