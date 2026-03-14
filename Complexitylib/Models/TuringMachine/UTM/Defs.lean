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

/-- Encode a single transition entry (the output of δ).
    Format: q' (one-hot, k bits) ++ wWrites (2n bits) ++ oWrite (2 bits)
            ++ iDir (2 bits) ++ wDirs (2n bits) ++ oDir (2 bits).
    Total width: k + 4n + 6 bits. -/
def encodeEntry (k n : ℕ) (q' : Fin k) (wW : Fin n → Γw) (oW : Γw)
    (iD : Dir3) (wD : Fin n → Dir3) (oD : Dir3) : List Bool :=
  (List.finRange k).map (fun i => i == q') ++
  (List.finRange n).flatMap (fun i => (wW i).encode) ++
  oW.encode ++ iD.encode ++
  (List.finRange n).flatMap (fun i => (wD i).encode) ++
  oD.encode

/-- Encode the full transition table for a normalized TM.
    Enumerates all input tuples `(q, iHead, wHeads, oHead)` in canonical order
    and encodes the δ output for each. -/
noncomputable def encodeTransTable {n : ℕ} (tm : TM n)
    (e : tm.Q ≃ Fin (Fintype.card tm.Q)) : List Bool :=
  let k := Fintype.card tm.Q
  (List.finRange k).flatMap fun q =>
    allΓ.flatMap fun iH =>
      (allΓFuncs n).flatMap fun wH =>
        allΓ.flatMap fun oH =>
          let (q', wW, oW, iD, wD, oD) := tm.δ (e.symm q) iH wH oH
          encodeEntry k n (e q') wW oW iD wD oD

/-- Full TM encoding: header + transition table.
    Header: k in unary (k ones) ++ [false] ++ n in unary (n ones) ++ [false]
    Body: transition table entries in canonical order. -/
noncomputable def encodeTM {n : ℕ} (tm : TM n) : List Bool :=
  let k := @Fintype.card tm.Q tm.finQ
  List.replicate k true ++ [false] ++
  List.replicate n true ++ [false] ++
  encodeTransTable tm tm.stateEquiv

end TMEncoding
