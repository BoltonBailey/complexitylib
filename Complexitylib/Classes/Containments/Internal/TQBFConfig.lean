/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFSavitchRec
public import Complexitylib.Classes.Containments.Internal.ConfigCount
public import Complexitylib.Circuits.Unrolling.Transition

/-!
# A machine's configuration space as `SavitchData`

⚠️ Unreviewed by Bolton

The unrolling layout of `Complexitylib.Circuits.Unrolling` puts a configuration's one-hot atoms in
a contiguous block of `configWidth tm T` wires, and `nextFormula` is one step of the machine as a
Boolean formula over such a block and a choice wire. This file reads that layout as a block of a
quantified formula: `cfgValidF` says a block is the one-hot encoding of a configuration that is
*windowed* for the input `x` and stays within space `S` — so the block determines the
configuration outright (`blockInj`) — `cfgBaseF` says one block is the other or its successor, and
`cfgAccF` says a block is halted and accepting. Together they are a `SavitchData` for the machine.

## Main definitions

- `EncBlock`, `CfgValid`, `CfgBase`, `CfgAcc` — the abstract predicates on blocks
- `headBound`, `fixedSym`, `allowedHeads`, `allowedSyms` — what a windowed block may hold
- `cfgValidF`, `cfgBaseF`, `cfgAccF` — the formulas
- `cfgSavitchData` — the packaged `SavitchData`

## Main results

- `cfgValidF_eval`, `cfgBaseF_eval`, `cfgAccF_eval`
- `blockInj` — the block determines a windowed, space-bounded configuration
-/

@[expose] public section

namespace Complexity

open QBF CircuitUnrolling

variable {k : ℕ} (tm : NTM k) (T : ℕ)

/-! ## Blocks as configurations -/

/-- The bit of a block carrying an atom. -/
noncomputable def blockAtom (u : Fin (configWidth tm T) → Bool) (atom : ConfigAtom tm T) : Bool :=
  u ⟨configIndex tm T atom, configIndex_lt tm T atom⟩

theorem blockAtom_blockOf (α : ℕ → Bool) (off : ℕ) (atom : ConfigAtom tm T) :
    blockAtom tm T (blockOf (configWidth tm T) α off) atom = α (configWire tm T off atom) := rfl

/-- Distinct atoms occupy distinct wires. -/
theorem configWire_inj (off : ℕ) {a b : ConfigAtom tm T}
    (h : configWire tm T off a = configWire tm T off b) : a = b := by
  rw [configWire, configWire] at h
  have h' : configIndex tm T a = configIndex tm T b := Nat.add_left_cancel h
  rw [← configAtomEquiv_apply_val, ← configAtomEquiv_apply_val] at h'
  exact (configAtomEquiv tm T).injective (Fin.ext h')

theorem wire_mem_block (off : ℕ) (i : ℕ) (atom : ConfigAtom tm T)
    (h : i = configWire tm T off atom) : off ≤ i ∧ i < off + configWidth tm T := by
  subst h
  have := configIndex_lt tm T atom
  rw [configWire]
  omega

/-- A block is the one-hot encoding of a configuration. -/
def EncBlock (u : Fin (configWidth tm T) → Bool) (c : Cfg k tm.Q) : Prop :=
  ∀ atom, blockAtom tm T u atom = atom.value c

/-- The largest position a tape's head may occupy in space `S` on input length `n`. -/
def headBound (n S : ℕ) : TapeSlot k → ℕ
  | .input => n + S + 1
  | .work _ => S
  | .output => S + 1

/-- The symbol a windowed configuration must hold outside its writable window, if any. -/
def fixedSym (x : List Bool) (S : ℕ) : TapeSlot k → ℕ → Option Γ
  | .input, p => some ((Tape.init (x.map Γ.ofBool)).cells p)
  | .work _, p => if S < p then some Γ.blank else none
  | .output, p => if S + 1 < p then some Γ.blank else none

/-- A block encodes a configuration that is windowed for `x` and stays within space `S`. -/
def CfgValid (x : List Bool) (S : ℕ) (u : Fin (configWidth tm T) → Bool) : Prop :=
  ∃ c, EncBlock tm T u c ∧ Windowed x S c ∧ c.WithinDecisionSpace x.length S

/-- One block is the other, or the configuration it reaches on the scratch bit's choice. -/
def CfgBase (x : List Bool) (S : ℕ) (u v : Fin (configWidth tm T) → Bool)
    (σ : Fin 1 → Bool) : Prop :=
  ∃ c, EncBlock tm T u c ∧ Windowed x S c ∧ c.WithinDecisionSpace x.length S ∧
    (v = u ∨ EncBlock tm T v (choiceStep tm (σ 0) c))

/-- The block is halted with a `1` in output cell one. -/
noncomputable def CfgAcc (u : Fin (configWidth tm T) → Bool) : Prop :=
  blockAtom tm T u (.state tm.qhalt) = true ∧
    blockAtom tm T u (.cell .output ⟨1, by omega⟩ Γ.one) = true

/-- A space-bounded configuration has all heads below a large enough horizon. -/
theorem headsLt_of_within {x : List Bool} {S : ℕ} {c : Cfg k tm.Q}
    (hs : c.WithinDecisionSpace x.length S) (hT : x.length + S + 1 < T) : HeadsLt T c := by
  intro tape
  cases tape with
  | input =>
      show c.input.head < T
      have := hs.1.2
      omega
  | work i =>
      show (c.work i).head < T
      have := hs.1.1 i
      omega
  | output =>
      show c.output.head < T
      have := hs.2
      omega

/-! ## The formulas -/

/-- Every named tape, as a list. -/
noncomputable def tapeList (k : ℕ) : List (TapeSlot k) :=
  (List.finRange (k + 2)).map (tapeSlotEquiv k).symm

theorem mem_tapeList (tape : TapeSlot k) : tape ∈ tapeList k := by
  rw [tapeList, List.mem_map]
  exact ⟨tapeSlotEquiv k tape, List.mem_finRange _, (tapeSlotEquiv k).symm_apply_apply tape⟩

/-- The head positions a tape may occupy. -/
def allowedHeads (n S : ℕ) (tape : TapeSlot k) : List (Fin (T + 1)) :=
  (List.finRange (T + 1)).filter fun p => decide (p.val ≤ headBound n S tape)

theorem mem_allowedHeads (n S : ℕ) (tape : TapeSlot k) (p : Fin (T + 1)) :
    p ∈ allowedHeads T n S tape ↔ p.val ≤ headBound n S tape := by
  rw [allowedHeads, List.mem_filter]
  simp

/-- Every symbol, ordered by its index. -/
def symbolList : List Γ := [Γ.zero, Γ.one, Γ.blank, Γ.start]

theorem mem_symbolList (s : Γ) : s ∈ symbolList := by
  cases s <;> simp [symbolList]

theorem symbolList_length : symbolList.length = 4 := rfl

theorem symbolIndex_symbolList (j : ℕ) (hj : j < 4) :
    (symbolIndex (symbolList[j]'(by rw [symbolList_length]; exact hj))).val = j := by
  interval_cases j <;> rfl

/-- The symbols a cell may hold. -/
noncomputable def allowedSyms (x : List Bool) (S : ℕ) (tape : TapeSlot k) (p : Fin (T + 2)) :
    List Γ :=
  (fixedSym x S tape p.val).elim symbolList fun s => [s]

theorem mem_allowedSyms (x : List Bool) (S : ℕ) (tape : TapeSlot k) (p : Fin (T + 2)) (s : Γ) :
    s ∈ allowedSyms T x S tape p ↔ ∀ s', fixedSym x S tape p.val = some s' → s = s' := by
  rw [allowedSyms]
  cases h : fixedSym x S tape p.val with
  | none =>
      simp only [Option.elim_none]
      exact ⟨fun _ s' hs' => absurd hs' (by simp), fun _ => mem_symbolList s⟩
  | some s' => simp

/-- The one-hot group of the state atoms. -/
noncomputable def stateGroupF (off : ℕ) : QBF :=
  oneHotCNF (fun q : tm.Q => configWire tm T off (.state q))
    (Finset.univ : Finset tm.Q).toList (Finset.univ : Finset tm.Q).toList

/-- The one-hot group of a tape's head atoms, restricted to the space bound. -/
noncomputable def headGroupF (n S off : ℕ) (tape : TapeSlot k) : QBF :=
  oneHotCNF (fun p : Fin (T + 1) => configWire tm T off (.head tape p)) (List.finRange (T + 1))
    (allowedHeads T n S tape)

/-- The one-hot group of a cell's symbol atoms, restricted to the window. -/
noncomputable def cellGroupF (x : List Bool) (S off : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) : QBF :=
  oneHotCNF (fun s : Γ => configWire tm T off (.cell tape pos s))
    (Finset.univ : Finset Γ).toList (allowedSyms T x S tape pos)

/-- **A block is a windowed, space-bounded configuration.** -/
noncomputable def cfgValidF (x : List Bool) (S off : ℕ) : QBF :=
  andList (stateGroupF tm T off ::
    (tapeList k).flatMap fun tape =>
      headGroupF tm T x.length S off tape ::
        (List.finRange (T + 2)).map (cellGroupF tm T x S off tape))

/-- **The block is halted and accepting.** -/
noncomputable def cfgAccF (off : ℕ) : QBF :=
  conj (var (configWire tm T off (.state tm.qhalt)))
    (var (configWire tm T off (.cell .output ⟨1, by omega⟩ Γ.one)))

/-- `x ↔ ψ`. -/
def iffQ (x ψ : QBF) : QBF := disj (conj x ψ) (conj (neg x) (neg ψ))

theorem eval_iffQ (α : ℕ → Bool) (x ψ : QBF) :
    eval α (iffQ x ψ) = (eval α x == eval α ψ) := by
  simp only [iffQ, eval_disj, eval_conj, eval_neg]
  cases eval α x <;> cases eval α ψ <;> rfl

theorem quantifierFree_iffQ {x ψ : QBF} (hx : QuantifierFree x) (hψ : QuantifierFree ψ) :
    QuantifierFree (iffQ x ψ) := by
  simp only [QuantifierFree, quantDepth, iffQ, Nat.max_eq_zero_iff] at *
  exact ⟨⟨hx, hψ⟩, hx, hψ⟩

theorem mem_freeVars_iffQ {x ψ : QBF} (i : ℕ) (hi : i ∈ freeVars (iffQ x ψ)) :
    i ∈ freeVars x ∨ i ∈ freeVars ψ := by
  simp only [iffQ, freeVars, Finset.mem_union] at hi
  tauto

/-- **One step**: every atom of the second block is the transition's value on the first. -/
noncomputable def stepF (u v s : ℕ) : QBF :=
  andList ((Finset.univ : Finset (ConfigAtom tm T)).toList.map fun atom =>
    iffQ (var (configWire tm T v atom)) (ofBoolFormula (nextFormula tm T u s atom)))

/-- **The step relation as a formula.** -/
noncomputable def cfgBaseF (u v s : ℕ) : QBF :=
  disj (eqF (configWidth tm T) u v) (stepF tm T u v s)

/-! ## Semantics of acceptance and the step -/

theorem cfgAccF_eval (α : ℕ → Bool) (off : ℕ) :
    eval α (cfgAccF tm T off) = true ↔
      CfgAcc tm T (blockOf (configWidth tm T) α off) := by
  rw [cfgAccF, eval_conj, Bool.and_eq_true, eval_var, eval_var, CfgAcc, blockAtom_blockOf,
    blockAtom_blockOf]

theorem stepF_eval (α : ℕ → Bool) (u v s : ℕ) (c : Cfg k tm.Q) (hheads : HeadsLt T c)
    (hc : ∀ atom, α (configWire tm T u atom) = atom.value c) :
    (eval α (stepF tm T u v s) = true ↔
      EncBlock tm T (blockOf (configWidth tm T) α v) (choiceStep tm (α s) c)) := by
  rw [stepF, eval_andList_iff]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, eval_iffQ, eval_var, eval_ofBoolFormula,
    nextFormula_eval tm T u s _ (α s) α c rfl hc hheads, beq_iff_eq]
  rw [EncBlock]
  simp only [blockAtom_blockOf]

theorem cfgBaseF_eval (x : List Bool) (S : ℕ) (hT : x.length + S + 1 < T) (α : ℕ → Bool)
    (u v s : ℕ) (hu : CfgValid tm T x S (blockOf (configWidth tm T) α u)) :
    (eval α (cfgBaseF tm T u v s) = true ↔
      CfgBase tm T x S (blockOf (configWidth tm T) α u) (blockOf (configWidth tm T) α v)
        (blockOf 1 α s)) := by
  obtain ⟨c, hEnc, hwin, hspace⟩ := hu
  have hheads : HeadsLt T c := headsLt_of_within tm T hspace hT
  have hc : ∀ atom, α (configWire tm T u atom) = atom.value c := fun atom => by
    have := hEnc atom
    rwa [blockAtom_blockOf] at this
  have hs : blockOf 1 α s 0 = α s := by rw [blockOf]; simp
  rw [cfgBaseF, eval_disj, Bool.or_eq_true, eval_eqF_iff]
  simp only [CfgBase, hs]
  constructor
  · rintro (h | h)
    · exact ⟨c, hEnc, hwin, hspace, Or.inl h.symm⟩
    · rw [stepF_eval tm T α u v s c hheads hc] at h
      exact ⟨c, hEnc, hwin, hspace, Or.inr h⟩
  · rintro ⟨c', hEnc', hwin', hspace', h | h⟩
    · exact Or.inl h.symm
    · right
      have hc' : ∀ atom, α (configWire tm T u atom) = atom.value c' := fun atom => by
        have := hEnc' atom
        rwa [blockAtom_blockOf] at this
      rw [stepF_eval tm T α u v s c' (headsLt_of_within tm T hspace' hT) hc']
      exact h

/-! ## The groups -/

theorem head_le_bound {x : List Bool} {S : ℕ} {c : Cfg k tm.Q}
    (hs : c.WithinDecisionSpace x.length S) (tape : TapeSlot k) :
    (tape.get c).head ≤ headBound x.length S tape := by
  cases tape with
  | input => exact hs.1.2
  | work i => exact hs.1.1 i
  | output => exact hs.2

theorem headBound_le (n S : ℕ) (tape : TapeSlot k) : headBound n S tape ≤ n + S + 1 := by
  cases tape <;> simp only [headBound] <;> omega

theorem stateGroupF_eval (α : ℕ → Bool) (off : ℕ) :
    eval α (stateGroupF tm T off) = true ↔
      ∃ q₀ : tm.Q, ∀ q, α (configWire tm T off (.state q)) = decide (q = q₀) := by
  rw [stateGroupF, eval_oneHotCNF_inj_iff _ _ _ (fun a ha => ha) (fun a _ b _ h => by
    have := configWire_inj tm T off h
    exact ConfigAtom.state.inj this)]
  simp only [Finset.mem_toList, Finset.mem_univ, true_and, forall_const]

theorem headGroupF_eval (α : ℕ → Bool) (n S off : ℕ) (tape : TapeSlot k) :
    eval α (headGroupF tm T n S off tape) = true ↔
      ∃ p₀ : Fin (T + 1), p₀.val ≤ headBound n S tape ∧
        ∀ p, α (configWire tm T off (.head tape p)) = decide (p = p₀) := by
  rw [headGroupF, eval_oneHotCNF_inj_iff _ _ _
    (fun a _ => List.mem_finRange a)
    (fun a _ b _ h => by
      have := configWire_inj tm T off h
      exact (ConfigAtom.head.inj this).2)]
  simp only [mem_allowedHeads, List.mem_finRange, forall_const]

theorem cellGroupF_eval (α : ℕ → Bool) (x : List Bool) (S off : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) :
    eval α (cellGroupF tm T x S off tape pos) = true ↔
      ∃ s₀ : Γ, (∀ s', fixedSym x S tape pos.val = some s' → s₀ = s') ∧
        ∀ s, α (configWire tm T off (.cell tape pos s)) = decide (s = s₀) := by
  rw [cellGroupF, eval_oneHotCNF_inj_iff _ _ _
    (fun a _ => Finset.mem_toList.mpr (Finset.mem_univ a))
    (fun a _ b _ h => by
      have := configWire_inj tm T off h
      exact (ConfigAtom.cell.inj this).2.2)]
  simp only [mem_allowedSyms, Finset.mem_toList, Finset.mem_univ, forall_const]

theorem cfgValidF_iff_groups (α : ℕ → Bool) (x : List Bool) (S off : ℕ) :
    eval α (cfgValidF tm T x S off) = true ↔
      (eval α (stateGroupF tm T off) = true ∧
        ∀ tape : TapeSlot k, eval α (headGroupF tm T x.length S off tape) = true ∧
          ∀ pos, eval α (cellGroupF tm T x S off tape pos) = true) := by
  rw [cfgValidF, eval_andList_iff]
  simp only [List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  constructor
  · intro h
    refine ⟨h _ (Or.inl rfl), fun tape => ⟨?_, fun pos => ?_⟩⟩
    · exact h _ (Or.inr ⟨tape, mem_tapeList tape, Or.inl rfl⟩)
    · exact h _ (Or.inr ⟨tape, mem_tapeList tape, Or.inr ⟨pos, rfl⟩⟩)
  · rintro ⟨h1, h2⟩ φ (rfl | ⟨tape, -, rfl | ⟨pos, rfl⟩⟩)
    · exact h1
    · exact (h2 tape).1
    · exact (h2 tape).2 pos

/-! ## Decoding a valid block -/

/-- The configuration a one-hot block denotes: the input tape is the input's, the other tapes
carry the block's symbols inside the window and blanks beyond it. -/
noncomputable def decodeCfgOf (x : List Bool) (q₀ : tm.Q) (p₀ : TapeSlot k → Fin (T + 1))
    (s₀ : TapeSlot k → Fin (T + 2) → Γ) : Cfg k tm.Q where
  state := q₀
  input := ⟨(p₀ .input).val, (Tape.init (x.map Γ.ofBool)).cells⟩
  work := fun j => ⟨(p₀ (.work j)).val,
    fun i => if h : i < T + 2 then s₀ (.work j) ⟨i, h⟩ else Γ.blank⟩
  output := ⟨(p₀ .output).val, fun i => if h : i < T + 2 then s₀ .output ⟨i, h⟩ else Γ.blank⟩

theorem head_decodeCfgOf (x : List Bool) (q₀ : tm.Q) (p₀ : TapeSlot k → Fin (T + 1))
    (s₀ : TapeSlot k → Fin (T + 2) → Γ) (tape : TapeSlot k) :
    (tape.get (decodeCfgOf tm T x q₀ p₀ s₀)).head = (p₀ tape).val := by
  cases tape <;> rfl

theorem cells_decodeCfgOf (x : List Bool) (q₀ : tm.Q) (p₀ : TapeSlot k → Fin (T + 1))
    (s₀ : TapeSlot k → Fin (T + 2) → Γ)
    (hin : ∀ pos : Fin (T + 2), s₀ .input pos = (Tape.init (x.map Γ.ofBool)).cells pos.val)
    (tape : TapeSlot k) {p : ℕ} (h : p < T + 2) :
    (tape.get (decodeCfgOf tm T x q₀ p₀ s₀)).cells p = s₀ tape ⟨p, h⟩ := by
  cases tape with
  | input => exact (hin ⟨p, h⟩).symm
  | work j =>
      show (if h' : p < T + 2 then s₀ (.work j) ⟨p, h'⟩ else Γ.blank) = _
      rw [dif_pos h]
  | output =>
      show (if h' : p < T + 2 then s₀ .output ⟨p, h'⟩ else Γ.blank) = _
      rw [dif_pos h]

theorem cells_decodeCfgOf_ge (x : List Bool) (q₀ : tm.Q) (p₀ : TapeSlot k → Fin (T + 1))
    (s₀ : TapeSlot k → Fin (T + 2) → Γ) (tape : TapeSlot k) {p : ℕ} (h : ¬ p < T + 2)
    (hne : tape ≠ .input) :
    (tape.get (decodeCfgOf tm T x q₀ p₀ s₀)).cells p = Γ.blank := by
  cases tape with
  | input => exact absurd rfl hne
  | work j =>
      show (if h' : p < T + 2 then s₀ (.work j) ⟨p, h'⟩ else Γ.blank) = _
      rw [dif_neg h]
  | output =>
      show (if h' : p < T + 2 then s₀ .output ⟨p, h'⟩ else Γ.blank) = _
      rw [dif_neg h]

/-- The one-hot data a valid block's groups carry: a state, a head within its bound for each
tape, and a symbol respecting the window for each cell. -/
def ValidGroups (x : List Bool) (S off : ℕ) (α : ℕ → Bool) : Prop :=
  (∃ q₀ : tm.Q, ∀ q, α (configWire tm T off (.state q)) = decide (q = q₀)) ∧
    ∀ tape : TapeSlot k,
      (∃ p₀ : Fin (T + 1), p₀.val ≤ headBound x.length S tape ∧
        ∀ p, α (configWire tm T off (.head tape p)) = decide (p = p₀)) ∧
      ∀ pos : Fin (T + 2), ∃ s₀ : Γ,
        (∀ s', fixedSym x S tape pos.val = some s' → s₀ = s') ∧
        ∀ s, α (configWire tm T off (.cell tape pos s)) = decide (s = s₀)

theorem validGroups_iff (x : List Bool) (S : ℕ) (hT : x.length + S + 1 ≤ T) (α : ℕ → Bool)
    (off : ℕ) :
    ValidGroups tm T x S off α ↔
      CfgValid tm T x S (blockOf (configWidth tm T) α off) := by
  constructor
  · rintro ⟨hst, hrest⟩
    obtain ⟨q₀, hq₀⟩ := hst
    have hhead : ∀ tape : TapeSlot k, ∃ p₀ : Fin (T + 1),
        p₀.val ≤ headBound x.length S tape ∧
        ∀ p, α (configWire tm T off (.head tape p)) = decide (p = p₀) := fun tape =>
      (hrest tape).1
    have hcell : ∀ (tape : TapeSlot k) (pos : Fin (T + 2)), ∃ s₀ : Γ,
        (∀ s', fixedSym x S tape pos.val = some s' → s₀ = s') ∧
        ∀ s, α (configWire tm T off (.cell tape pos s)) = decide (s = s₀) := fun tape pos =>
      (hrest tape).2 pos
    choose p₀ hp₀ hp₀' using hhead
    choose s₀ hs₀ hs₀' using hcell
    have hin : ∀ pos : Fin (T + 2),
        s₀ .input pos = (Tape.init (x.map Γ.ofBool)).cells pos.val := fun pos =>
      hs₀ .input pos _ rfl
    refine ⟨decodeCfgOf tm T x q₀ p₀ s₀, fun atom => ?_, ⟨rfl, ?_, ?_⟩, ⟨fun i => ?_, ?_⟩, ?_⟩
    · rw [blockAtom_blockOf]
      cases atom with
      | state q =>
          rw [hq₀ q]
          show _ = decide ((decodeCfgOf tm T x q₀ p₀ s₀).state = q)
          exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩
      | head tape p =>
          rw [hp₀' tape p]
          show _ = decide ((tape.get (decodeCfgOf tm T x q₀ p₀ s₀)).head = p.val)
          rw [head_decodeCfgOf]
          exact decide_eq_decide.mpr ⟨fun h => by rw [h], fun h => Fin.ext h.symm⟩
      | cell tape pos s =>
          rw [hs₀' tape pos s]
          show _ = decide ((tape.get (decodeCfgOf tm T x q₀ p₀ s₀)).cells pos.val = s)
          rw [cells_decodeCfgOf tm T x q₀ p₀ s₀ hin tape pos.isLt, Fin.eta]
          exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩
    · intro i p hp
      by_cases hlt : p < T + 2
      · rw [show (decodeCfgOf tm T x q₀ p₀ s₀).work i
            = (TapeSlot.work i).get (decodeCfgOf tm T x q₀ p₀ s₀) from rfl,
          cells_decodeCfgOf tm T x q₀ p₀ s₀ hin (.work i) hlt]
        exact hs₀ (.work i) ⟨p, hlt⟩ Γ.blank (by simp [fixedSym, hp])
      · exact cells_decodeCfgOf_ge tm T x q₀ p₀ s₀ (.work i) hlt (by simp)
    · intro p hp
      by_cases hlt : p < T + 2
      · rw [show (decodeCfgOf tm T x q₀ p₀ s₀).output
            = (TapeSlot.output).get (decodeCfgOf tm T x q₀ p₀ s₀) from rfl,
          cells_decodeCfgOf tm T x q₀ p₀ s₀ hin .output hlt]
        exact hs₀ .output ⟨p, hlt⟩ Γ.blank (by simp [fixedSym, hp])
      · exact cells_decodeCfgOf_ge tm T x q₀ p₀ s₀ .output hlt (by simp)
    · have hb := hp₀ (.work i)
      simp only [headBound] at hb
      show ((TapeSlot.work i).get (decodeCfgOf tm T x q₀ p₀ s₀)).head ≤ S
      rw [head_decodeCfgOf]
      exact hb
    · have hb := hp₀ .input
      simp only [headBound] at hb
      show ((TapeSlot.input).get (decodeCfgOf tm T x q₀ p₀ s₀)).head ≤ x.length + S + 1
      rw [head_decodeCfgOf]
      exact hb
    · have hb := hp₀ .output
      simp only [headBound] at hb
      show ((TapeSlot.output).get (decodeCfgOf tm T x q₀ p₀ s₀)).head ≤ S + 1
      rw [head_decodeCfgOf]
      exact hb
  · rintro ⟨c, hEnc, hwin, hspace⟩
    have hval : ∀ atom, α (configWire tm T off atom) = atom.value c := fun atom => by
      have := hEnc atom
      rwa [blockAtom_blockOf] at this
    refine ⟨?_, fun tape => ⟨?_, fun pos => ?_⟩⟩
    · refine ⟨c.state, fun q => ?_⟩
      rw [hval (.state q)]
      exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩
    · have hb := head_le_bound tm hspace tape
      have hb' := headBound_le (k := k) x.length S tape
      refine ⟨⟨(tape.get c).head, by omega⟩, hb, fun p => ?_⟩
      rw [hval (.head tape p)]
      exact decide_eq_decide.mpr ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
    · refine ⟨(tape.get c).cells pos.val, fun s' hs' => ?_, fun s => ?_⟩
      · cases tape with
        | input =>
            simp only [fixedSym, Option.some.injEq] at hs'
            show c.input.cells pos.val = s'
            rw [hwin.input, hs']
        | work j =>
            simp only [fixedSym] at hs'
            split_ifs at hs' with hlt
            · show (c.work j).cells pos.val = s'
              rw [hwin.work j pos.val hlt, Option.some.inj hs']
        | output =>
            simp only [fixedSym] at hs'
            split_ifs at hs' with hlt
            · show c.output.cells pos.val = s'
              rw [hwin.output pos.val hlt, Option.some.inj hs']
      · rw [hval (.cell tape pos s)]
        exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩

theorem cfgValidF_eval (x : List Bool) (S : ℕ) (hT : x.length + S + 1 ≤ T) (α : ℕ → Bool)
    (off : ℕ) :
    eval α (cfgValidF tm T x S off) = true ↔
      CfgValid tm T x S (blockOf (configWidth tm T) α off) := by
  rw [← validGroups_iff tm T x S hT α off, cfgValidF_iff_groups]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(stateGroupF_eval tm T α off).mp h1, fun tape =>
      ⟨(headGroupF_eval tm T α x.length S off tape).mp (h2 tape).1,
        fun pos => (cellGroupF_eval tm T α x S off tape pos).mp ((h2 tape).2 pos)⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(stateGroupF_eval tm T α off).mpr h1, fun tape =>
      ⟨(headGroupF_eval tm T α x.length S off tape).mpr (h2 tape).1,
        fun pos => (cellGroupF_eval tm T α x S off tape pos).mpr ((h2 tape).2 pos)⟩⟩

/-! ## Validity as a clause list -/

/-- Every state, ordered by its index, so that the wires of consecutive entries are
consecutive. -/
noncomputable def stateList (tm : NTM k) : List tm.Q :=
  (List.finRange (Fintype.card tm.Q)).map (Fintype.equivFin tm.Q).symm

theorem mem_stateList (q : tm.Q) : q ∈ stateList tm := by
  rw [stateList, List.mem_map]
  exact ⟨Fintype.equivFin tm.Q q, List.mem_finRange _,
    (Fintype.equivFin tm.Q).symm_apply_apply q⟩

theorem stateList_length : (stateList tm).length = Fintype.card tm.Q := by
  rw [stateList, List.length_map, List.length_finRange]

theorem stateIndex_stateList (j : ℕ) (hj : j < Fintype.card tm.Q) :
    stateIndex tm ((stateList tm)[j]'(by rw [stateList_length]; exact hj)) = j := by
  simp only [stateList, List.getElem_map, List.getElem_finRange, stateIndex,
    Equiv.apply_symm_apply]
  rfl

/-- The state group, as clauses. -/
noncomputable def stateGroupC (off : ℕ) : List (List CLit) :=
  oneHotClauses (fun q : tm.Q => configWire tm T off (.state q))
    (stateList tm) (stateList tm)

/-- A tape's head group, as clauses. -/
noncomputable def headGroupC (n S off : ℕ) (tape : TapeSlot k) : List (List CLit) :=
  oneHotClauses (fun p : Fin (T + 1) => configWire tm T off (.head tape p))
    (List.finRange (T + 1)) (allowedHeads T n S tape)

/-- A cell's symbol group, as clauses. -/
noncomputable def cellGroupC (x : List Bool) (S off : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) : List (List CLit) :=
  oneHotClauses (fun s : Γ => configWire tm T off (.cell tape pos s))
    symbolList (allowedSyms T x S tape pos)

/-- **A block is a windowed, space-bounded configuration** — as a clause list. -/
noncomputable def cfgValidC (x : List Bool) (S off : ℕ) : List (List CLit) :=
  stateGroupC tm T off ++ (tapeList k).flatMap fun tape =>
    headGroupC tm T x.length S off tape ++
      (List.finRange (T + 2)).flatMap fun pos => cellGroupC tm T x S off tape pos

theorem stateGroupC_eval (α : ℕ → Bool) (off : ℕ) :
    eval α (cnfQBF (stateGroupC tm T off)) = true ↔
      ∃ q₀ : tm.Q, ∀ q, α (configWire tm T off (.state q)) = decide (q = q₀) := by
  rw [stateGroupC, eval_oneHotClauses_inj_iff _ _ _ (fun a ha => ha) (fun a _ b _ h => by
    have := configWire_inj tm T off h
    exact ConfigAtom.state.inj this)]
  constructor
  · rintro ⟨q₀, -, h⟩
    exact ⟨q₀, fun q => h q (mem_stateList tm q)⟩
  · rintro ⟨q₀, h⟩
    exact ⟨q₀, mem_stateList tm q₀, fun q _ => h q⟩

theorem headGroupC_eval (α : ℕ → Bool) (n S off : ℕ) (tape : TapeSlot k) :
    eval α (cnfQBF (headGroupC tm T n S off tape)) = true ↔
      ∃ p₀ : Fin (T + 1), p₀.val ≤ headBound n S tape ∧
        ∀ p, α (configWire tm T off (.head tape p)) = decide (p = p₀) := by
  rw [headGroupC, eval_oneHotClauses_inj_iff _ _ _
    (fun a _ => List.mem_finRange a)
    (fun a _ b _ h => by
      have := configWire_inj tm T off h
      exact (ConfigAtom.head.inj this).2)]
  simp only [mem_allowedHeads, List.mem_finRange, forall_const]

theorem cellGroupC_eval (α : ℕ → Bool) (x : List Bool) (S off : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) :
    eval α (cnfQBF (cellGroupC tm T x S off tape pos)) = true ↔
      ∃ s₀ : Γ, (∀ s', fixedSym x S tape pos.val = some s' → s₀ = s') ∧
        ∀ s, α (configWire tm T off (.cell tape pos s)) = decide (s = s₀) := by
  rw [cellGroupC, eval_oneHotClauses_inj_iff _ _ _
    (fun a _ => mem_symbolList a)
    (fun a _ b _ h => by
      have := configWire_inj tm T off h
      exact (ConfigAtom.cell.inj this).2.2)]
  constructor
  · rintro ⟨s₀, hs₀, h⟩
    exact ⟨s₀, (mem_allowedSyms T x S tape pos s₀).mp hs₀, fun s => h s (mem_symbolList s)⟩
  · rintro ⟨s₀, hfix, h⟩
    exact ⟨s₀, (mem_allowedSyms T x S tape pos s₀).mpr hfix, fun s _ => h s⟩

theorem cfgValidC_eval (x : List Bool) (S : ℕ) (hT : x.length + S + 1 ≤ T) (α : ℕ → Bool)
    (off : ℕ) :
    eval α (cnfQBF (cfgValidC tm T x S off)) = true ↔
      CfgValid tm T x S (blockOf (configWidth tm T) α off) := by
  rw [← validGroups_iff tm T x S hT α off, cfgValidC, eval_cnfQBF_append,
    eval_cnfQBF_flatMap]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(stateGroupC_eval tm T α off).mp h1, fun tape => ?_⟩
    have h3 := h2 tape (mem_tapeList tape)
    rw [eval_cnfQBF_append, eval_cnfQBF_flatMap] at h3
    exact ⟨(headGroupC_eval tm T α x.length S off tape).mp h3.1, fun pos =>
      (cellGroupC_eval tm T α x S off tape pos).mp (h3.2 pos (List.mem_finRange pos))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(stateGroupC_eval tm T α off).mpr h1, fun tape _ => ?_⟩
    rw [eval_cnfQBF_append, eval_cnfQBF_flatMap]
    exact ⟨(headGroupC_eval tm T α x.length S off tape).mpr (h2 tape).1, fun pos _ =>
      (cellGroupC_eval tm T α x S off tape pos).mpr ((h2 tape).2 pos)⟩

/-- **The block is halted and accepting** — as two unit clauses. -/
noncomputable def cfgAccC (off : ℕ) : List (List CLit) :=
  [[(true, configWire tm T off (.state tm.qhalt))],
    [(true, configWire tm T off (.cell .output ⟨1, by omega⟩ Γ.one))]]

theorem cfgAccC_eval (α : ℕ → Bool) (off : ℕ) :
    eval α (cnfQBF (cfgAccC tm T off)) = true ↔
      CfgAcc tm T (blockOf (configWidth tm T) α off) := by
  rw [eval_cnfQBF_iff]
  simp only [cfgAccC, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    eval_clauseQBF_iff, exists_eq_left, eval_litQBF, beq_iff_eq]
  rw [CfgAcc, blockAtom_blockOf, blockAtom_blockOf]

theorem mem_cfgValidC_vars (x : List Bool) (S off : ℕ) :
    ∀ c ∈ cfgValidC tm T x S off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + configWidth tm T := by
  intro c hc l hl
  rw [cfgValidC, List.mem_append] at hc
  rcases hc with h | h
  · rw [stateGroupC] at h
    obtain ⟨a, -, hv⟩ := mem_oneHotClauses_vars _ _ _ (fun a ha => ha) c h l hl
    exact wire_mem_block tm T off l.2 _ hv
  · rw [List.mem_flatMap] at h
    obtain ⟨tape, -, h⟩ := h
    rw [List.mem_append] at h
    rcases h with h | h
    · rw [headGroupC] at h
      obtain ⟨a, -, hv⟩ :=
        mem_oneHotClauses_vars _ _ _ (fun a _ => List.mem_finRange a) c h l hl
      exact wire_mem_block tm T off l.2 _ hv
    · rw [List.mem_flatMap] at h
      obtain ⟨pos, -, h⟩ := h
      rw [cellGroupC] at h
      obtain ⟨a, -, hv⟩ := mem_oneHotClauses_vars _ _ _
        (fun a _ => mem_symbolList a) c h l hl
      exact wire_mem_block tm T off l.2 _ hv

theorem mem_cfgAccC_vars (off : ℕ) :
    ∀ c ∈ cfgAccC tm T off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + configWidth tm T := by
  intro c hc l hl
  rw [cfgAccC, List.mem_cons, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact wire_mem_block tm T off _ _ rfl
    · simp at hl
  · rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact wire_mem_block tm T off _ _ rfl
    · simp at hl
  · simp at hc

/-! ## Local views -/

/-- A complete local view of a block: what the machine reads, and where its heads are. -/
abbrev StepView (tm : NTM k) (T : ℕ) := TransitionCase tm × (TapeSlot k → Fin (T + 1))

/-- The literals saying the block shows this view. -/
noncomputable def viewLits (u : ℕ) (V : StepView tm T) : List CLit :=
  (true, configWire tm T u (.state V.1.state)) ::
    (tapeList k).flatMap fun t =>
      [(true, configWire tm T u (.head t (V.2 t))),
        (true, configWire tm T u (.cell t (headCellPosition (V.2 t)) (V.1.read t)))]

/-- The configuration really shows the view. -/
def ViewMatches (V : StepView tm T) (c : Cfg k tm.Q) : Prop :=
  c.state = V.1.state ∧ ∀ t : TapeSlot k,
    (t.get c).head = (V.2 t).val ∧ (t.get c).cells (V.2 t).val = V.1.read t

/-- **The view's literals say exactly that the block's configuration shows the view.** -/
theorem viewLits_iff (α : ℕ → Bool) (u : ℕ) (V : StepView tm T) (c : Cfg k tm.Q)
    (hu : ∀ atom, α (configWire tm T u atom) = atom.value c) :
    (∀ lit ∈ viewLits tm T u V, α lit.2 = lit.1) ↔ ViewMatches tm T V c := by
  have hstate : ∀ q : tm.Q, α (configWire tm T u (.state q)) = decide (c.state = q) := fun q =>
    hu (.state q)
  have hhead : ∀ (t : TapeSlot k) (p : Fin (T + 1)),
      α (configWire tm T u (.head t p)) = decide ((t.get c).head = p.val) := fun t p =>
    hu (.head t p)
  have hcell : ∀ (t : TapeSlot k) (pos : Fin (T + 2)) (sym : Γ),
      α (configWire tm T u (.cell t pos sym)) = decide ((t.get c).cells pos.val = sym) :=
    fun t pos sym => hu (.cell t pos sym)
  constructor
  · intro h
    refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
    · have := h _ (List.mem_cons_self)
      rw [hstate] at this
      exact of_decide_eq_true this
    · have := h ((true, configWire tm T u (.head t (V.2 t))) : CLit)
        (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨t, mem_tapeList t, List.mem_cons_self⟩))
      rw [hhead] at this
      exact of_decide_eq_true this
    · have := h ((true, configWire tm T u
        (.cell t (headCellPosition (V.2 t)) (V.1.read t))) : CLit)
        (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨t, mem_tapeList t, List.mem_cons_of_mem _ List.mem_cons_self⟩))
      rw [hcell] at this
      have h2 := of_decide_eq_true this
      simpa [headCellPosition] using h2
  · rintro ⟨hq, ht⟩ lit hlit
    rw [viewLits, List.mem_cons, List.mem_flatMap] at hlit
    rcases hlit with rfl | ⟨t, -, hlit⟩
    · rw [hstate, decide_eq_true hq]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hlit
      rcases hlit with rfl | rfl
      · rw [hhead, decide_eq_true (ht t).1]
      · rw [hcell]
        exact decide_eq_true (by
          have h2 := (ht t).2
          simpa [headCellPosition] using h2)

/-- **A valid block shows exactly one view.** -/
theorem exists_viewMatches (c : Cfg k tm.Q) (b : Bool) (hheads : HeadsLt T c) :
    ViewMatches tm T ((currentCase tm b c), fun t => ⟨(t.get c).head, by
      have := hheads t; omega⟩) c :=
  ⟨rfl, fun t => ⟨rfl, by cases t <;> rfl⟩⟩

/-! ## What a view determines about the next configuration -/

/-- The transition a view takes. -/
noncomputable def viewDelta (V : StepView tm T) :=
  tm.δ V.1.choice V.1.state V.1.inputRead V.1.workRead V.1.outputRead

theorem read_of_viewMatches {V : StepView tm T} {c : Cfg k tm.Q} (h : ViewMatches tm T V c)
    (t : TapeSlot k) : (t.get c).read = V.1.read t := by
  rw [Tape.read, (h.2 t).1, (h.2 t).2]

/-- **A view fixes the machine's transition.** -/
theorem delta_of_viewMatches {V : StepView tm T} {c : Cfg k tm.Q} (h : ViewMatches tm T V c) :
    tm.δ V.1.choice c.state c.input.read (fun i => (c.work i).read) c.output.read
      = viewDelta tm T V := by
  have hin : c.input.read = V.1.inputRead := read_of_viewMatches tm T h .input
  have hout : c.output.read = V.1.outputRead := read_of_viewMatches tm T h .output
  have hwk : (fun i => (c.work i).read) = V.1.workRead := by
    funext i
    exact read_of_viewMatches tm T h (.work i)
  rw [viewDelta, h.1, hin, hout, hwk]

@[simp] theorem stepCfg_state (b : Bool) (c : Cfg k tm.Q) :
    (tm.stepCfg b c).state
      = (tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read).1 := rfl

@[simp] theorem stepCfg_input (b : Bool) (c : Cfg k tm.Q) :
    (tm.stepCfg b c).input = c.input.move
      (tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.1 := rfl

@[simp] theorem stepCfg_work (b : Bool) (c : Cfg k tm.Q) (i : Fin k) :
    (tm.stepCfg b c).work i = (c.work i).writeAndMove
      ((tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read).2.1 i)
      ((tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.2.1 i) := rfl

@[simp] theorem stepCfg_output (b : Bool) (c : Cfg k tm.Q) :
    (tm.stepCfg b c).output = c.output.writeAndMove
      (tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.1
      (tm.δ b c.state c.input.read (fun i => (c.work i).read) c.output.read).2.2.2.2.2 := rfl

/-! ## The successor a view determines -/

/-- One step of the machine, halted or not. -/
theorem choiceStep_eq (b : Bool) (c : Cfg k tm.Q) :
    choiceStep tm b c = if c.state = tm.qhalt then c else tm.stepCfg b c := by
  rw [choiceStep, NTM.trace]
  split_ifs <;> rfl

theorem move_head_eq (t : Tape) (d : Dir3) : (t.move d).head = movedHeadPosition t.head d := by
  cases d <;> rfl

/-- The direction a view moves a tape's head. -/
noncomputable def viewDir (V : StepView tm T) : TapeSlot k → Dir3
  | .input => (viewDelta tm T V).2.2.2.1
  | .work i => (viewDelta tm T V).2.2.2.2.1 i
  | .output => (viewDelta tm T V).2.2.2.2.2

/-- The symbol a view leaves under a tape's head: the input tape and cell zero keep what they
hold, everything else takes the transition's write. -/
noncomputable def viewWrite (V : StepView tm T) : TapeSlot k → Γ
  | .input => V.1.inputRead
  | .work i =>
      if (V.2 (.work i)).val = 0 then V.1.workRead i else ((viewDelta tm T V).2.1 i : Γ)
  | .output =>
      if (V.2 .output).val = 0 then V.1.outputRead else ((viewDelta tm T V).2.2.1 : Γ)

variable {V : StepView tm T} {c : Cfg k tm.Q}

theorem stepCfg_state_of_view (h : ViewMatches tm T V c) :
    (tm.stepCfg V.1.choice c).state = (viewDelta tm T V).1 := by
  rw [stepCfg_state, delta_of_viewMatches tm T h]

theorem stepCfg_head_of_view (h : ViewMatches tm T V c) (t : TapeSlot k) :
    (t.get (tm.stepCfg V.1.choice c)).head
      = movedHeadPosition (V.2 t).val (viewDir tm T V t) := by
  have hδ := delta_of_viewMatches tm T h
  cases t with
  | input =>
      show ((tm.stepCfg V.1.choice c).input).head = _
      rw [stepCfg_input, move_head_eq, hδ, viewDir]
      congr 1
      exact (h.2 TapeSlot.input).1
  | work i =>
      show ((tm.stepCfg V.1.choice c).work i).head = _
      rw [stepCfg_work, Tape.writeAndMove, move_head_eq, Tape.write_head, hδ, viewDir]
      congr 1
      exact (h.2 (TapeSlot.work i)).1
  | output =>
      show ((tm.stepCfg V.1.choice c).output).head = _
      rw [stepCfg_output, Tape.writeAndMove, move_head_eq, Tape.write_head, hδ, viewDir]
      congr 1
      exact (h.2 TapeSlot.output).1

theorem stepCfg_cells_of_view (h : ViewMatches tm T V c) (t : TapeSlot k) {p : ℕ}
    (hp : p ≠ (V.2 t).val) :
    (t.get (tm.stepCfg V.1.choice c)).cells p = (t.get c).cells p := by
  have hhead : (t.get c).head = (V.2 t).val := (h.2 t).1
  cases t with
  | input =>
      show ((tm.stepCfg V.1.choice c).input).cells p = c.input.cells p
      rw [stepCfg_input, Tape.move_cells]
  | work i =>
      show ((tm.stepCfg V.1.choice c).work i).cells p = (c.work i).cells p
      rw [stepCfg_work, Tape.writeAndMove, Tape.move_cells, Tape.write]
      split_ifs with h0
      · rfl
      · have hh : (c.work i).head = (V.2 (TapeSlot.work i)).val := hhead
        show Function.update (c.work i).cells (c.work i).head _ p = _
        rw [Function.update_of_ne (by rw [hh]; exact hp)]
  | output =>
      show ((tm.stepCfg V.1.choice c).output).cells p = c.output.cells p
      rw [stepCfg_output, Tape.writeAndMove, Tape.move_cells, Tape.write]
      split_ifs with h0
      · rfl
      · have hh : c.output.head = (V.2 TapeSlot.output).val := hhead
        show Function.update c.output.cells c.output.head _ p = _
        rw [Function.update_of_ne (by rw [hh]; exact hp)]

theorem stepCfg_cells_head_of_view (h : ViewMatches tm T V c) (t : TapeSlot k) :
    (t.get (tm.stepCfg V.1.choice c)).cells (V.2 t).val = viewWrite tm T V t := by
  have hhead : (t.get c).head = (V.2 t).val := (h.2 t).1
  have hread : (t.get c).cells (V.2 t).val = V.1.read t := (h.2 t).2
  have hδ := delta_of_viewMatches tm T h
  cases t with
  | input =>
      show ((tm.stepCfg V.1.choice c).input).cells _ = _
      rw [stepCfg_input, Tape.move_cells, viewWrite]
      exact hread
  | work i =>
      show ((tm.stepCfg V.1.choice c).work i).cells _ = _
      rw [stepCfg_work, Tape.writeAndMove, Tape.move_cells, Tape.write, hδ, viewWrite]
      have hh : (c.work i).head = (V.2 (TapeSlot.work i)).val := hhead
      split_ifs with h0 h1 h1
      · exact hread
      · rw [hh] at h0
        exact absurd h0 h1
      · rw [hh] at h0
        exact absurd h1 h0
      · show Function.update (c.work i).cells (c.work i).head _ _ = _
        rw [hh, Function.update_self]
  | output =>
      show ((tm.stepCfg V.1.choice c).output).cells _ = _
      rw [stepCfg_output, Tape.writeAndMove, Tape.move_cells, Tape.write, hδ, viewWrite]
      have hh : c.output.head = (V.2 TapeSlot.output).val := hhead
      split_ifs with h0 h1 h1
      · exact hread
      · rw [hh] at h0
        exact absurd h0 h1
      · rw [hh] at h0
        exact absurd h1 h0
      · show Function.update c.output.cells c.output.head _ _ = _
        rw [hh, Function.update_self]

/-! ## What the successor's atoms are, as functions of the view -/

/-- The state the successor has. -/
noncomputable def newStateV (V : StepView tm T) : tm.Q :=
  if V.1.state = tm.qhalt then V.1.state else (viewDelta tm T V).1

/-- Where a tape's head goes. -/
noncomputable def newHeadV (V : StepView tm T) (t : TapeSlot k) : ℕ :=
  if V.1.state = tm.qhalt then (V.2 t).val
  else movedHeadPosition (V.2 t).val (viewDir tm T V t)

/-- What is left under the old head position. -/
noncomputable def newSymV (V : StepView tm T) (t : TapeSlot k) : Γ :=
  if V.1.state = tm.qhalt then V.1.read t else viewWrite tm T V t

/-- **The view determines the successor's atoms**, except for the cells it does not touch,
which keep the block's own values. -/
theorem choiceStep_of_view (h : ViewMatches tm T V c) :
    (choiceStep tm V.1.choice c).state = newStateV tm T V ∧
    (∀ t : TapeSlot k, (t.get (choiceStep tm V.1.choice c)).head = newHeadV tm T V t) ∧
    (∀ t : TapeSlot k,
      (t.get (choiceStep tm V.1.choice c)).cells (V.2 t).val = newSymV tm T V t) ∧
    (∀ (t : TapeSlot k) (p : ℕ), p ≠ (V.2 t).val →
      (t.get (choiceStep tm V.1.choice c)).cells p = (t.get c).cells p) := by
  rw [choiceStep_eq]
  by_cases hhalt : c.state = tm.qhalt
  · have hV : V.1.state = tm.qhalt := by rw [← h.1]; exact hhalt
    rw [if_pos hhalt]
    refine ⟨by rw [newStateV, if_pos hV, h.1], fun t => ?_, fun t => ?_, fun t p _ => rfl⟩
    · rw [newHeadV, if_pos hV]
      exact (h.2 t).1
    · rw [newSymV, if_pos hV]
      exact (h.2 t).2
  · have hV : ¬ V.1.state = tm.qhalt := by rw [← h.1]; exact hhalt
    rw [if_neg hhalt]
    refine ⟨?_, fun t => ?_, fun t => ?_, fun t p hp => stepCfg_cells_of_view tm T h t hp⟩
    · rw [newStateV, if_neg hV]
      exact stepCfg_state_of_view tm T h
    · rw [newHeadV, if_neg hV]
      exact stepCfg_head_of_view tm T h t
    · rw [newSymV, if_neg hV]
      exact stepCfg_cells_head_of_view tm T h t

/-! ## Forcing an atom under a view -/

/-- Negate every literal. -/
def negLits (L : List CLit) : List CLit := L.map fun l => (!l.1, l.2)

theorem eval_negLits (α : ℕ → Bool) (L : List CLit) :
    (∃ l ∈ negLits L, eval α (litQBF l) = true) ↔ ¬ ∀ l ∈ L, α l.2 = l.1 := by
  simp only [negLits, List.mem_map, exists_exists_and_eq_and, eval_litQBF, beq_iff_eq]
  constructor
  · rintro ⟨l, hl, hv⟩ hall
    rw [hall l hl] at hv
    exact (Bool.self_ne_not _) hv
  · intro h
    by_contra hc
    push Not at hc
    refine h fun l hl => ?_
    have hthis := hc l hl
    generalize hb : l.1 = b at hthis ⊢
    generalize hα : α l.2 = a at hthis ⊢
    cases a <;> cases b <;> simp_all

/-- The literals saying the block shows the view *and* the scratch bit is the view's choice. -/
noncomputable def viewCondLits (u s : ℕ) (V : StepView tm T) : List CLit :=
  (V.1.choice, s) :: viewLits tm T u V

/-- **The condition's literals hold exactly when the block shows the view on that choice.** -/
theorem viewCondLits_iff (α : ℕ → Bool) (u s : ℕ) (V : StepView tm T) (c : Cfg k tm.Q)
    (hu : ∀ atom, α (configWire tm T u atom) = atom.value c) :
    (∀ lit ∈ viewCondLits tm T u s V, α lit.2 = lit.1) ↔
      (α s = V.1.choice ∧ ViewMatches tm T V c) := by
  rw [viewCondLits]
  constructor
  · intro h
    exact ⟨h _ List.mem_cons_self,
      (viewLits_iff tm T α u V c hu).mp fun lit hlit => h lit (List.mem_cons_of_mem _ hlit)⟩
  · rintro ⟨hs, hv⟩ lit hlit
    rw [List.mem_cons] at hlit
    rcases hlit with rfl | hlit
    · exact hs
    · exact (viewLits_iff tm T α u V c hu).mpr hv lit hlit

/-- The clause forcing an atom of the new block to a value, whenever the old block shows the
view on the scratch bit's choice. -/
noncomputable def forceAtom (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T) (b : Bool) :
    List CLit := negLits (viewCondLits tm T u s V) ++ [(b, configWire tm T v a)]

theorem eval_forceAtom (α : ℕ → Bool) (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T)
    (b : Bool) :
    eval α (clauseQBF (forceAtom tm T u v s V a b)) = true ↔
      ((¬ ∀ lit ∈ viewCondLits tm T u s V, α lit.2 = lit.1) ∨
        α (configWire tm T v a) = b) := by
  rw [forceAtom, eval_clauseQBF_iff, ← eval_negLits α (viewCondLits tm T u s V)]
  constructor
  · rintro ⟨l, hl, hv⟩
    rw [List.mem_append] at hl
    rcases hl with hl | hl
    · exact Or.inl ⟨l, hl, hv⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      rw [eval_litQBF, beq_iff_eq] at hv
      exact Or.inr hv
  · rintro (⟨l, hl, hv⟩ | hv)
    · exact ⟨l, List.mem_append.mpr (Or.inl hl), hv⟩
    · refine ⟨(b, configWire tm T v a), List.mem_append.mpr (Or.inr (by simp)), ?_⟩
      rw [eval_litQBF, beq_iff_eq]
      exact hv

/-! ## The clauses of one view -/

/-- The clauses a single view contributes: they fix every atom of the new block that the view
determines. -/
noncomputable def stepClausesView (u v s : ℕ) (V : StepView tm T) : List (List CLit) :=
  ((stateList tm).map fun q =>
      forceAtom tm T u v s V (.state q) (decide (newStateV tm T V = q))) ++
  (((tapeList k).flatMap fun t => (List.finRange (T + 1)).map fun p =>
      forceAtom tm T u v s V (.head t p) (decide (newHeadV tm T V t = p.val))) ++
    ((tapeList k).flatMap fun t => symbolList.map fun sym =>
      forceAtom tm T u v s V (.cell t (headCellPosition (V.2 t)) sym)
        (decide (newSymV tm T V t = sym))))

theorem mem_stepClausesView (u v s : ℕ) (V : StepView tm T) :
    ∀ c ∈ stepClausesView tm T u v s V, ∃ a b, c = forceAtom tm T u v s V a b := by
  intro c hc
  rw [stepClausesView, List.mem_append, List.mem_append] at hc
  rcases hc with hc | hc | hc
  · rw [List.mem_map] at hc
    obtain ⟨q, -, rfl⟩ := hc
    exact ⟨_, _, rfl⟩
  · rw [List.mem_flatMap] at hc
    obtain ⟨t, -, hc⟩ := hc
    rw [List.mem_map] at hc
    obtain ⟨p, -, rfl⟩ := hc
    exact ⟨_, _, rfl⟩
  · rw [List.mem_flatMap] at hc
    obtain ⟨t, -, hc⟩ := hc
    rw [List.mem_map] at hc
    obtain ⟨sym, -, rfl⟩ := hc
    exact ⟨_, _, rfl⟩

/-- The atoms of the new block that a view fixes. -/
def StepForced (v : ℕ) (V : StepView tm T) (α : ℕ → Bool) : Prop :=
  (∀ q, α (configWire tm T v (.state q)) = decide (newStateV tm T V = q)) ∧
  (∀ (t : TapeSlot k) (p : Fin (T + 1)),
    α (configWire tm T v (.head t p)) = decide (newHeadV tm T V t = p.val)) ∧
  (∀ (t : TapeSlot k) (sym : Γ),
    α (configWire tm T v (.cell t (headCellPosition (V.2 t)) sym))
      = decide (newSymV tm T V t = sym))

theorem eval_stepClausesView (α : ℕ → Bool) (u v s : ℕ) (V : StepView tm T) :
    eval α (cnfQBF (stepClausesView tm T u v s V)) = true ↔
      ((¬ ∀ lit ∈ viewCondLits tm T u s V, α lit.2 = lit.1) ∨ StepForced tm T v V α) := by
  rw [eval_cnfQBF_iff]
  by_cases hview : ∀ lit ∈ viewCondLits tm T u s V, α lit.2 = lit.1
  · constructor
    · intro h
      refine Or.inr ⟨fun q => ?_, fun t p => ?_, fun t sym => ?_⟩
      · have hcl := h _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr
          ⟨q, mem_stateList tm q, rfl⟩)))
        rw [eval_forceAtom] at hcl
        exact hcl.resolve_left (fun hc => hc hview)
      · have hcl := h _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
          (List.mem_flatMap.mpr ⟨t, mem_tapeList t,
            List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩⟩)))))
        rw [eval_forceAtom] at hcl
        exact hcl.resolve_left (fun hc => hc hview)
      · have hcl := h _ (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
          (List.mem_flatMap.mpr ⟨t, mem_tapeList t,
            List.mem_map.mpr ⟨sym, mem_symbolList sym, rfl⟩⟩)))))
        rw [eval_forceAtom] at hcl
        exact hcl.resolve_left (fun hc => hc hview)
    · rintro (hc | ⟨h1, h2, h3⟩)
      · exact absurd hview hc
      · intro c hc
        rw [stepClausesView, List.mem_append, List.mem_append] at hc
        rcases hc with hc | hc | hc
        · rw [List.mem_map] at hc
          obtain ⟨q, -, rfl⟩ := hc
          rw [eval_forceAtom]
          exact Or.inr (h1 q)
        · rw [List.mem_flatMap] at hc
          obtain ⟨t, -, hc⟩ := hc
          rw [List.mem_map] at hc
          obtain ⟨p, -, rfl⟩ := hc
          rw [eval_forceAtom]
          exact Or.inr (h2 t p)
        · rw [List.mem_flatMap] at hc
          obtain ⟨t, -, hc⟩ := hc
          rw [List.mem_map] at hc
          obtain ⟨sym, -, rfl⟩ := hc
          rw [eval_forceAtom]
          exact Or.inr (h3 t sym)
  · constructor
    · intro _
      exact Or.inl hview
    · intro _ c hc
      obtain ⟨a, b, rfl⟩ := mem_stepClausesView tm T u v s V c hc
      rw [eval_forceAtom]
      exact Or.inl hview

/-! ## The frame clauses -/

/-- The two clauses tying a cell away from a tape's head to its old value. -/
noncomputable def framePair (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1)) (pos : Fin (T + 2))
    (sym : Γ) : List (List CLit) :=
  [[(false, configWire tm T u (.head t p)), (false, configWire tm T u (.cell t pos sym)),
      (true, configWire tm T v (.cell t pos sym))],
    [(false, configWire tm T u (.head t p)), (true, configWire tm T u (.cell t pos sym)),
      (false, configWire tm T v (.cell t pos sym))]]

theorem eval_framePair (α : ℕ → Bool) (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1))
    (pos : Fin (T + 2)) (sym : Γ) :
    eval α (cnfQBF (framePair tm T u v t p pos sym)) = true ↔
      (α (configWire tm T u (.head t p)) = true →
        α (configWire tm T v (.cell t pos sym))
          = α (configWire tm T u (.cell t pos sym))) := by
  rw [eval_cnfQBF_iff]
  simp only [framePair, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    eval_clauseQBF_iff, exists_eq_or_imp, exists_eq_left, eval_litQBF, beq_iff_eq]
  cases hh : α (configWire tm T u (.head t p)) <;>
    cases hu : α (configWire tm T u (.cell t pos sym)) <;>
    cases hv : α (configWire tm T v (.cell t pos sym)) <;> simp

/-- Every cell away from its tape's head keeps its value. -/
noncomputable def framePairOr (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1))
    (pos : Fin (T + 2)) (sym : Γ) : List (List CLit) :=
  if pos.val = p.val then
    [[(false, configWire tm T u (.head t p)), (true, configWire tm T u (.head t p))],
      [(false, configWire tm T u (.head t p)), (true, configWire tm T u (.head t p))]]
  else framePair tm T u v t p pos sym

theorem eval_framePairOr (α : ℕ → Bool) (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1))
    (pos : Fin (T + 2)) (sym : Γ) :
    eval α (cnfQBF (framePairOr tm T u v t p pos sym)) = true ↔
      (pos.val ≠ p.val → α (configWire tm T u (.head t p)) = true →
        α (configWire tm T v (.cell t pos sym))
          = α (configWire tm T u (.cell t pos sym))) := by
  rw [framePairOr]
  by_cases hne : pos.val = p.val
  · rw [if_pos hne]
    constructor
    · intro _ hc
      exact absurd hne hc
    · intro _
      rw [eval_cnfQBF_iff]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        · rw [eval_clauseQBF_iff]
          cases hb : α (configWire tm T u (.head t p))
          · exact ⟨(false, configWire tm T u (.head t p)), by simp, by
              rw [eval_litQBF, hb]; rfl⟩
          · exact ⟨(true, configWire tm T u (.head t p)), by simp, by
              rw [eval_litQBF, hb]; rfl⟩
  · rw [if_neg hne, eval_framePair]
    constructor
    · intro h _ hh
      exact h hh
    · intro h hh
      exact h hne hh

/-- Every cell away from its tape's head keeps its value. The diagonal contributes
tautologies, so that every position contributes the same number of clauses. -/
noncomputable def frameClauses (u v : ℕ) : List (List CLit) :=
  (tapeList k).flatMap fun t =>
    (List.finRange (T + 1)).flatMap fun p =>
      (List.finRange (T + 2)).flatMap fun pos =>
        symbolList.flatMap fun sym => framePairOr tm T u v t p pos sym

/-- What the frame clauses say. -/
def FrameHolds (u v : ℕ) (α : ℕ → Bool) : Prop :=
  ∀ (t : TapeSlot k) (p : Fin (T + 1)) (pos : Fin (T + 2)) (sym : Γ), pos.val ≠ p.val →
    α (configWire tm T u (.head t p)) = true →
      α (configWire tm T v (.cell t pos sym)) = α (configWire tm T u (.cell t pos sym))

theorem eval_frameClauses (α : ℕ → Bool) (u v : ℕ) :
    eval α (cnfQBF (frameClauses tm T u v)) = true ↔ FrameHolds tm T u v α := by
  rw [frameClauses, eval_cnfQBF_flatMap]
  constructor
  · intro h t p pos sym hne
    have h1 := h t (mem_tapeList t)
    rw [eval_cnfQBF_flatMap] at h1
    have h2 := h1 p (List.mem_finRange p)
    rw [eval_cnfQBF_flatMap] at h2
    have h3 := h2 pos (List.mem_finRange pos)
    rw [eval_cnfQBF_flatMap] at h3
    have h4 := h3 sym (mem_symbolList sym)
    rw [eval_framePairOr] at h4
    exact h4 hne
  · intro h t _
    rw [eval_cnfQBF_flatMap]
    intro p _
    rw [eval_cnfQBF_flatMap]
    intro pos _
    rw [eval_cnfQBF_flatMap]
    intro sym _
    rw [eval_framePairOr]
    exact fun hne => h t p pos sym hne

/-! ## The view a configuration shows -/

/-- The view a configuration shows on a given choice. -/
noncomputable def viewOf (b : Bool) (c : Cfg k tm.Q) (h : HeadsLt T c) : StepView tm T :=
  (currentCase tm b c, fun t => ⟨(t.get c).head, by have := h t; omega⟩)

theorem viewMatches_viewOf (b : Bool) (c : Cfg k tm.Q) (h : HeadsLt T c) :
    ViewMatches tm T (viewOf tm T b c h) c :=
  ⟨rfl, fun t => ⟨rfl, by cases t <;> rfl⟩⟩

@[simp] theorem viewOf_choice (b : Bool) (c : Cfg k tm.Q) (h : HeadsLt T c) :
    (viewOf tm T b c h).1.choice = b := rfl

/-- **A configuration shows only one view on a given choice.** -/
theorem eq_viewOf {V : StepView tm T} {c : Cfg k tm.Q} {b : Bool} (hm : ViewMatches tm T V c)
    (hb : V.1.choice = b) (hh : HeadsLt T c) : V = viewOf tm T b c hh := by
  refine Prod.ext ?_ ?_
  · refine TransitionCase.ext hb hm.1.symm ?_ ?_ ?_
    · exact (read_of_viewMatches tm T hm TapeSlot.input).symm
    · funext i
      exact (read_of_viewMatches tm T hm (TapeSlot.work i)).symm
    · exact (read_of_viewMatches tm T hm TapeSlot.output).symm
  · funext t
    exact Fin.ext (hm.2 t).1.symm

/-! ## The step relation as clauses -/

/-- The head positions a view names, decoded from a mixed-radix index. -/
noncomputable def headTupleOf (k T : ℕ) (i : Fin ((T + 1) ^ (k + 2))) :
    TapeSlot k → Fin (T + 1) :=
  fun t => finFunctionFinEquiv.symm i (tapeSlotEquiv k t)

theorem headTupleOf_val (k T : ℕ) (i : Fin ((T + 1) ^ (k + 2))) (t : TapeSlot k) :
    (headTupleOf k T i t).val = i.val / (T + 1) ^ (tapeSlotEquiv k t).val % (T + 1) :=
  finFunctionFinEquiv_symm_apply_val i (tapeSlotEquiv k t)

theorem headTupleOf_surj (k T : ℕ) (f : TapeSlot k → Fin (T + 1)) :
    ∃ i, headTupleOf k T i = f := by
  refine ⟨finFunctionFinEquiv fun j => f ((tapeSlotEquiv k).symm j), ?_⟩
  funext t
  rw [headTupleOf, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Every local view, as an explicit indexed list: a transition case and a mixed-radix index
for the head positions. Enumerating them this way is what lets the emitter address them. -/
noncomputable def viewList : List (StepView tm T) :=
  (Finset.univ : Finset (TransitionCase tm)).toList.flatMap fun tc =>
    (List.finRange ((T + 1) ^ (k + 2))).map fun i => (tc, headTupleOf k T i)

theorem mem_viewList (V : StepView tm T) : V ∈ viewList tm T := by
  obtain ⟨i, hi⟩ := headTupleOf_surj k T V.2
  rw [viewList, List.mem_flatMap]
  refine ⟨V.1, Finset.mem_toList.mpr (Finset.mem_univ _),
    List.mem_map.mpr ⟨i, List.mem_finRange i, ?_⟩⟩
  rw [hi]

/-- **One step of the machine, as a clause list**: every view's forced atoms, and the frame. -/
noncomputable def stepClauses (u v s : ℕ) : List (List CLit) :=
  ((viewList tm T).flatMap fun V => stepClausesView tm T u v s V) ++ frameClauses tm T u v

theorem eval_stepClauses (α : ℕ → Bool) (u v s : ℕ) :
    eval α (cnfQBF (stepClauses tm T u v s)) = true ↔
      ((∀ V : StepView tm T, (∀ lit ∈ viewCondLits tm T u s V, α lit.2 = lit.1) →
          StepForced tm T v V α) ∧ FrameHolds tm T u v α) := by
  rw [stepClauses, eval_cnfQBF_append, eval_cnfQBF_flatMap, eval_frameClauses]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun V hV => ?_, h2⟩
    have := h1 V (mem_viewList tm T V)
    rw [eval_stepClausesView] at this
    exact this.resolve_left (fun hc => hc hV)
  · rintro ⟨h1, h2⟩
    refine ⟨fun V _ => ?_, h2⟩
    rw [eval_stepClausesView]
    by_cases hV : ∀ lit ∈ viewCondLits tm T u s V, α lit.2 = lit.1
    · exact Or.inr (h1 V hV)
    · exact Or.inl hV

/-- **The step clauses say the new block is the successor.** -/
theorem stepClauses_eval (α : ℕ → Bool) (u v s : ℕ) (c : Cfg k tm.Q) (hh : HeadsLt T c)
    (hu : ∀ atom, α (configWire tm T u atom) = atom.value c) :
    eval α (cnfQBF (stepClauses tm T u v s)) = true ↔
      EncBlock tm T (blockOf (configWidth tm T) α v) (choiceStep tm (α s) c) := by
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, V₀ = viewOf tm T (α s) c hh := ⟨_, rfl⟩
  have hm : ViewMatches tm T V₀ c := by rw [hV₀]; exact viewMatches_viewOf tm T (α s) c hh
  have hch : V₀.1.choice = α s := by
    rw [hV₀]
    exact viewOf_choice tm T (α s) c hh
  have hpos : ∀ t : TapeSlot k, (V₀.2 t).val = (t.get c).head := fun t => (hm.2 t).1.symm
  obtain ⟨hst, hhd, hcl, hfr⟩ := choiceStep_of_view tm T hm
  rw [hch] at hst hhd hcl hfr
  have hcond : (∀ lit ∈ viewCondLits tm T u s V₀, α lit.2 = lit.1) :=
    (viewCondLits_iff tm T α u s V₀ c hu).mpr ⟨hch.symm, hm⟩
  have hheadtrue : ∀ t : TapeSlot k, α (configWire tm T u (.head t (V₀.2 t))) = true := fun t => by
    rw [hu (.head t (V₀.2 t))]
    exact decide_eq_true (hpos t).symm
  rw [eval_stepClauses]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨f1, f2, f3⟩ := h1 V₀ hcond
    intro atom
    rw [blockAtom_blockOf]
    cases atom with
    | state q =>
        rw [f1 q]
        show _ = decide ((choiceStep tm (α s) c).state = q)
        rw [hst]
    | head t p =>
        rw [f2 t p]
        show _ = decide ((t.get (choiceStep tm (α s) c)).head = p.val)
        rw [hhd t]
    | cell t pos sym =>
        show _ = decide ((t.get (choiceStep tm (α s) c)).cells pos.val = sym)
        by_cases hp : pos.val = (V₀.2 t).val
        · have hpe : pos = headCellPosition (V₀.2 t) := Fin.ext hp
          rw [hpe, f3 t sym]
          show decide (newSymV tm T V₀ t = sym)
            = decide ((t.get (choiceStep tm (α s) c)).cells (V₀.2 t).val = sym)
          rw [hcl t]
        · rw [h2 t (V₀.2 t) pos sym hp (hheadtrue t), hu (.cell t pos sym), hfr t pos.val hp]
          rfl
  · intro hv
    have hval : ∀ atom, α (configWire tm T v atom)
        = atom.value (choiceStep tm (α s) c) := fun atom => by
      have := hv atom
      rwa [blockAtom_blockOf] at this
    refine ⟨fun V hV => ?_, fun t p pos sym hne hhead => ?_⟩
    · obtain ⟨hs, hmV⟩ := (viewCondLits_iff tm T α u s V c hu).mp hV
      have hVeq : V = V₀ := by rw [hV₀]; exact eq_viewOf tm T hmV hs.symm hh
      subst hVeq
      refine ⟨fun q => ?_, fun t p => ?_, fun t sym => ?_⟩
      · rw [hval (.state q)]
        show decide ((choiceStep tm (α s) c).state = q) = _
        rw [hst]
      · rw [hval (.head t p)]
        show decide ((t.get (choiceStep tm (α s) c)).head = p.val) = _
        rw [hhd t]
      · rw [hval (.cell t (headCellPosition (V.2 t)) sym)]
        show decide ((t.get (choiceStep tm (α s) c)).cells
          (headCellPosition (V.2 t)).val = sym) = _
        rw [show (headCellPosition (V.2 t)).val = (V.2 t).val from rfl, hcl t]
    · have hpc : (t.get c).head = p.val := by
        have := hu (.head t p)
        rw [hhead] at this
        exact of_decide_eq_true this.symm
      rw [hval (.cell t pos sym), hu (.cell t pos sym)]
      show decide ((t.get (choiceStep tm (α s) c)).cells pos.val = sym) = _
      rw [hfr t pos.val (by rw [hpos t, hpc]; exact hne)]
      rfl

/-- **A block determines a windowed, space-bounded configuration.** -/
theorem blockInj (x : List Bool) (S : ℕ) (hT : x.length + S + 1 ≤ T)
    {u : Fin (configWidth tm T) → Bool} {c₁ c₂ : Cfg k tm.Q}
    (h₁ : EncBlock tm T u c₁) (hw₁ : Windowed x S c₁)
    (h₂ : EncBlock tm T u c₂) (hw₂ : Windowed x S c₂)
    (hs₂ : c₂.WithinDecisionSpace x.length S) : c₁ = c₂ := by
  have hstate : c₁.state = c₂.state := by
    have e₁ := h₁ (.state c₁.state)
    have e₂ := h₂ (.state c₁.state)
    rw [e₂] at e₁
    have e : decide (c₂.state = c₁.state) = decide (c₁.state = c₁.state) := e₁
    exact (of_decide_eq_true (e.trans (decide_eq_true rfl))).symm
  have hhead : ∀ tape : TapeSlot k, (tape.get c₁).head = (tape.get c₂).head := by
    intro tape
    have hb := head_le_bound tm hs₂ tape
    have hb' := headBound_le (k := k) x.length S tape
    have hlt : (tape.get c₂).head < T + 1 := by omega
    have e₁ := h₁ (.head tape ⟨(tape.get c₂).head, hlt⟩)
    have e₂ := h₂ (.head tape ⟨(tape.get c₂).head, hlt⟩)
    rw [e₂] at e₁
    have e : decide ((tape.get c₂).head = (tape.get c₂).head)
        = decide ((tape.get c₁).head = (tape.get c₂).head) := e₁
    exact of_decide_eq_true (e.symm.trans (decide_eq_true rfl))
  have hcell : ∀ (tape : TapeSlot k) (p : ℕ),
      (tape.get c₁).cells p = (tape.get c₂).cells p := by
    intro tape p
    by_cases hlt : p < T + 2
    · have e₁ := h₁ (.cell tape ⟨p, hlt⟩ ((tape.get c₁).cells p))
      have e₂ := h₂ (.cell tape ⟨p, hlt⟩ ((tape.get c₁).cells p))
      rw [e₂] at e₁
      have e : decide ((tape.get c₂).cells p = (tape.get c₁).cells p)
          = decide ((tape.get c₁).cells p = (tape.get c₁).cells p) := e₁
      exact (of_decide_eq_true (e.trans (decide_eq_true rfl))).symm
    · cases tape with
      | input =>
          show c₁.input.cells p = c₂.input.cells p
          rw [hw₁.input, hw₂.input]
      | work j =>
          show (c₁.work j).cells p = (c₂.work j).cells p
          rw [hw₁.work j p (by omega), hw₂.work j p (by omega)]
      | output =>
          show c₁.output.cells p = c₂.output.cells p
          rw [hw₁.output p (by omega), hw₂.output p (by omega)]
  refine Cfg.ext hstate ?_ ?_ ?_
  · exact Tape.ext (hhead .input) (funext fun p => hcell .input p)
  · funext j
    exact Tape.ext (hhead (.work j)) (funext fun p => hcell (.work j) p)
  · exact Tape.ext (hhead .output) (funext fun p => hcell .output p)

/-! ## The base relation as clauses -/

/-- **One step or none, as a clause list.** The scratch block carries two bits: the choice, and
a selector saying which of the two disjuncts has to hold. -/
noncomputable def cfgBaseC (u v s : ℕ) : List (List CLit) :=
  orCNF (s + 1) (eqClauses (configWidth tm T) u v) (stepClauses tm T u v s)

theorem mem_viewCondLits_vars (u s : ℕ) (V : StepView tm T) :
    ∀ l ∈ viewCondLits tm T u s V, l.2 = s ∨ (u ≤ l.2 ∧ l.2 < u + configWidth tm T) := by
  intro l hl
  rw [viewCondLits, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact Or.inl rfl
  · refine Or.inr ?_
    rw [viewLits, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact wire_mem_block tm T u _ _ rfl
    · rw [List.mem_flatMap] at hl
      obtain ⟨t, -, hl⟩ := hl
      rw [List.mem_cons, List.mem_cons] at hl
      rcases hl with rfl | rfl | hl
      · exact wire_mem_block tm T u _ _ rfl
      · exact wire_mem_block tm T u _ _ rfl
      · simp at hl

theorem mem_negLits_vars (Ls : List CLit) : ∀ l ∈ negLits Ls, ∃ l' ∈ Ls, l.2 = l'.2 := by
  intro l hl
  rw [negLits, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  exact ⟨l', hl', rfl⟩

theorem mem_forceAtom_vars (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T) (b : Bool) :
    ∀ l ∈ forceAtom tm T u v s V a b, l.2 = s ∨
      (u ≤ l.2 ∧ l.2 < u + configWidth tm T) ∨ (v ≤ l.2 ∧ l.2 < v + configWidth tm T) := by
  intro l hl
  rw [forceAtom, List.mem_append] at hl
  rcases hl with hl | hl
  · obtain ⟨l', hl', heq⟩ := mem_negLits_vars _ l hl
    rcases mem_viewCondLits_vars tm T u s V l' hl' with h | h
    · exact Or.inl (by rw [heq, h])
    · exact Or.inr (Or.inl (by rw [heq]; exact h))
  · rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact Or.inr (Or.inr (wire_mem_block tm T v _ _ rfl))
    · simp at hl

theorem mem_framePair_vars (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1)) (pos : Fin (T + 2))
    (sym : Γ) : ∀ c ∈ framePair tm T u v t p pos sym, ∀ l ∈ c,
      (u ≤ l.2 ∧ l.2 < u + configWidth tm T) ∨ (v ≤ l.2 ∧ l.2 < v + configWidth tm T) := by
  intro c hc l hl
  rw [framePair, List.mem_cons, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc <;>
    [skip; skip; (simp at hc)] <;>
    · rw [List.mem_cons, List.mem_cons, List.mem_cons] at hl
      rcases hl with rfl | rfl | rfl | hl
      · exact Or.inl (wire_mem_block tm T u _ _ rfl)
      · exact Or.inl (wire_mem_block tm T u _ _ rfl)
      · exact Or.inr (wire_mem_block tm T v _ _ rfl)
      · simp at hl

theorem mem_frameClauses_vars (u v : ℕ) :
    ∀ c ∈ frameClauses tm T u v, ∀ l ∈ c,
      (u ≤ l.2 ∧ l.2 < u + configWidth tm T) ∨ (v ≤ l.2 ∧ l.2 < v + configWidth tm T) := by
  intro c hc l hl
  rw [frameClauses, List.mem_flatMap] at hc
  obtain ⟨t, -, hc⟩ := hc
  rw [List.mem_flatMap] at hc
  obtain ⟨p, -, hc⟩ := hc
  rw [List.mem_flatMap] at hc
  obtain ⟨pos, -, hc⟩ := hc
  rw [List.mem_flatMap] at hc
  obtain ⟨sym, -, hc⟩ := hc
  rw [framePairOr] at hc
  split at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      · rw [List.mem_cons, List.mem_cons] at hl
        rcases hl with rfl | rfl | hl
        · exact Or.inl (wire_mem_block tm T u _ _ rfl)
        · exact Or.inl (wire_mem_block tm T u _ _ rfl)
        · simp at hl
  · exact mem_framePair_vars tm T u v t p pos sym c hc l hl

theorem mem_stepClauses_vars (u v s : ℕ) :
    ∀ c ∈ stepClauses tm T u v s, ∀ l ∈ c, l.2 = s ∨
      (u ≤ l.2 ∧ l.2 < u + configWidth tm T) ∨ (v ≤ l.2 ∧ l.2 < v + configWidth tm T) := by
  intro c hc l hl
  rw [stepClauses, List.mem_append] at hc
  rcases hc with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨V, -, h⟩ := h
    obtain ⟨a, b, rfl⟩ := mem_stepClausesView tm T u v s V c h
    exact mem_forceAtom_vars tm T u v s V a b l hl
  · rcases mem_frameClauses_vars tm T u v c h l hl with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

/-- What the base clauses say about the two blocks. -/
def CfgBaseC (x : List Bool) (S : ℕ) (u v : Fin (configWidth tm T) → Bool)
    (σ : Fin 2 → Bool) : Prop :=
  ∃ c, EncBlock tm T u c ∧ Windowed x S c ∧ c.WithinDecisionSpace x.length S ∧
    (if σ 1 = true then u = v else EncBlock tm T v (choiceStep tm (σ 0) c))

theorem mem_cfgBaseC_vars (u v s : ℕ) :
    ∀ c ∈ cfgBaseC tm T u v s, ∀ l ∈ c,
      (u ≤ l.2 ∧ l.2 < u + configWidth tm T) ∨ (v ≤ l.2 ∧ l.2 < v + configWidth tm T) ∨
        (s ≤ l.2 ∧ l.2 < s + 2) := by
  intro c hc l hl
  rw [cfgBaseC, orCNF, disjLit, disjLit, List.mem_append] at hc
  rcases hc with h | h
  · rcases mem_disjLits_vars _ _ c h l hl with h' | ⟨c', hc', hl'⟩
    · rw [List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · simp at h'
    · rcases mem_eqClauses_vars _ u v c' hc' l hl' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (Or.inl h'')
  · rcases mem_disjLits_vars _ _ c h l hl with h' | ⟨c', hc', hl'⟩
    · rw [List.mem_cons] at h'
      rcases h' with rfl | h'
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · simp at h'
    · rcases mem_stepClauses_vars tm T u v s c' hc' l hl' with h'' | h'' | h''
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · exact Or.inl h''
      · exact Or.inr (Or.inl h'')

theorem blockOf_two_zero (α : ℕ → Bool) (s : ℕ) : blockOf 2 α s 0 = α s := by
  rw [blockOf]
  simp

theorem blockOf_two_one (α : ℕ → Bool) (s : ℕ) : blockOf 2 α s 1 = α (s + 1) := by
  rw [blockOf]
  simp

/-- **The base clauses are the base relation.** -/
theorem cfgBaseC_eval (x : List Bool) (S : ℕ) (hT : x.length + S + 1 < T) (α : ℕ → Bool)
    (u v s : ℕ) (hu : CfgValid tm T x S (blockOf (configWidth tm T) α u)) :
    eval α (cnfQBF (cfgBaseC tm T u v s)) = true ↔
      CfgBaseC tm T x S (blockOf (configWidth tm T) α u) (blockOf (configWidth tm T) α v)
        (blockOf 2 α s) := by
  obtain ⟨c, hEnc, hwin, hspace⟩ := hu
  have hheads : HeadsLt T c := headsLt_of_within tm T hspace hT
  have hc : ∀ atom, α (configWire tm T u atom) = atom.value c := fun atom => by
    have := hEnc atom
    rwa [blockAtom_blockOf] at this
  rw [cfgBaseC, eval_orCNF, eval_eqClauses, stepClauses_eval tm T α u v s c hheads hc]
  simp only [CfgBaseC, blockOf_two_zero, blockOf_two_one]
  constructor
  · intro h
    refine ⟨c, hEnc, hwin, hspace, ?_⟩
    by_cases hz : α (s + 1) = true
    · rw [if_pos hz] at h ⊢
      exact h
    · rw [if_neg hz] at h ⊢
      exact h
  · rintro ⟨c', hEnc', hwin', hspace', h⟩
    have hheads' : HeadsLt T c' := headsLt_of_within tm T hspace' hT
    have hcc : c' = c := blockInj tm T x S (le_of_lt hT) hEnc' hwin' hEnc hwin hspace
    subst hcc
    by_cases hz : α (s + 1) = true
    · rw [if_pos hz] at h ⊢
      exact h
    · rw [if_neg hz] at h ⊢
      exact h

/-! ## Quantifier-freeness and variable ranges -/

theorem quantifierFree_cfgValidF (x : List Bool) (S off : ℕ) :
    QuantifierFree (cfgValidF tm T x S off) :=
  quantifierFree_andList _ fun φ hφ => by
    simp only [List.mem_cons, List.mem_flatMap, List.mem_map] at hφ
    rcases hφ with rfl | ⟨tape, -, rfl | ⟨pos, -, rfl⟩⟩
    · exact quantifierFree_oneHotCNF _ _ _
    · exact quantifierFree_oneHotCNF _ _ _
    · exact quantifierFree_oneHotCNF _ _ _

theorem mem_freeVars_cfgValidF (x : List Bool) (S off : ℕ) (i : ℕ)
    (hi : i ∈ freeVars (cfgValidF tm T x S off)) :
    off ≤ i ∧ i < off + configWidth tm T := by
  obtain ⟨φ, hφ, hi⟩ := mem_freeVars_andList _ i hi
  simp only [List.mem_cons, List.mem_flatMap, List.mem_map] at hφ
  rcases hφ with rfl | ⟨tape, -, rfl | ⟨pos, -, rfl⟩⟩
  · obtain ⟨q, -, h⟩ := mem_freeVars_oneHotCNF _ _ _ (fun a ha => ha) i hi
    exact wire_mem_block tm T off i _ h
  · obtain ⟨p, -, h⟩ := mem_freeVars_oneHotCNF _ _ _ (fun a _ => List.mem_finRange a) i hi
    exact wire_mem_block tm T off i _ h
  · obtain ⟨sym, -, h⟩ := mem_freeVars_oneHotCNF _ _ _
      (fun a _ => Finset.mem_toList.mpr (Finset.mem_univ a)) i hi
    exact wire_mem_block tm T off i _ h

theorem quantifierFree_cfgAccF (off : ℕ) : QuantifierFree (cfgAccF tm T off) := by
  simp [cfgAccF, QuantifierFree, quantDepth]

theorem mem_freeVars_cfgAccF (off : ℕ) (i : ℕ) (hi : i ∈ freeVars (cfgAccF tm T off)) :
    off ≤ i ∧ i < off + configWidth tm T := by
  simp only [cfgAccF, freeVars, Finset.mem_union, Finset.mem_singleton] at hi
  rcases hi with h | h
  · exact wire_mem_block tm T off i _ h
  · exact wire_mem_block tm T off i _ h

theorem quantifierFree_stepF (u v s : ℕ) : QuantifierFree (stepF tm T u v s) :=
  quantifierFree_andList _ fun φ hφ => by
    rw [List.mem_map] at hφ
    obtain ⟨atom, -, rfl⟩ := hφ
    exact quantifierFree_iffQ (by simp [QuantifierFree, quantDepth])
      (quantifierFree_ofBoolFormula _)

theorem quantifierFree_cfgBaseF (u v s : ℕ) : QuantifierFree (cfgBaseF tm T u v s) := by
  have h1 := quantifierFree_eqF (configWidth tm T) u v
  have h2 := quantifierFree_stepF tm T u v s
  simp only [QuantifierFree, quantDepth, cfgBaseF, Nat.max_eq_zero_iff] at *
  exact ⟨h1, h2⟩

theorem mem_freeVars_cfgBaseF (u v s : ℕ) (i : ℕ) (hi : i ∈ freeVars (cfgBaseF tm T u v s)) :
    (u ≤ i ∧ i < u + configWidth tm T) ∨ (v ≤ i ∧ i < v + configWidth tm T) ∨
      (s ≤ i ∧ i < s + 1) := by
  simp only [cfgBaseF, freeVars, Finset.mem_union] at hi
  rcases hi with h | h
  · rcases mem_freeVars_eqF _ _ _ _ h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨φ, hφ, h⟩ := mem_freeVars_andList _ i h
    rw [List.mem_map] at hφ
    obtain ⟨atom, -, rfl⟩ := hφ
    rcases mem_freeVars_iffQ i h with h | h
    · simp only [freeVars, Finset.mem_singleton] at h
      exact Or.inr (Or.inl (wire_mem_block tm T v i atom h))
    · rw [freeVars_ofBoolFormula] at h
      rcases mem_vars_nextFormula tm T u s atom i h with rfl | ⟨oldAtom, rfl⟩
      · exact Or.inr (Or.inr ⟨le_rfl, by omega⟩)
      · exact Or.inl (wire_mem_block tm T u _ oldAtom rfl)

/-! ## The instance -/

/-- **The machine's configuration space as a `SavitchData`**, for input `x` and space `S`, with
the layout horizon `T` beyond every head the space bound allows. -/
noncomputable def cfgSavitchData (x : List Bool) (S : ℕ) (hT : x.length + S + 1 < T) :
    SavitchData (configWidth tm T) 1 where
  Valid := CfgValid tm T x S
  Base := CfgBase tm T x S
  Acc := CfgAcc tm T
  validF := cfgValidF tm T x S
  baseF := cfgBaseF tm T
  accF := cfgAccF tm T
  validF_qf := quantifierFree_cfgValidF tm T x S
  validF_vars := mem_freeVars_cfgValidF tm T x S
  validF_eval := cfgValidF_eval tm T x S (le_of_lt hT)
  baseF_qf := quantifierFree_cfgBaseF tm T
  baseF_vars := mem_freeVars_cfgBaseF tm T
  baseF_eval := fun α u v s hu _ => cfgBaseF_eval tm T x S hT α u v s hu
  accF_qf := quantifierFree_cfgAccF tm T
  accF_vars := mem_freeVars_cfgAccF tm T
  accF_eval := cfgAccF_eval tm T

/-- **The configuration space as `SavitchData`, in clause form.** Same valid blocks and same
accepting blocks as `cfgSavitchData`; the base relation carries a second scratch bit, the
selector that says which side of `cfgBaseC`'s disjunction holds. -/
noncomputable def cfgSavitchDataC (x : List Bool) (S : ℕ) (hT : x.length + S + 1 < T) :
    SavitchData (configWidth tm T) 2 where
  Valid := CfgValid tm T x S
  Base := CfgBaseC tm T x S
  Acc := CfgAcc tm T
  validF := fun off => cnfQBF (cfgValidC tm T x S off)
  baseF := fun u v s => cnfQBF (cfgBaseC tm T u v s)
  accF := fun off => cnfQBF (cfgAccC tm T off)
  validF_qf := fun off => quantifierFree_cnfQBF _
  validF_vars := fun off i hi => by
    obtain ⟨c, hc, l, hl, rfl⟩ := mem_freeVars_cnfQBF _ i hi
    exact mem_cfgValidC_vars tm T x S off c hc l hl
  validF_eval := fun α off => cfgValidC_eval tm T x S (le_of_lt hT) α off
  baseF_qf := fun _ _ _ => quantifierFree_cnfQBF _
  baseF_vars := fun u v s i hi => by
    obtain ⟨c, hc, l, hl, rfl⟩ := mem_freeVars_cnfQBF _ i hi
    exact mem_cfgBaseC_vars tm T u v s c hc l hl
  baseF_eval := fun α u v s hu _ => cfgBaseC_eval tm T x S hT α u v s hu
  accF_qf := fun _ => quantifierFree_cnfQBF _
  accF_vars := fun off i hi => by
    obtain ⟨c, hc, l, hl, rfl⟩ := mem_freeVars_cnfQBF _ i hi
    exact mem_cfgAccC_vars tm T off c hc l hl
  accF_eval := fun α off => cfgAccC_eval tm T α off

/-- The two base relations have the same closure: the selector bit only records which disjunct
of `CfgBase` is taken. -/
theorem exists_cfgBaseC_iff (x : List Bool) (S : ℕ) (u v : Fin (configWidth tm T) → Bool) :
    (∃ σ : Fin 2 → Bool, CfgBaseC tm T x S u v σ) ↔
      (∃ σ : Fin 1 → Bool, CfgBase tm T x S u v σ) := by
  constructor
  · rintro ⟨σ, c, hEnc, hw, hs, hstep⟩
    refine ⟨fun _ => σ 0, c, hEnc, hw, hs, ?_⟩
    by_cases hσ : σ 1 = true
    · rw [if_pos hσ] at hstep
      exact Or.inl hstep.symm
    · rw [if_neg hσ] at hstep
      exact Or.inr hstep
  · rintro ⟨σ, c, hEnc, hw, hs, hstep⟩
    rcases hstep with hstep | hstep
    · refine ⟨fun i => if i = 1 then true else σ 0, c, hEnc, hw, hs, ?_⟩
      rw [if_pos (by simp)]
      exact hstep.symm
    · refine ⟨fun i => if i = 1 then false else σ 0, c, hEnc, hw, hs, ?_⟩
      rw [if_neg (by simp)]
      simpa using hstep

end Complexity
