/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFSavitchRec
public import Complexitylib.Circuits.Unrolling.Transition

/-!
# A machine's configuration space as `SavitchData`

⚠️ Unreviewed by Bolton

The unrolling layout of `Complexitylib.Circuits.Unrolling` puts a configuration's one-hot atoms in
a contiguous block of `configWidth tm T` wires, and `nextFormula` is one step of the machine as a
Boolean formula over such a block and a choice wire. This file reads that layout as a block of a
quantified formula: `cfgValidF` says a block is the one-hot encoding of a configuration whose
heads are below `T`, `cfgBaseF` says one block is the other or its successor, and `cfgAccF` says
a block is halted and accepting. Together they are a `SavitchData` for the machine.

## Main definitions

- `EncBlock`, `CfgValid`, `CfgBase`, `CfgAcc` — the abstract predicates on blocks
- `cfgValidF`, `cfgBaseF`, `cfgAccF` — the formulas
- `cfgSavitchData` — the packaged `SavitchData`

## Main results

- `cfgValidF_eval`, `cfgBaseF_eval`, `cfgAccF_eval`
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

/-- A block is the one-hot encoding of a configuration. -/
def EncBlock (u : Fin (configWidth tm T) → Bool) (c : Cfg k tm.Q) : Prop :=
  ∀ atom, blockAtom tm T u atom = atom.value c

/-- A block encodes a configuration whose heads are below `T`. -/
def CfgValid (u : Fin (configWidth tm T) → Bool) : Prop :=
  ∃ c, HeadsLt T c ∧ EncBlock tm T u c

/-- One block is the other, or the configuration it reaches on the scratch bit's choice. -/
def CfgBase (u v : Fin (configWidth tm T) → Bool) (σ : Fin 1 → Bool) : Prop :=
  ∃ c, HeadsLt T c ∧ EncBlock tm T u c ∧
    (v = u ∨ EncBlock tm T v (choiceStep tm (σ 0) c))

/-- The block is halted with a `1` in output cell one. -/
noncomputable def CfgAcc (u : Fin (configWidth tm T) → Bool) : Prop :=
  blockAtom tm T u (.state tm.qhalt) = true ∧
    blockAtom tm T u (.cell .output ⟨1, by omega⟩ Γ.one) = true

/-! ## The formulas -/

/-- Every named tape, as a list. -/
noncomputable def tapeList (k : ℕ) : List (TapeSlot k) :=
  (List.finRange (k + 2)).map (tapeSlotEquiv k).symm

theorem mem_tapeList (tape : TapeSlot k) : tape ∈ tapeList k := by
  rw [tapeList, List.mem_map]
  exact ⟨tapeSlotEquiv k tape, List.mem_finRange _, (tapeSlotEquiv k).symm_apply_apply tape⟩

/-- The one-hot group of the state atoms. -/
noncomputable def stateGroupF (off : ℕ) : QBF :=
  oneHotL (fun q : tm.Q => configWire tm T off (.state q)) (Finset.univ : Finset tm.Q).toList

/-- The one-hot group of a tape's head atoms. -/
noncomputable def headGroupF (off : ℕ) (tape : TapeSlot k) : QBF :=
  oneHotL (fun p : Fin (T + 1) => configWire tm T off (.head tape p)) (List.finRange (T + 1))

/-- The one-hot group of a cell's symbol atoms. -/
noncomputable def cellGroupF (off : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2)) : QBF :=
  oneHotL (fun s : Γ => configWire tm T off (.cell tape pos s)) (Finset.univ : Finset Γ).toList

/-- The head of a tape is not at the last represented position. -/
noncomputable def headLtF (off : ℕ) (tape : TapeSlot k) : QBF :=
  neg (var (configWire tm T off (.head tape ⟨T, by omega⟩)))

/-- **A block is a configuration with heads below `T`.** -/
noncomputable def cfgValidF (off : ℕ) : QBF :=
  andList (stateGroupF tm T off ::
    (tapeList k).flatMap fun tape =>
      headGroupF tm T off tape :: headLtF tm T off tape ::
        (List.finRange (T + 2)).map (cellGroupF tm T off tape))

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

/-! ## Semantics -/

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

theorem cfgBaseF_eval (α : ℕ → Bool) (u v s : ℕ)
    (hu : CfgValid tm T (blockOf (configWidth tm T) α u)) :
    (eval α (cfgBaseF tm T u v s) = true ↔
      CfgBase tm T (blockOf (configWidth tm T) α u) (blockOf (configWidth tm T) α v)
        (blockOf 1 α s)) := by
  obtain ⟨c, hheads, hEnc⟩ := hu
  have hc : ∀ atom, α (configWire tm T u atom) = atom.value c := fun atom => by
    have := hEnc atom
    rwa [blockAtom_blockOf] at this
  have hs : blockOf 1 α s 0 = α s := by rw [blockOf]; simp
  rw [cfgBaseF, eval_disj, Bool.or_eq_true, eval_eqF_iff]
  simp only [CfgBase, hs]
  constructor
  · rintro (h | h)
    · exact ⟨c, hheads, hEnc, Or.inl h.symm⟩
    · rw [stepF_eval tm T α u v s c hheads hc] at h
      exact ⟨c, hheads, hEnc, Or.inr h⟩
  · rintro ⟨c', hheads', hEnc', h | h⟩
    · exact Or.inl h.symm
    · right
      have hc' : ∀ atom, α (configWire tm T u atom) = atom.value c' := fun atom => by
        have := hEnc' atom
        rwa [blockAtom_blockOf] at this
      rw [stepF_eval tm T α u v s c' hheads' hc']
      exact h

/-! ## The groups -/

theorem stateGroupF_eval (α : ℕ → Bool) (off : ℕ) :
    eval α (stateGroupF tm T off) = true ↔
      ∃ q₀ : tm.Q, ∀ q, α (configWire tm T off (.state q)) = decide (q = q₀) := by
  rw [stateGroupF, eval_oneHotL_inj_iff _ _ (fun a _ b _ h => by
    have := configWire_inj tm T off h
    exact ConfigAtom.state.inj this)]
  simp only [Finset.mem_toList, Finset.mem_univ, true_and, forall_const]

theorem headGroupF_eval (α : ℕ → Bool) (off : ℕ) (tape : TapeSlot k) :
    eval α (headGroupF tm T off tape) = true ↔
      ∃ p₀ : Fin (T + 1), ∀ p, α (configWire tm T off (.head tape p)) = decide (p = p₀) := by
  rw [headGroupF, eval_oneHotL_inj_iff _ _ (fun a _ b _ h => by
    have := configWire_inj tm T off h
    exact (ConfigAtom.head.inj this).2)]
  simp only [List.mem_finRange, true_and, forall_const]

theorem cellGroupF_eval (α : ℕ → Bool) (off : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2)) :
    eval α (cellGroupF tm T off tape pos) = true ↔
      ∃ s₀ : Γ, ∀ s, α (configWire tm T off (.cell tape pos s)) = decide (s = s₀) := by
  rw [cellGroupF, eval_oneHotL_inj_iff _ _ (fun a _ b _ h => by
    have := configWire_inj tm T off h
    exact (ConfigAtom.cell.inj this).2.2)]
  simp only [Finset.mem_toList, Finset.mem_univ, true_and, forall_const]

theorem headLtF_eval (α : ℕ → Bool) (off : ℕ) (tape : TapeSlot k) :
    eval α (headLtF tm T off tape) = true ↔
      α (configWire tm T off (.head tape ⟨T, by omega⟩)) = false := by
  rw [headLtF, eval_neg, eval_var, Bool.not_eq_eq_eq_not, Bool.not_true]

theorem cfgValidF_iff_groups (α : ℕ → Bool) (off : ℕ) :
    eval α (cfgValidF tm T off) = true ↔
      (eval α (stateGroupF tm T off) = true ∧
        ∀ tape : TapeSlot k, eval α (headGroupF tm T off tape) = true ∧
          eval α (headLtF tm T off tape) = true ∧
          ∀ pos, eval α (cellGroupF tm T off tape pos) = true) := by
  rw [cfgValidF, eval_andList_iff]
  simp only [List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  constructor
  · intro h
    refine ⟨h _ (Or.inl rfl), fun tape => ⟨?_, ?_, fun pos => ?_⟩⟩
    · exact h _ (Or.inr ⟨tape, mem_tapeList tape, Or.inl rfl⟩)
    · exact h _ (Or.inr ⟨tape, mem_tapeList tape, Or.inr (Or.inl rfl)⟩)
    · exact h _ (Or.inr ⟨tape, mem_tapeList tape, Or.inr (Or.inr ⟨pos, rfl⟩)⟩)
  · rintro ⟨h1, h2⟩ φ (rfl | ⟨tape, -, rfl | rfl | ⟨pos, rfl⟩⟩)
    · exact h1
    · exact (h2 tape).1
    · exact (h2 tape).2.1
    · exact (h2 tape).2.2 pos

/-! ## Decoding a valid block -/

/-- The configuration a one-hot block denotes. -/
noncomputable def decodeCfgOf (q₀ : tm.Q) (p₀ : TapeSlot k → Fin (T + 1))
    (s₀ : TapeSlot k → Fin (T + 2) → Γ) : Cfg k tm.Q where
  state := q₀
  input := ⟨(p₀ .input).val, fun i => if h : i < T + 2 then s₀ .input ⟨i, h⟩ else Γ.blank⟩
  work := fun j => ⟨(p₀ (.work j)).val,
    fun i => if h : i < T + 2 then s₀ (.work j) ⟨i, h⟩ else Γ.blank⟩
  output := ⟨(p₀ .output).val, fun i => if h : i < T + 2 then s₀ .output ⟨i, h⟩ else Γ.blank⟩

theorem get_decodeCfgOf (q₀ : tm.Q) (p₀ : TapeSlot k → Fin (T + 1))
    (s₀ : TapeSlot k → Fin (T + 2) → Γ) (tape : TapeSlot k) :
    tape.get (decodeCfgOf tm T q₀ p₀ s₀)
      = ⟨(p₀ tape).val, fun i => if h : i < T + 2 then s₀ tape ⟨i, h⟩ else Γ.blank⟩ := by
  cases tape <;> rfl

theorem cfgValidF_eval (α : ℕ → Bool) (off : ℕ) :
    eval α (cfgValidF tm T off) = true ↔
      CfgValid tm T (blockOf (configWidth tm T) α off) := by
  rw [cfgValidF_iff_groups]
  constructor
  · rintro ⟨hst, hrest⟩
    rw [stateGroupF_eval] at hst
    obtain ⟨q₀, hq₀⟩ := hst
    have hhead : ∀ tape : TapeSlot k, ∃ p₀ : Fin (T + 1),
        ∀ p, α (configWire tm T off (.head tape p)) = decide (p = p₀) := fun tape => by
      have := (hrest tape).1
      rwa [headGroupF_eval] at this
    have hcell : ∀ (tape : TapeSlot k) (pos : Fin (T + 2)), ∃ s₀ : Γ,
        ∀ s, α (configWire tm T off (.cell tape pos s)) = decide (s = s₀) := fun tape pos => by
      have := (hrest tape).2.2 pos
      rwa [cellGroupF_eval] at this
    choose p₀ hp₀ using hhead
    choose s₀ hs₀ using hcell
    refine ⟨decodeCfgOf tm T q₀ p₀ s₀, fun tape => ?_, fun atom => ?_⟩
    · rw [get_decodeCfgOf]
      have hne := (hrest tape).2.1
      rw [headLtF_eval, hp₀ tape ⟨T, by omega⟩] at hne
      have : ¬ ((⟨T, by omega⟩ : Fin (T + 1)) = p₀ tape) := by
        intro hc
        rw [decide_eq_true hc] at hne
        exact Bool.noConfusion hne
      have hlt := (p₀ tape).isLt
      have hval : (p₀ tape).val ≠ T := by
        intro hc
        refine this (Fin.ext ?_)
        show T = (p₀ tape).val
        omega
      simp only
      omega
    · rw [blockAtom_blockOf]
      cases atom with
      | state q =>
          rw [hq₀ q]
          show _ = decide ((decodeCfgOf tm T q₀ p₀ s₀).state = q)
          exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩
      | head tape p =>
          rw [hp₀ tape p]
          show _ = decide ((tape.get (decodeCfgOf tm T q₀ p₀ s₀)).head = p.val)
          rw [get_decodeCfgOf]
          exact decide_eq_decide.mpr ⟨fun h => by rw [h], fun h => Fin.ext h.symm⟩
      | cell tape pos s =>
          rw [hs₀ tape pos s]
          show _ = decide ((tape.get (decodeCfgOf tm T q₀ p₀ s₀)).cells pos.val = s)
          rw [get_decodeCfgOf]
          simp only [dif_pos pos.isLt, Fin.eta]
          exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩
  · rintro ⟨c, hheads, hEnc⟩
    have hval : ∀ atom, α (configWire tm T off atom) = atom.value c := fun atom => by
      have := hEnc atom
      rwa [blockAtom_blockOf] at this
    refine ⟨?_, fun tape => ⟨?_, ?_, fun pos => ?_⟩⟩
    · rw [stateGroupF_eval]
      refine ⟨c.state, fun q => ?_⟩
      rw [hval (.state q)]
      exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩
    · rw [headGroupF_eval]
      refine ⟨⟨(tape.get c).head, by have := hheads tape; omega⟩, fun p => ?_⟩
      rw [hval (.head tape p)]
      exact decide_eq_decide.mpr ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
    · rw [headLtF_eval, hval (.head tape ⟨T, by omega⟩)]
      show decide ((tape.get c).head = T) = false
      have := hheads tape
      exact decide_eq_false (by omega)
    · rw [cellGroupF_eval]
      refine ⟨(tape.get c).cells pos.val, fun s => ?_⟩
      rw [hval (.cell tape pos s)]
      exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩

/-! ## Quantifier-freeness and variable ranges -/

theorem quantifierFree_cfgValidF (off : ℕ) : QuantifierFree (cfgValidF tm T off) :=
  quantifierFree_andList _ fun φ hφ => by
    simp only [List.mem_cons, List.mem_flatMap, List.mem_map] at hφ
    rcases hφ with rfl | ⟨tape, -, rfl | rfl | ⟨pos, -, rfl⟩⟩
    · exact quantifierFree_oneHotL _ _
    · exact quantifierFree_oneHotL _ _
    · simp [headLtF, QuantifierFree, quantDepth]
    · exact quantifierFree_oneHotL _ _

theorem mem_freeVars_cfgValidF (off : ℕ) (i : ℕ) (hi : i ∈ freeVars (cfgValidF tm T off)) :
    off ≤ i ∧ i < off + configWidth tm T := by
  obtain ⟨φ, hφ, hi⟩ := mem_freeVars_andList _ i hi
  have hwire : ∀ atom : ConfigAtom tm T, i = configWire tm T off atom →
      off ≤ i ∧ i < off + configWidth tm T := by
    rintro atom rfl
    have := configIndex_lt tm T atom
    rw [configWire]
    omega
  simp only [List.mem_cons, List.mem_flatMap, List.mem_map] at hφ
  rcases hφ with rfl | ⟨tape, -, rfl | rfl | ⟨pos, -, rfl⟩⟩
  · obtain ⟨q, -, h⟩ := mem_freeVars_oneHotL _ _ i hi
    exact hwire _ h
  · obtain ⟨p, -, h⟩ := mem_freeVars_oneHotL _ _ i hi
    exact hwire _ h
  · simp only [headLtF, freeVars, Finset.mem_singleton] at hi
    exact hwire _ hi
  · obtain ⟨sym, -, h⟩ := mem_freeVars_oneHotL _ _ i hi
    exact hwire _ h

theorem quantifierFree_cfgAccF (off : ℕ) : QuantifierFree (cfgAccF tm T off) := by
  simp [cfgAccF, QuantifierFree, quantDepth]

theorem mem_freeVars_cfgAccF (off : ℕ) (i : ℕ) (hi : i ∈ freeVars (cfgAccF tm T off)) :
    off ≤ i ∧ i < off + configWidth tm T := by
  have hwire : ∀ atom : ConfigAtom tm T, i = configWire tm T off atom →
      off ≤ i ∧ i < off + configWidth tm T := by
    rintro atom rfl
    have := configIndex_lt tm T atom
    rw [configWire]
    omega
  simp only [cfgAccF, freeVars, Finset.mem_union, Finset.mem_singleton] at hi
  rcases hi with h | h
  · exact hwire _ h
  · exact hwire _ h

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
  have hwire : ∀ (off : ℕ) (atom : ConfigAtom tm T), i = configWire tm T off atom →
      off ≤ i ∧ i < off + configWidth tm T := by
    rintro off atom rfl
    have := configIndex_lt tm T atom
    rw [configWire]
    omega
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
      exact Or.inr (Or.inl (hwire v atom h))
    · rw [freeVars_ofBoolFormula] at h
      rcases mem_vars_nextFormula tm T u s atom i h with rfl | ⟨oldAtom, rfl⟩
      · exact Or.inr (Or.inr ⟨le_rfl, by omega⟩)
      · exact Or.inl (hwire u oldAtom rfl)

/-! ## The instance -/

/-- **The machine's configuration space as a `SavitchData`.** -/
noncomputable def cfgSavitchData : SavitchData (configWidth tm T) 1 where
  Valid := CfgValid tm T
  Base := CfgBase tm T
  Acc := CfgAcc tm T
  validF := cfgValidF tm T
  baseF := cfgBaseF tm T
  accF := cfgAccF tm T
  validF_qf := quantifierFree_cfgValidF tm T
  validF_vars := mem_freeVars_cfgValidF tm T
  validF_eval := cfgValidF_eval tm T
  baseF_qf := quantifierFree_cfgBaseF tm T
  baseF_vars := mem_freeVars_cfgBaseF tm T
  baseF_eval := fun α u v s hu _ => cfgBaseF_eval tm T α u v s hu
  accF_qf := quantifierFree_cfgAccF tm T
  accF_vars := mem_freeVars_cfgAccF tm T
  accF_eval := cfgAccF_eval tm T

end Complexity
