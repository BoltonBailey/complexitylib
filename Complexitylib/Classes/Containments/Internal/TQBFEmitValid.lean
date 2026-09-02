/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFEmitClause
public import Complexitylib.Classes.Containments.Internal.TQBFConfig

/-!
# Indexing the validity clauses

⚠️ Unreviewed by Bolton

`cfgValidC` is a state group, then one block per named tape, each a head group followed by one
cell group per tape position. Every block has a size that does not depend on which tape or which
position it is, so a clause index splits by division: tape, then position, then the one-hot
group's own row and column.

## Main results

- `cfgValidC_length` and the three `cfgValidC_getElem?_*` lemmas
-/

@[expose] public section

namespace Complexity

open QBF CircuitUnrolling

variable {k : ℕ} (tm : NTM k) (T : ℕ)

/-! ## The sizes of the groups -/

theorem tapeList_length : (tapeList k).length = k + 2 := by
  rw [tapeList, List.length_map, List.length_finRange]

theorem stateGroupC_length (off : ℕ) :
    (stateGroupC tm T off).length = 1 + Fintype.card tm.Q * Fintype.card tm.Q := by
  rw [stateGroupC, oneHotClauses_length, stateList_length]

theorem headGroupC_length (n S off : ℕ) (tape : TapeSlot k) :
    (headGroupC tm T n S off tape).length = 1 + (T + 1) * (T + 1) := by
  rw [headGroupC, oneHotClauses_length, List.length_finRange]

theorem cellGroupC_length (x : List Bool) (S off : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2)) :
    (cellGroupC tm T x S off tape pos).length = 1 + 4 * 4 := by
  rw [cellGroupC, oneHotClauses_length, symbolList_length]

/-- The number of clauses one tape contributes. -/
def tapeBlockSize : ℕ := 1 + (T + 1) * (T + 1) + (T + 2) * (1 + 4 * 4)

theorem sum_map_const {α : Type} (c : ℕ) (g : α → ℕ) :
    ∀ (l : List α), (∀ a ∈ l, g a = c) → (l.map g).sum = l.length * c
  | [], _ => by simp
  | a :: t, h => by
      rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
        sum_map_const c g t (fun b hb => h b (List.mem_cons_of_mem _ hb)), List.length_cons]
      ring

theorem tapeBlock_length (x : List Bool) (S off : ℕ) (tape : TapeSlot k) :
    (headGroupC tm T x.length S off tape ++
        (List.finRange (T + 2)).flatMap fun pos => cellGroupC tm T x S off tape pos).length
      = tapeBlockSize T := by
  rw [List.length_append, headGroupC_length, List.length_flatMap,
    sum_map_const (1 + 4 * 4) _ _ (fun pos _ => cellGroupC_length tm T x S off tape pos),
    List.length_finRange, tapeBlockSize]

theorem cfgValidC_length (x : List Bool) (S off : ℕ) :
    (cfgValidC tm T x S off).length
      = 1 + Fintype.card tm.Q * Fintype.card tm.Q + (k + 2) * tapeBlockSize T := by
  rw [cfgValidC, List.length_append, stateGroupC_length, List.length_flatMap,
    sum_map_const (tapeBlockSize T) _ _
      (fun tape _ => tapeBlock_length tm T x S off tape), tapeList_length]

/-! ## The allowed head positions are a prefix -/

theorem mem_take_finRange {n m : ℕ} (p : Fin n) :
    p ∈ (List.finRange n).take m ↔ p.val < m := by
  constructor
  · intro h
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
    rw [List.length_take, List.length_finRange] at hi
    rw [List.getElem_take, List.getElem_finRange] at hget
    have hv : p.val = i := by rw [← hget]; simp
    omega
  · intro h
    refine List.mem_iff_getElem.mpr ⟨p.val, ?_, ?_⟩
    · rw [List.length_take, List.length_finRange]
      omega
    · rw [List.getElem_take, List.getElem_finRange]
      simp

theorem mem_drop_finRange {n m : ℕ} (p : Fin n) :
    p ∈ (List.finRange n).drop m ↔ m ≤ p.val := by
  constructor
  · intro h
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp h
    rw [List.length_drop, List.length_finRange] at hi
    rw [List.getElem_drop, List.getElem_finRange] at hget
    have hv : p.val = m + i := by rw [← hget]; simp
    omega
  · intro h
    refine List.mem_iff_getElem.mpr ⟨p.val - m, ?_, ?_⟩
    · rw [List.length_drop, List.length_finRange]
      have := p.isLt
      omega
    · rw [List.getElem_drop, List.getElem_finRange]
      have hv : m + (p.val - m) = p.val := by omega
      simp [hv]

/-- **The allowed head positions are exactly a prefix.** -/
theorem allowedHeads_eq (n S : ℕ) (tape : TapeSlot k) :
    allowedHeads T n S tape = (List.finRange (T + 1)).take (headBound n S tape + 1) := by
  rw [allowedHeads]
  conv_lhs => rw [← List.take_append_drop (headBound n S tape + 1) (List.finRange (T + 1))]
  rw [List.filter_append,
    List.filter_eq_self.mpr (fun a ha => by
      have h := (mem_take_finRange a).mp ha
      simp only [decide_eq_true_eq]
      omega),
    List.filter_eq_nil_iff.mpr (fun a ha => by
      have h := (mem_drop_finRange a).mp ha
      simp only [decide_eq_true_eq, not_le]
      omega),
    List.append_nil]

theorem allowedHeads_length (n S : ℕ) (tape : TapeSlot k) :
    (allowedHeads T n S tape).length = min (headBound n S tape + 1) (T + 1) := by
  rw [allowedHeads_eq, List.length_take, List.length_finRange]

theorem allowedHeads_getElem? (n S : ℕ) (tape : TapeSlot k) (i : ℕ)
    (hi : i < min (headBound n S tape + 1) (T + 1)) :
    (allowedHeads T n S tape)[i]? = some ⟨i, by omega⟩ := by
  rw [allowedHeads_eq,
    List.getElem?_eq_getElem (by rw [List.length_take, List.length_finRange]; exact hi),
    List.getElem_take, List.getElem_finRange]
  rfl

/-! ## Indexing -/

theorem tapeBlockSize_pos : 0 < tapeBlockSize T := by
  rw [tapeBlockSize]
  omega

theorem tapeBlock_getElem?_head (x : List Bool) (S off : ℕ) (tape : TapeSlot k) (p : ℕ)
    (hp : p < 1 + (T + 1) * (T + 1)) :
    (headGroupC tm T x.length S off tape ++
        (List.finRange (T + 2)).flatMap fun pos => cellGroupC tm T x S off tape pos)[p]?
      = (headGroupC tm T x.length S off tape)[p]? :=
  List.getElem?_append_left (by rw [headGroupC_length]; exact hp)

theorem tapeBlock_getElem?_cell (x : List Bool) (S off : ℕ) (tape : TapeSlot k) (p : ℕ)
    (h₁ : 1 + (T + 1) * (T + 1) ≤ p) (h₂ : p < tapeBlockSize T) :
    (headGroupC tm T x.length S off tape ++
        (List.finRange (T + 2)).flatMap fun pos => cellGroupC tm T x S off tape pos)[p]?
      = ((List.finRange (T + 2))[(p - (1 + (T + 1) * (T + 1))) / (1 + 4 * 4)]?).bind
          fun pos => (cellGroupC tm T x S off tape pos)[(p - (1 + (T + 1) * (T + 1)))
            % (1 + 4 * 4)]? := by
  have hlt : p - (1 + (T + 1) * (T + 1)) < (List.finRange (T + 2)).length * (1 + 4 * 4) := by
    rw [List.length_finRange]
    rw [tapeBlockSize] at h₂
    omega
  rw [List.getElem?_append_right (by rw [headGroupC_length]; exact h₁), headGroupC_length,
    getElem?_flatMap_const (1 + 4 * 4) (by omega) _
      (fun pos => cellGroupC_length tm T x S off tape pos) _ _ hlt]

theorem cfgValidC_getElem?_state (x : List Bool) (S off p : ℕ)
    (hp : p < 1 + Fintype.card tm.Q * Fintype.card tm.Q) :
    (cfgValidC tm T x S off)[p]? = (stateGroupC tm T off)[p]? := by
  rw [cfgValidC, List.getElem?_append_left (by rw [stateGroupC_length]; exact hp)]

theorem cfgValidC_getElem?_tape (x : List Bool) (S off p : ℕ)
    (h₁ : 1 + Fintype.card tm.Q * Fintype.card tm.Q ≤ p)
    (h₂ : p < 1 + Fintype.card tm.Q * Fintype.card tm.Q + (k + 2) * tapeBlockSize T) :
    (cfgValidC tm T x S off)[p]?
      = ((tapeList k)[(p - (1 + Fintype.card tm.Q * Fintype.card tm.Q))
            / tapeBlockSize T]?).bind fun tape =>
          (headGroupC tm T x.length S off tape ++
            (List.finRange (T + 2)).flatMap fun pos =>
              cellGroupC tm T x S off tape pos)[(p -
                (1 + Fintype.card tm.Q * Fintype.card tm.Q)) % tapeBlockSize T]? := by
  have hlt : p - (1 + Fintype.card tm.Q * Fintype.card tm.Q)
      < (tapeList k).length * tapeBlockSize T := by
    rw [tapeList_length]
    omega
  rw [cfgValidC, List.getElem?_append_right (by rw [stateGroupC_length]; exact h₁),
    stateGroupC_length,
    getElem?_flatMap_const (tapeBlockSize T) (tapeBlockSize_pos T) _
      (fun tape => tapeBlock_length tm T x S off tape) _ _ hlt]

/-- **The at-least-one clause of a head group is a run of consecutive literals.** -/
theorem atLeastOneClause_head_eq (n S : ℕ) (tape : TapeSlot k) (off : ℕ) :
    QBF.atLeastOneClause (fun p : Fin (T + 1) => configWire tm T off (.head tape p))
        (allowedHeads T n S tape)
      = (List.range (min (headBound n S tape + 1) (T + 1))).map fun j =>
          ((true, off + (Fintype.card tm.Q + tape.index.val * (T + 1) + j)) : CLit) := by
  simp only [QBF.atLeastOneClause]
  refine List.ext_getElem (by
    rw [List.length_map, allowedHeads_length, List.length_map, List.length_range])
    fun j hj hj' => ?_
  rw [List.length_map, allowedHeads_length] at hj
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  have hget : (allowedHeads T n S tape)[j]'(by rw [allowedHeads_length]; exact hj)
      = ⟨j, by omega⟩ := by
    have h := allowedHeads_getElem? T n S tape j hj
    rw [List.getElem?_eq_getElem (by rw [allowedHeads_length]; exact hj)] at h
    exact Option.some.inj h
  rw [hget, configWire, configIndex]

/-- **The at-least-one clause of a state group is a run.** -/
theorem atLeastOneClause_state_eq (off : ℕ) :
    QBF.atLeastOneClause (fun q : tm.Q => configWire tm T off (.state q)) (stateList tm)
      = (List.range (Fintype.card tm.Q)).map fun j => ((true, off + j) : CLit) := by
  simp only [QBF.atLeastOneClause]
  refine List.ext_getElem (by
    rw [List.length_map, stateList_length, List.length_map, List.length_range])
    fun j hj hj' => ?_
  rw [List.length_map, stateList_length] at hj
  rw [List.getElem_map, List.getElem_map, List.getElem_range, configWire,
    configIndex, stateIndex_stateList tm j hj]

/-- Where a cell's symbol wires start. -/
noncomputable def cellBase (tape : TapeSlot k) (pos : Fin (T + 2)) : ℕ :=
  Fintype.card tm.Q + (k + 2) * (T + 1) + (tape.index.val * (T + 2) + pos.val) * 4

/-- The index of the first symbol a cell may hold. -/
noncomputable def symStart (x : List Bool) (S : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2)) :
    ℕ :=
  (fixedSym x S tape pos.val).elim 0 fun s => (symbolIndex s).val

/-- **The at-least-one clause of a cell group is a run**: the allowed symbols are either all
four, in index order, or a single one. -/
theorem atLeastOneClause_cell_eq (x : List Bool) (S off : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) :
    QBF.atLeastOneClause (fun s : Γ => configWire tm T off (.cell tape pos s))
        (allowedSyms T x S tape pos)
      = (List.range (allowedSyms T x S tape pos).length).map fun j =>
          ((true, off + (cellBase tm T tape pos + (symStart T x S tape pos + j))) : CLit) := by
  cases h : fixedSym x S tape pos.val with
  | none =>
      have h1 : allowedSyms T x S tape pos = symbolList := by simp [allowedSyms, h]
      have h2 : symStart T x S tape pos = 0 := by simp [symStart, h]
      rw [h1, h2]
      simp only [QBF.atLeastOneClause]
      refine List.ext_getElem (by
        rw [List.length_map, List.length_map, List.length_range]) fun j hj hj' => ?_
      rw [List.length_map, symbolList_length] at hj
      rw [List.getElem_map, List.getElem_map, List.getElem_range, configWire, configIndex,
        cellBase, symbolIndex_symbolList j hj]
      congr 1
      omega
  | some s' =>
      have h1 : allowedSyms T x S tape pos = [s'] := by simp [allowedSyms, h]
      have h2 : symStart T x S tape pos = (symbolIndex s').val := by simp [symStart, h]
      rw [h1, h2]
      simp only [QBF.atLeastOneClause]
      refine List.ext_getElem (by
        rw [List.length_map, List.length_map, List.length_range]) fun j hj hj' => ?_
      rw [List.length_map, List.length_cons, List.length_nil] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [List.getElem_map, List.getElem_map, List.getElem_range, configWire, configIndex,
        cellBase, List.getElem_cons_zero]
      simp

/-! ## Where a cell's run starts, and how long it is -/

theorem symStart_of_none (x : List Bool) (S : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2))
    (h : fixedSym x S tape pos.val = none) : symStart T x S tape pos = 0 := by
  simp [symStart, h]

theorem symStart_of_some (x : List Bool) (S : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2))
    {s : Γ} (h : fixedSym x S tape pos.val = some s) :
    symStart T x S tape pos = (symbolIndex s).val := by
  simp [symStart, h]

theorem allowedSyms_length_of_none (x : List Bool) (S : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) (h : fixedSym x S tape pos.val = none) :
    (allowedSyms T x S tape pos).length = 4 := by
  simp [allowedSyms, h, symbolList]

theorem allowedSyms_length_of_some (x : List Bool) (S : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) {s : Γ} (h : fixedSym x S tape pos.val = some s) :
    (allowedSyms T x S tape pos).length = 1 := by
  simp [allowedSyms, h]

theorem symStart_lt (x : List Bool) (S : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2)) :
    symStart T x S tape pos < 4 := by
  rcases h : fixedSym x S tape pos.val with _ | s
  · rw [symStart_of_none T x S tape pos h]
    omega
  · rw [symStart_of_some T x S tape pos h]
    exact (symbolIndex s).isLt

/-- **The allowed symbols of a cell stay inside its four-symbol group.** -/
theorem symStart_add_allowedSyms_le (x : List Bool) (S : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) :
    symStart T x S tape pos + (allowedSyms T x S tape pos).length ≤ 4 := by
  rcases h : fixedSym x S tape pos.val with _ | s
  · rw [symStart_of_none T x S tape pos h, allowedSyms_length_of_none T x S tape pos h]
  · rw [symStart_of_some T x S tape pos h, allowedSyms_length_of_some T x S tape pos h]
    have := (symbolIndex s).isLt
    omega

theorem fixedSym_work (x : List Bool) (S : ℕ) (i : Fin k) (p : ℕ) :
    fixedSym x S (.work i) p = if S < p then some Γ.blank else none := rfl

theorem fixedSym_output (x : List Bool) (S : ℕ) (p : ℕ) :
    fixedSym x S (.output : TapeSlot k) p = if S + 1 < p then some Γ.blank else none := rfl

theorem fixedSym_input (x : List Bool) (S : ℕ) (p : ℕ) :
    fixedSym x S (.input : TapeSlot k) p
      = some ((Tape.init (x.map Γ.ofBool)).cells p) := rfl

/-! ## The counts as polynomials -/

open Polynomial

theorem cfgAccC_length (off : ℕ) : (cfgAccC tm T off).length = 2 := rfl

/-- How many clauses one block's validity takes. -/
noncomputable def validCountP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C (1 + Fintype.card tm.Q * Fintype.card tm.Q) +
    C (k + 2) * (C 1 + (horizonP sp + C 1) * (horizonP sp + C 1)
      + (horizonP sp + C 2) * C (1 + 4 * 4))

theorem validCountP_eval (sp : Polynomial ℕ) (n : ℕ) (x : List Bool) (S off : ℕ) :
    (validCountP tm sp).eval n
      = (cfgValidC tm ((horizonP sp).eval n) x S off).length := by
  rw [cfgValidC_length, validCountP, tapeBlockSize]
  simp only [eval_add, eval_mul, eval_C]

/-- How many clauses one level takes. -/
noncomputable def levelCountP (sp : Polynomial ℕ) : Polynomial ℕ :=
  validCountP tm sp + C 16 * widthP tm sp + C 2

/-- How many clauses the guards take. -/
noncomputable def guardCountP (sp : Polynomial ℕ) : Polynomial ℕ :=
  widthP tm sp + C 2 * validCountP tm sp + C 3

theorem levelCountP_eval (sp : Polynomial ℕ) (x : List Bool) (j : ℕ) :
    (levelCountP tm sp).eval x.length
      = ((flatLayoutOf tm sp x).levelClauses
          (cfgValidC tm ((horizonP sp).eval x.length) x (sp.eval x.length)) j).length := by
  rw [FlatLayout.levelClauses_length _ _ ((validCountP tm sp).eval x.length)
    (fun off => (validCountP_eval tm sp x.length x (sp.eval x.length) off).symm) j,
    flatLayoutOf_W, levelCountP]
  simp only [eval_add, eval_mul, eval_C]
  ring

theorem guardCountP_eval (sp : Polynomial ℕ) (x : List Bool)
    (init : Fin (flatLayoutOf tm sp x).W → Bool) :
    (guardCountP tm sp).eval x.length
      = ((flatLayoutOf tm sp x).guardClauses
          (cfgValidC tm ((horizonP sp).eval x.length) x (sp.eval x.length))
          (cfgAccC tm ((horizonP sp).eval x.length)) init).length := by
  rw [FlatLayout.guardClauses_length _ _ _ ((validCountP tm sp).eval x.length) 2
    (fun off => (validCountP_eval tm sp x.length x (sp.eval x.length) off).symm)
    (fun off => cfgAccC_length tm _ off) init, flatLayoutOf_W, guardCountP]
  simp only [eval_add, eval_mul, eval_C]
  ring

/-! ## Sizes as rulers -/

/-- A polynomial size, in unary, read off the input half of a paired argument. -/
noncomputable def rulerOf (q : Polynomial ℕ) (z : List Bool) : List Bool :=
  polyRuler q (pairFst z)

@[simp] theorem rulerOf_length (q : Polynomial ℕ) (x u : List Bool) :
    (rulerOf q (pair x u)).length = q.eval x.length := by
  rw [rulerOf, pairFst_pair, polyRuler_length]

theorem rulerOf_length' (q : Polynomial ℕ) (z : List Bool) :
    (rulerOf q z).length = q.eval (pairFst z).length := by
  rw [rulerOf, polyRuler_length]

theorem rulerOf_mem_FP (q : Polynomial ℕ) : rulerOf q ∈ FP :=
  polyRulerFn_mem_FP q pairFst_mem_FP

/-! ## The remaining sizes as polynomials -/

/-- The number of named tapes. -/
noncomputable def tapesP : Polynomial ℕ := C (k + 2)

/-- The number of head positions. -/
noncomputable def horP (sp : Polynomial ℕ) : Polynomial ℕ := horizonP sp + C 1

/-- The number of cell positions. -/
noncomputable def hor2P (sp : Polynomial ℕ) : Polynomial ℕ := horizonP sp + C 2

/-- Where a block's cell wires start, relative to its head wires. -/
noncomputable def headBlockP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C (k + 2) * horP sp

/-- The size of a state group. -/
noncomputable def stateGroupP : Polynomial ℕ :=
  C (1 + Fintype.card tm.Q * Fintype.card tm.Q)

/-- The size of a head group. -/
noncomputable def headGroupP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C 1 + horP sp * horP sp

/-- The size of one tape's block of validity clauses. -/
noncomputable def tapeBlockP (sp : Polynomial ℕ) : Polynomial ℕ :=
  headGroupP sp + hor2P sp * C (1 + 4 * 4)

/-- Twice a block's width. -/
noncomputable def twoWidthP (sp : Polynomial ℕ) : Polynomial ℕ := C 2 * widthP tm sp

@[simp] theorem horP_eval (sp : Polynomial ℕ) (n : ℕ) :
    (horP sp).eval n = (horizonP sp).eval n + 1 := by
  rw [horP, eval_add, eval_C]

@[simp] theorem hor2P_eval (sp : Polynomial ℕ) (n : ℕ) :
    (hor2P sp).eval n = (horizonP sp).eval n + 2 := by
  rw [hor2P, eval_add, eval_C]

@[simp] theorem stateGroupP_eval (n : ℕ) :
    (stateGroupP tm).eval n = 1 + Fintype.card tm.Q * Fintype.card tm.Q := by
  rw [stateGroupP, eval_C]

@[simp] theorem headBlockP_eval (sp : Polynomial ℕ) (n : ℕ) :
    (headBlockP (k := k) sp).eval n = (k + 2) * ((horizonP sp).eval n + 1) := by
  rw [headBlockP, eval_mul, eval_C, horP_eval]

@[simp] theorem headGroupP_eval (sp : Polynomial ℕ) (n : ℕ) :
    (headGroupP sp).eval n
      = 1 + ((horizonP sp).eval n + 1) * ((horizonP sp).eval n + 1) := by
  rw [headGroupP, eval_add, eval_mul, eval_C, horP_eval]

@[simp] theorem tapeBlockP_eval (sp : Polynomial ℕ) (n : ℕ) :
    (tapeBlockP sp).eval n = tapeBlockSize ((horizonP sp).eval n) := by
  rw [tapeBlockP, eval_add, eval_mul, eval_C, headGroupP_eval, hor2P_eval, tapeBlockSize]

/-- The size of one level, in variables. -/
noncomputable def levelSizeP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C 7 * widthP tm sp + C 1

/-- Where the second endpoint block starts. -/
noncomputable def bStartP (sp : Polynomial ℕ) : Polynomial ℕ := widthP tm sp

/-- Where the first chain bit lives. -/
noncomputable def y0P (sp : Polynomial ℕ) : Polynomial ℕ := C 2 * widthP tm sp

/-- Where the last chain bit lives. -/
noncomputable def yLastP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C 2 * widthP tm sp + levelSizeP tm sp * levelsP tm sp

/-- How many clauses one view contributes. -/
noncomputable def viewClauseP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C (Fintype.card tm.Q) + (C (k + 2) * horP sp + C (k + 2) * C 4)

/-- How many views there are. -/
noncomputable def viewCountP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C (Fintype.card (TransitionCase tm)) * horP sp ^ (k + 2)

/-- The frame block sizes. -/
noncomputable def frameTapeP (sp : Polynomial ℕ) : Polynomial ℕ :=
  horP sp * (hor2P sp * C (4 * 2))

/-- The frame block size for one head position. -/
noncomputable def framePosP (sp : Polynomial ℕ) : Polynomial ℕ := hor2P sp * C (4 * 2)

/-- The wire saying the second endpoint is halted. -/
noncomputable def accStateP (sp : Polynomial ℕ) : Polynomial ℕ :=
  bStartP tm sp + C (stateIndex tm tm.qhalt)

/-- The wire saying the second endpoint's output cell one holds a `1`. -/
noncomputable def accCellP (sp : Polynomial ℕ) : Polynomial ℕ :=
  bStartP tm sp + (C (Fintype.card tm.Q) + C (k + 2) * horP sp
    + (C (k + 1) * hor2P sp + C 1) * C 4 + C 1)

/-- The wire of the start state. -/
noncomputable def qstartP : Polynomial ℕ := C (stateIndex tm tm.qstart)

/-- One less than the number of levels: the level count is always positive. -/
noncomputable def predLevelsP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C (Fintype.card tm.Q) + (X + sp + C 1) + C (3 * k) * (sp + C 1) + C 3 * (sp + C 2)

theorem levelsP_eval_succ (sp : Polynomial ℕ) (nn : ℕ) :
    (levelsP tm sp).eval nn = (predLevelsP tm sp).eval nn + 1 := by
  simp only [levelsP, predLevelsP, eval_add, eval_mul, eval_C, eval_X]
  omega

/-- Where the last level starts. -/
noncomputable def lastStartP (sp : Polynomial ℕ) : Polynomial ℕ :=
  twoWidthP tm sp + C 1 + levelSizeP tm sp * predLevelsP tm sp

/-- The left endpoint of the base pair. -/
noncomputable def leftLastP (sp : Polynomial ℕ) : Polynomial ℕ :=
  lastStartP tm sp + widthP tm sp

/-- The right endpoint of the base pair. -/
noncomputable def rightLastP (sp : Polynomial ℕ) : Polynomial ℕ :=
  lastStartP tm sp + twoWidthP tm sp

/-- Where the scratch block starts. -/
noncomputable def scrP (sp : Polynomial ℕ) : Polynomial ℕ := yLastP tm sp + C 1

theorem leftLastP_eval (sp : Polynomial ℕ) (x : List Bool) :
    (leftLastP tm sp).eval x.length
      = (flatLayoutOf tm sp x).leftOf (flatLayoutOf tm sp x).n := by
  have hn : (flatLayoutOf tm sp x).n = (predLevelsP tm sp).eval x.length + 1 := by
    rw [flatLayoutOf_n]; exact levelsP_eval_succ tm sp x.length
  rw [FlatLayout.leftOf, if_neg (by omega), FlatLayout.uBlk, FlatLayout.levStart,
    FlatLayout.levelSize, flatLayoutOf_W, hn, Nat.add_sub_cancel]
  simp only [leftLastP, lastStartP, twoWidthP, levelSizeP, eval_add, eval_mul, eval_C]

theorem rightLastP_eval (sp : Polynomial ℕ) (x : List Bool) :
    (rightLastP tm sp).eval x.length
      = (flatLayoutOf tm sp x).rightOf (flatLayoutOf tm sp x).n := by
  have hn : (flatLayoutOf tm sp x).n = (predLevelsP tm sp).eval x.length + 1 := by
    rw [flatLayoutOf_n]; exact levelsP_eval_succ tm sp x.length
  rw [FlatLayout.rightOf, if_neg (by omega), FlatLayout.vBlk, FlatLayout.levStart,
    FlatLayout.levelSize, flatLayoutOf_W, hn, Nat.add_sub_cancel]
  simp only [rightLastP, lastStartP, twoWidthP, levelSizeP, eval_add, eval_mul, eval_C]

theorem guardCountP_eval_layout (sp : Polynomial ℕ) (x : List Bool) :
    (guardCountP tm sp).eval x.length
      = (flatLayoutOf tm sp x).W
        + ((validCountP tm sp).eval x.length
          + ((validCountP tm sp).eval x.length + (2 + 1))) := by
  rw [guardCountP_eval tm sp x (fun _ => false),
    FlatLayout.guardClauses_length _ _ _ ((validCountP tm sp).eval x.length) 2
      (fun off => (validCountP_eval tm sp x.length x (sp.eval x.length) off).symm)
      (fun off => cfgAccC_length tm _ off) (fun _ => false)]

theorem yLastP_eval (sp : Polynomial ℕ) (x : List Bool) :
    (yLastP tm sp).eval x.length
      = (flatLayoutOf tm sp x).yAt (flatLayoutOf tm sp x).n := by
  have hn : (flatLayoutOf tm sp x).n = (predLevelsP tm sp).eval x.length + 1 := by
    rw [flatLayoutOf_n]; exact levelsP_eval_succ tm sp x.length
  rw [FlatLayout.yAt, if_neg (by omega), FlatLayout.levStart, FlatLayout.levelSize,
    flatLayoutOf_W, hn, Nat.add_sub_cancel, yLastP, levelSizeP]
  simp only [eval_add, eval_mul, eval_C, levelsP_eval_succ tm sp x.length]
  ring

theorem scrP_eval (sp : Polynomial ℕ) (x : List Bool) :
    (scrP tm sp).eval x.length = (flatLayoutOf tm sp x).scr := by
  rw [FlatLayout.scr, FlatLayout.levelSize, flatLayoutOf_W, flatLayoutOf_n]
  simp only [scrP, yLastP, levelSizeP, eval_add, eval_mul, eval_C]
  ring

/-! ## The layout's sizes fit inside the variable count -/

theorem widthP_le_nvarP (sp : Polynomial ℕ) (n : ℕ) :
    (widthP tm sp).eval n ≤ (nvarP tm sp).eval n := by
  rw [nvarP]
  simp only [eval_add, eval_mul, eval_C]
  omega

theorem twoWidthP_le_nvarP (sp : Polynomial ℕ) (n : ℕ) :
    (twoWidthP tm sp).eval n ≤ (nvarP tm sp).eval n := by
  rw [twoWidthP, nvarP]
  simp only [eval_add, eval_mul, eval_C]
  omega

theorem y0P_le_nvarP (sp : Polynomial ℕ) (n : ℕ) :
    (y0P tm sp).eval n ≤ (nvarP tm sp).eval n := by
  rw [y0P, nvarP]
  simp only [eval_add, eval_mul, eval_C]
  omega

theorem yLastP_le_nvarP (sp : Polynomial ℕ) (n : ℕ) :
    (yLastP tm sp).eval n ≤ (nvarP tm sp).eval n := by
  rw [yLastP, nvarP, levelSizeP]
  simp only [eval_add, eval_mul, eval_C]
  omega

theorem bStartP_le_nvarP (sp : Polynomial ℕ) (n : ℕ) :
    (bStartP tm sp).eval n ≤ (nvarP tm sp).eval n := widthP_le_nvarP tm sp n

theorem flatLayoutOf_W_configWidth (sp : Polynomial ℕ) (x : List Bool) :
    (flatLayoutOf tm sp x).W = configWidth tm ((horizonP sp).eval x.length) := by
  rw [flatLayoutOf_W, widthP_eval]

theorem bStartP_eval (sp : Polynomial ℕ) (x : List Bool) :
    (bStartP tm sp).eval x.length = (flatLayoutOf tm sp x).bStart := by
  rw [bStartP, FlatLayout.bStart, flatLayoutOf_W]

theorem y0P_eval (sp : Polynomial ℕ) (x : List Bool) :
    (y0P tm sp).eval x.length = (flatLayoutOf tm sp x).y0 := by
  rw [y0P, FlatLayout.y0, flatLayoutOf_W]
  simp only [eval_mul, eval_C]

theorem accStateP_eval (sp : Polynomial ℕ) (x : List Bool) :
    (accStateP tm sp).eval x.length
      = configWire tm ((horizonP sp).eval x.length) (flatLayoutOf tm sp x).bStart
        (.state tm.qhalt) := by
  rw [accStateP, configWire, configIndex_state, ← bStartP_eval]
  simp only [eval_add, eval_C]

theorem accCellP_eval (sp : Polynomial ℕ) (x : List Bool) :
    (accCellP tm sp).eval x.length
      = configWire tm ((horizonP sp).eval x.length) (flatLayoutOf tm sp x).bStart
        (.cell TapeSlot.output ⟨1, by omega⟩ Γ.one) := by
  rw [accCellP, configWire, configIndex_cell, ← bStartP_eval]
  simp only [horP, hor2P, eval_add, eval_mul, eval_C, horizonP_eval]
  rfl

theorem accStateP_eval' (sp : Polynomial ℕ) (x : List Bool) (H : ℕ)
    (hH : (horizonP sp).eval x.length = H) :
    (accStateP tm sp).eval x.length
      = configWire tm H (flatLayoutOf tm sp x).bStart (.state tm.qhalt) := by
  subst hH
  exact accStateP_eval tm sp x

theorem accCellP_eval' (sp : Polynomial ℕ) (x : List Bool) (H : ℕ)
    (hH : (horizonP sp).eval x.length = H) :
    (accCellP tm sp).eval x.length
      = configWire tm H (flatLayoutOf tm sp x).bStart
        (.cell TapeSlot.output ⟨1, by omega⟩ Γ.one) := by
  subst hH
  exact accCellP_eval tm sp x

theorem accStateP_le_nvarP (sp : Polynomial ℕ) (x : List Bool) :
    (accStateP tm sp).eval x.length ≤ (nvarP tm sp).eval x.length := by
  have h1 := configIndex_lt tm ((horizonP sp).eval x.length) (ConfigAtom.state tm.qhalt)
  have h2 : (widthP tm sp).eval x.length
      = configWidth tm ((horizonP sp).eval x.length) := widthP_eval tm sp _
  have h3 := twoWidthP_le_nvarP tm sp x.length
  rw [twoWidthP] at h3
  simp only [eval_mul, eval_C] at h3
  have h4 : (bStartP tm sp).eval x.length = (widthP tm sp).eval x.length := by rw [bStartP]
  rw [accStateP_eval, configWire, ← bStartP_eval]
  omega

theorem accCellP_le_nvarP (sp : Polynomial ℕ) (x : List Bool) :
    (accCellP tm sp).eval x.length ≤ (nvarP tm sp).eval x.length := by
  have h1 := configIndex_lt tm ((horizonP sp).eval x.length)
    (ConfigAtom.cell TapeSlot.output ⟨1, by omega⟩ Γ.one)
  have h2 : (widthP tm sp).eval x.length
      = configWidth tm ((horizonP sp).eval x.length) := widthP_eval tm sp _
  have h3 := twoWidthP_le_nvarP tm sp x.length
  rw [twoWidthP] at h3
  simp only [eval_mul, eval_C] at h3
  have h4 : (bStartP tm sp).eval x.length = (widthP tm sp).eval x.length := by rw [bStartP]
  rw [accCellP_eval, configWire, ← bStartP_eval]
  omega

theorem leftLastP_le_nvarP (sp : Polynomial ℕ) (n : ℕ) :
    (leftLastP tm sp).eval n + (widthP tm sp).eval n ≤ (nvarP tm sp).eval n := by
  have hlv : (levelsP tm sp).eval n = (predLevelsP tm sp).eval n + 1 :=
    levelsP_eval_succ tm sp n
  have hmul : (7 * (widthP tm sp).eval n + 1) * (levelsP tm sp).eval n
      = (7 * (widthP tm sp).eval n + 1) * (predLevelsP tm sp).eval n
        + (7 * (widthP tm sp).eval n + 1) := by rw [hlv]; ring
  simp only [leftLastP, lastStartP, twoWidthP, levelSizeP, nvarP, eval_add, eval_mul,
    eval_C]
  omega

theorem rightLastP_le_nvarP (sp : Polynomial ℕ) (n : ℕ) :
    (rightLastP tm sp).eval n + (widthP tm sp).eval n ≤ (nvarP tm sp).eval n := by
  have hlv : (levelsP tm sp).eval n = (predLevelsP tm sp).eval n + 1 :=
    levelsP_eval_succ tm sp n
  have hmul : (7 * (widthP tm sp).eval n + 1) * (levelsP tm sp).eval n
      = (7 * (widthP tm sp).eval n + 1) * (predLevelsP tm sp).eval n
        + (7 * (widthP tm sp).eval n + 1) := by rw [hlv]; ring
  simp only [rightLastP, lastStartP, twoWidthP, levelSizeP, nvarP, eval_add, eval_mul,
    eval_C]
  omega

theorem scrP_le_nvarP (sp : Polynomial ℕ) (n : ℕ) :
    (scrP tm sp).eval n + 1 ≤ (nvarP tm sp).eval n := by
  simp only [scrP, yLastP, levelSizeP, nvarP, eval_add, eval_mul, eval_C]
  omega

/-- **A block inside a level fits inside the variable count.** -/
theorem levBlock_le_nvarP (sp : Polynomial ℕ) (nn j c : ℕ)
    (hj : j < (levelsP tm sp).eval nn) (hc : c ≤ (levelSizeP tm sp).eval nn) :
    (twoWidthP tm sp).eval nn + 1 + ((levelSizeP tm sp).eval nn * j + c)
      ≤ (nvarP tm sp).eval nn := by
  have hstep : (levelSizeP tm sp).eval nn * j + c
      ≤ (levelSizeP tm sp).eval nn * (levelsP tm sp).eval nn := by
    have h1 : (levelSizeP tm sp).eval nn * j + c
        ≤ (levelSizeP tm sp).eval nn * j + (levelSizeP tm sp).eval nn := by omega
    have h2 : (levelSizeP tm sp).eval nn * j + (levelSizeP tm sp).eval nn
        = (levelSizeP tm sp).eval nn * (j + 1) := by ring
    have h3 : (levelSizeP tm sp).eval nn * (j + 1)
        ≤ (levelSizeP tm sp).eval nn * (levelsP tm sp).eval nn :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  rw [nvarP, twoWidthP, levelSizeP] at *
  simp only [eval_add, eval_mul, eval_C] at *
  omega

end Complexity
