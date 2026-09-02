/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFConfig

/-!
# Savitch's recursion as a flat CNF

⚠️ Unreviewed by Bolton

The recursion of `Complexitylib.Classes.Containments.Internal.TQBFSavitchRec` nests an
implication per level, which a generic Tseitin pass would have to walk as a parse tree. This file
lays the same content out flat: one variable block per level, an auxiliary bit `y j` carrying
"the chain of conditions has held so far", and one equality-bit block per comparison, so that
every clause family is indexed by the level and the whole matrix is a single indexed family — the
shape `Complexity.emit_list_mem_FP` consumes.

## Main definitions

- `FlatLayout` — where each block lives
- `levelClauses`, `flatClauses` — the matrix
- `flatPrefix` — the quantifier prefix

## Main results

- `flatPrefix_listed` — the prefix names consecutive variables, universal exactly on `U`/`V`
-/

@[expose] public section

namespace Complexity

open QBF CircuitUnrolling Shen

/-- Where the blocks of the flat encoding live, for a block width `W` and `n` levels. -/
structure FlatLayout where
  /-- The width of a configuration block. -/
  W : ℕ
  /-- The width of the scratch block. -/
  Ws : ℕ
  /-- The number of levels. -/
  n : ℕ

namespace FlatLayout

variable (L : FlatLayout)

/-- The variables of one level: the midpoint, the two universal blocks, four equality-bit
blocks, and the next chain bit. -/
def levelSize : ℕ := 7 * L.W + 1

/-- The second block. -/
def bStart : ℕ := L.W
/-- The chain bit before any level. -/
def y0 : ℕ := 2 * L.W
/-- Where level `j` starts. -/
def levStart (j : ℕ) : ℕ := 2 * L.W + 1 + L.levelSize * j
/-- The midpoint of level `j`. -/
def mid (j : ℕ) : ℕ := L.levStart j
/-- The first universal block of level `j`. -/
def uBlk (j : ℕ) : ℕ := L.levStart j + L.W
/-- The second universal block of level `j`. -/
def vBlk (j : ℕ) : ℕ := L.levStart j + 2 * L.W
/-- The bits comparing `U` with the level's left endpoint. -/
def eUA (j : ℕ) : ℕ := L.levStart j + 3 * L.W
/-- The bits comparing `V` with the midpoint. -/
def eVM (j : ℕ) : ℕ := L.levStart j + 4 * L.W
/-- The bits comparing `U` with the midpoint. -/
def eUM (j : ℕ) : ℕ := L.levStart j + 5 * L.W
/-- The bits comparing `V` with the level's right endpoint. -/
def eVB (j : ℕ) : ℕ := L.levStart j + 6 * L.W
/-- The chain bit after level `j`. -/
def yAt (j : ℕ) : ℕ := if j = 0 then L.y0 else L.levStart (j - 1) + 7 * L.W
/-- The left endpoint of level `j`. -/
def leftOf (j : ℕ) : ℕ := if j = 0 then 0 else L.uBlk (j - 1)
/-- The right endpoint of level `j`. -/
def rightOf (j : ℕ) : ℕ := if j = 0 then L.bStart else L.vBlk (j - 1)
/-- Where the scratch block sits. -/
def scr : ℕ := 2 * L.W + 1 + L.levelSize * L.n
/-- How many variables the encoding uses. -/
def nvar : ℕ := L.scr + L.Ws

theorem levStart_lt_scr {j : ℕ} (hj : j < L.n) : L.levStart j + L.levelSize ≤ L.scr := by
  rw [levStart, scr]
  have h1 : L.levelSize * (j + 1) ≤ L.levelSize * L.n := Nat.mul_le_mul_left _ hj
  have h2 : L.levelSize * (j + 1) = L.levelSize * j + L.levelSize := by ring
  omega

theorem y0_lt_scr : L.y0 < L.scr := by
  rw [y0, scr]
  omega

theorem levelSize_pos : 0 < L.levelSize := by
  rw [levelSize]
  omega

/-- Reading a level's index and offset back off a variable. -/
theorem levOffset (j c : ℕ) (hc : c < L.levelSize) :
    (L.levStart j + c - (2 * L.W + 1)) % L.levelSize = c ∧
      (L.levStart j + c - (2 * L.W + 1)) / L.levelSize = j := by
  have hrw : L.levStart j + c - (2 * L.W + 1) = L.levelSize * j + c := by
    rw [levStart]
    omega
  rw [hrw]
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  · rw [Nat.mul_add_div L.levelSize_pos, Nat.div_eq_of_lt hc]
    omega

/-! ## The quantifier prefix -/

/-- Which variables are universally quantified: exactly the two blocks of each level that the
verifier chooses. -/
def flatKind (i : ℕ) : Bool :=
  decide (2 * L.W + 1 ≤ i ∧ (i - (2 * L.W + 1)) / L.levelSize < L.n ∧
    L.W ≤ (i - (2 * L.W + 1)) % L.levelSize ∧ (i - (2 * L.W + 1)) % L.levelSize < 3 * L.W)

/-- The prefix: every variable in order, universal exactly on the chosen blocks. -/
noncomputable def flatPrefix : Prefix :=
  (List.range L.nvar).map fun i => (L.flatKind i, i)

theorem flatPrefix_length : L.flatPrefix.length = L.nvar := by
  rw [flatPrefix, List.length_map, List.length_range]

theorem flatPrefix_listed : SavitchData.Listed L.flatKind 0 L.flatPrefix := by
  rw [SavitchData.Listed, flatPrefix_length, flatPrefix]
  refine List.map_congr_left fun i _ => ?_
  rw [Nat.zero_add]

/-- A variable inside a level's block, with its offset. -/
theorem flatKind_lev (j c : ℕ) (hj : j < L.n) (hc : c < L.levelSize) :
    L.flatKind (L.levStart j + c) = decide (L.W ≤ c ∧ c < 3 * L.W) := by
  obtain ⟨hm, hd⟩ := L.levOffset j c hc
  rw [flatKind, hm, hd]
  refine decide_eq_decide.mpr ⟨fun h => ⟨h.2.2.1, h.2.2.2⟩, fun h => ⟨?_, hj, h.1, h.2⟩⟩
  rw [levStart]
  omega

theorem flatKind_uBlk (j i : ℕ) (hj : j < L.n) (hi : i < L.W) :
    L.flatKind (L.uBlk j + i) = true := by
  have hc : L.W + i < L.levelSize := by rw [levelSize]; omega
  have hrw : L.uBlk j + i = L.levStart j + (L.W + i) := by rw [uBlk]; omega
  rw [hrw, L.flatKind_lev j (L.W + i) hj hc, decide_eq_true]
  omega

theorem flatKind_vBlk (j i : ℕ) (hj : j < L.n) (hi : i < L.W) :
    L.flatKind (L.vBlk j + i) = true := by
  have hc : 2 * L.W + i < L.levelSize := by rw [levelSize]; omega
  have hrw : L.vBlk j + i = L.levStart j + (2 * L.W + i) := by rw [vBlk]; omega
  rw [hrw, L.flatKind_lev j (2 * L.W + i) hj hc, decide_eq_true]
  omega

theorem flatKind_mid (j i : ℕ) (hj : j < L.n) (hi : i < L.W) :
    L.flatKind (L.mid j + i) = false := by
  have hc : i < L.levelSize := by rw [levelSize]; omega
  have hrw : L.mid j + i = L.levStart j + i := by rw [mid]
  rw [hrw, L.flatKind_lev j i hj hc, decide_eq_false]
  omega

theorem flatKind_below (i : ℕ) (hi : i < 2 * L.W + 1) : L.flatKind i = false := by
  rw [flatKind, decide_eq_false]
  rintro ⟨h, -, -, -⟩
  omega

theorem flatKind_scr (i : ℕ) (hi : L.scr ≤ i) : L.flatKind i = false := by
  rw [flatKind, decide_eq_false]
  rintro ⟨-, hd, -, -⟩
  have hge : L.n * L.levelSize ≤ i - (2 * L.W + 1) := by
    rw [scr] at hi
    have : L.levelSize * L.n = L.n * L.levelSize := by ring
    omega
  have hle : L.n ≤ (i - (2 * L.W + 1)) / L.levelSize :=
    (Nat.le_div_iff_mul_le L.levelSize_pos).mpr hge
  omega

theorem flatKind_eblk (j i : ℕ) (hj : j < L.n) (hi : i < 4 * L.W + 1) :
    L.flatKind (L.eUA j + i) = false := by
  have hc : 3 * L.W + i < L.levelSize := by rw [levelSize]; omega
  have hrw : L.eUA j + i = L.levStart j + (3 * L.W + i) := by rw [eUA]; omega
  rw [hrw, L.flatKind_lev j (3 * L.W + i) hj hc, decide_eq_false]
  omega

theorem levStart_succ (j : ℕ) : L.levStart (j + 1) = L.levStart j + L.levelSize := by
  rw [levStart, levStart]
  ring

theorem yAt_lt_levStart (j : ℕ) : L.yAt j < L.levStart j := by
  cases j with
  | zero =>
      rw [yAt, if_pos rfl, y0, levStart]
      omega
  | succ j =>
      rw [yAt, if_neg (by omega), levStart_succ, levelSize]
      simp only [Nat.add_sub_cancel]
      omega

theorem leftOf_succ (j : ℕ) : L.leftOf (j + 1) = L.uBlk j := by
  rw [leftOf, if_neg (by omega), Nat.add_sub_cancel]

theorem rightOf_succ (j : ℕ) : L.rightOf (j + 1) = L.vBlk j := by
  rw [rightOf, if_neg (by omega), Nat.add_sub_cancel]

theorem yAt_succ (j : ℕ) : L.yAt (j + 1) = L.levStart j + 7 * L.W := by
  rw [yAt, if_neg (by omega), Nat.add_sub_cancel]

/-! ### The blocks of a level are adjacent -/

theorem uBlk_eq (j : ℕ) : L.uBlk j = L.mid j + L.W := rfl
theorem vBlk_eq (j : ℕ) : L.vBlk j = L.uBlk j + L.W := by
  rw [vBlk, uBlk]
  ring
theorem eUA_eq (j : ℕ) : L.eUA j = L.vBlk j + L.W := by
  rw [eUA, vBlk]
  ring
theorem eVM_eq (j : ℕ) : L.eVM j = L.eUA j + L.W := by
  rw [eVM, eUA]
  ring
theorem eUM_eq (j : ℕ) : L.eUM j = L.eVM j + L.W := by
  rw [eUM, eVM]
  ring
theorem eVB_eq (j : ℕ) : L.eVB j = L.eUM j + L.W := by
  rw [eVB, eUM]
  ring
theorem yAt_succ_eq (j : ℕ) : L.yAt (j + 1) = L.eVB j + L.W := by
  rw [yAt_succ, eVB]
  ring
theorem levStart_succ_eq (j : ℕ) : L.levStart (j + 1) = L.yAt (j + 1) + 1 := by
  rw [levStart_succ, yAt_succ, levelSize]
  ring

/-- **Merging two adjacent existential blocks.** -/
theorem exists_merge (α : ℕ → Bool) (o n₁ n₂ : ℕ) (P : (ℕ → Bool) → Prop) :
    (∃ β : ℕ → Bool, (∀ i, (i < o ∨ o + n₁ ≤ i) → β i = α i) ∧
      ∃ γ : ℕ → Bool, (∀ i, (i < o + n₁ ∨ o + n₁ + n₂ ≤ i) → γ i = β i) ∧ P γ) ↔
    (∃ γ : ℕ → Bool, (∀ i, (i < o ∨ o + (n₁ + n₂) ≤ i) → γ i = α i) ∧ P γ) := by
  constructor
  · rintro ⟨β, hβ, γ, hγ, hP⟩
    refine ⟨γ, fun i hi => ?_, hP⟩
    rw [hγ i (by omega), hβ i (by omega)]
  · rintro ⟨γ, hγ, hP⟩
    classical
    refine ⟨fun i => if o + n₁ ≤ i ∧ i < o + n₁ + n₂ then α i else γ i, fun i hi => ?_,
      γ, fun i hi => ?_, hP⟩
    · show (if o + n₁ ≤ i ∧ i < o + n₁ + n₂ then α i else γ i) = α i
      by_cases hc : o + n₁ ≤ i ∧ i < o + n₁ + n₂
      · rw [if_pos hc]
      · rw [if_neg hc]
        exact hγ i (by omega)
    · show γ i = (if o + n₁ ≤ i ∧ i < o + n₁ + n₂ then α i else γ i)
      rw [if_neg (by omega)]

/-- **The five auxiliary blocks of a level are one existential block.** -/
theorem exists_aux_blocks (j : ℕ) (α : ℕ → Bool) (P : (ℕ → Bool) → Prop) :
    (∃ ε₁ : ℕ → Bool, (∀ i, (i < L.eUA j ∨ L.eUA j + L.W ≤ i) → ε₁ i = α i) ∧
      ∃ ε₂ : ℕ → Bool, (∀ i, (i < L.eVM j ∨ L.eVM j + L.W ≤ i) → ε₂ i = ε₁ i) ∧
        ∃ ε₃ : ℕ → Bool, (∀ i, (i < L.eUM j ∨ L.eUM j + L.W ≤ i) → ε₃ i = ε₂ i) ∧
          ∃ ε₄ : ℕ → Bool, (∀ i, (i < L.eVB j ∨ L.eVB j + L.W ≤ i) → ε₄ i = ε₃ i) ∧
            ∃ ε₅ : ℕ → Bool,
              (∀ i, (i < L.yAt (j + 1) ∨ L.yAt (j + 1) + 1 ≤ i) → ε₅ i = ε₄ i) ∧ P ε₅) ↔
    (∃ ε : ℕ → Bool,
      (∀ i, (i < L.eUA j ∨ L.eUA j + (4 * L.W + 1) ≤ i) → ε i = α i) ∧ P ε) := by
  classical
  have h1 : L.eVM j = L.eUA j + L.W := L.eVM_eq j
  have h2 : L.eUM j = L.eUA j + L.W + L.W := by rw [L.eUM_eq j, h1]
  have h3 : L.eVB j = L.eUA j + L.W + L.W + L.W := by rw [L.eVB_eq j, h2]
  have h4 : L.yAt (j + 1) = L.eUA j + L.W + L.W + L.W + L.W := by rw [L.yAt_succ_eq j, h3]
  constructor
  · rintro ⟨ε₁, a1, ε₂, a2, ε₃, a3, ε₄, a4, ε₅, a5, hP⟩
    refine ⟨ε₅, fun i hi => ?_, hP⟩
    rw [a5 i (by omega), a4 i (by omega), a3 i (by omega), a2 i (by omega), a1 i (by omega)]
  · rintro ⟨ε, hε, hP⟩
    refine ⟨fun i => if L.eUA j ≤ i ∧ i < L.eUA j + L.W then ε i else α i, fun i hi => ?_,
      fun i => if L.eUA j ≤ i ∧ i < L.eUA j + 2 * L.W then ε i else α i, fun i hi => ?_,
      fun i => if L.eUA j ≤ i ∧ i < L.eUA j + 3 * L.W then ε i else α i, fun i hi => ?_,
      fun i => if L.eUA j ≤ i ∧ i < L.eUA j + 4 * L.W then ε i else α i, fun i hi => ?_,
      ε, fun i hi => ?_, hP⟩
    · show (if L.eUA j ≤ i ∧ i < L.eUA j + L.W then ε i else α i) = α i
      rw [if_neg (by omega)]
    · show (if L.eUA j ≤ i ∧ i < L.eUA j + 2 * L.W then ε i else α i)
        = (if L.eUA j ≤ i ∧ i < L.eUA j + L.W then ε i else α i)
      by_cases hc : L.eUA j ≤ i ∧ i < L.eUA j + L.W
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]
    · show (if L.eUA j ≤ i ∧ i < L.eUA j + 3 * L.W then ε i else α i)
        = (if L.eUA j ≤ i ∧ i < L.eUA j + 2 * L.W then ε i else α i)
      by_cases hc : L.eUA j ≤ i ∧ i < L.eUA j + 2 * L.W
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]
    · show (if L.eUA j ≤ i ∧ i < L.eUA j + 4 * L.W then ε i else α i)
        = (if L.eUA j ≤ i ∧ i < L.eUA j + 3 * L.W then ε i else α i)
      by_cases hc : L.eUA j ≤ i ∧ i < L.eUA j + 3 * L.W
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]
    · show ε i = (if L.eUA j ≤ i ∧ i < L.eUA j + 4 * L.W then ε i else α i)
      by_cases hc : L.eUA j ≤ i ∧ i < L.eUA j + 4 * L.W
      · rw [if_pos hc]
      · rw [if_neg hc]
        exact hε i (by omega)

/-! ## The clause families -/

/-- The literals saying every bit of a block is `false`. -/
def negRange (W off : ℕ) : List CLit := (List.range W).map fun i => (false, off + i)

theorem eval_negRange (α : ℕ → Bool) (W off : ℕ) :
    (∃ l ∈ negRange W off, eval α (litQBF l) = true) ↔ ¬ ∀ i, i < W → α (off + i) = true := by
  simp only [negRange, List.mem_map, List.mem_range, exists_exists_and_eq_and, eval_litQBF,
    beq_iff_eq]
  constructor
  · rintro ⟨i, hi, hv⟩ hall
    rw [hall i hi] at hv
    exact Bool.noConfusion hv
  · intro h
    by_contra hc
    push Not at hc
    refine h fun i hi => ?_
    cases hα : α (off + i) with
    | false => exact absurd hα (hc i hi)
    | true => rfl

/-- Unit clauses pinning a block to a fixed value. -/
def constClauses (W off : ℕ) (b : Fin W → Bool) : List (List CLit) :=
  (List.finRange W).map fun i => [(b i, off + i.val)]

theorem eval_constClauses (α : ℕ → Bool) (W off : ℕ) (b : Fin W → Bool) :
    eval α (cnfQBF (constClauses W off b)) = true ↔ blockOf W α off = b := by
  rw [eval_cnfQBF_iff]
  simp only [constClauses, List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, eval_clauseQBF_iff, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_left, eval_litQBF, beq_iff_eq]
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

theorem negRange_length (W off : ℕ) : (negRange W off).length = W := by
  rw [negRange, List.length_map, List.length_range]

theorem negRange_getElem? (W off i : ℕ) (hi : i < W) :
    (negRange W off)[i]? = some (false, off + i) := by
  rw [negRange, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [List.length_range]; exact hi)]
  simp

/-! ## The clauses of one level -/

variable (validC : ℕ → List (List CLit))

/-- The chain clause for one of the two ways the level's condition can hold. -/
def chainClause (j : ℕ) (e₁ e₂ : ℕ) : List CLit :=
  ((false, L.yAt j) :: (negRange L.W e₁ ++ negRange L.W e₂)) ++ [(true, L.yAt (j + 1))]

/-- The clauses of level `j`: the midpoint is valid whenever the chain still holds, the four
equality-bit blocks say what they compare, and the chain carries on when the level's condition
does. -/
noncomputable def levelClauses (j : ℕ) : List (List CLit) :=
  disjLit (false, L.yAt j) (validC (L.mid j)) ++
    ((eqAuxCNF L.W (L.eUA j) (L.uBlk j) (L.leftOf j) ++
        eqAuxCNF L.W (L.eVM j) (L.vBlk j) (L.mid j)) ++
      ((eqAuxCNF L.W (L.eUM j) (L.uBlk j) (L.mid j) ++
          eqAuxCNF L.W (L.eVB j) (L.vBlk j) (L.rightOf j)) ++
        [L.chainClause j (L.eUA j) (L.eVM j), L.chainClause j (L.eUM j) (L.eVB j)]))

theorem eval_chainClause (α : ℕ → Bool) (j e₁ e₂ : ℕ) :
    eval α (clauseQBF (L.chainClause j e₁ e₂)) = true ↔
      ((α (L.yAt j) = true ∧ (∀ i, i < L.W → α (e₁ + i) = true) ∧
          (∀ i, i < L.W → α (e₂ + i) = true)) → α (L.yAt (j + 1)) = true) := by
  rw [chainClause, eval_clauseQBF_iff]
  have hneg₁ := eval_negRange α L.W e₁
  have hneg₂ := eval_negRange α L.W e₂
  constructor
  · rintro ⟨l, hl, hv⟩ ⟨hy, h1, h2⟩
    rw [List.mem_append, List.mem_cons, List.mem_append] at hl
    rcases hl with (rfl | hl | hl) | hl
    · rw [eval_litQBF, beq_iff_eq, hy] at hv
      exact absurd hv (by simp)
    · exact absurd h1 (hneg₁.mp ⟨l, hl, hv⟩)
    · exact absurd h2 (hneg₂.mp ⟨l, hl, hv⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      rw [eval_litQBF, beq_iff_eq] at hv
      exact hv
  · intro h
    by_cases hy : α (L.yAt j) = true
    · by_cases h1 : ∀ i, i < L.W → α (e₁ + i) = true
      · by_cases h2 : ∀ i, i < L.W → α (e₂ + i) = true
        · refine ⟨(true, L.yAt (j + 1)),
            List.mem_append.mpr (Or.inr List.mem_cons_self), ?_⟩
          rw [eval_litQBF, beq_iff_eq]
          exact h ⟨hy, h1, h2⟩
        · obtain ⟨l, hl, hv⟩ := hneg₂.mpr h2
          exact ⟨l, List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _
            (List.mem_append.mpr (Or.inr hl)))), hv⟩
      · obtain ⟨l, hl, hv⟩ := hneg₁.mpr h1
        exact ⟨l, List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inl hl)))), hv⟩
    · refine ⟨(false, L.yAt j),
        List.mem_append.mpr (Or.inl List.mem_cons_self), ?_⟩
      rw [eval_litQBF, beq_iff_eq]
      exact Bool.eq_false_iff.mpr hy

theorem chainClause_length (j e₁ e₂ : ℕ) :
    (L.chainClause j e₁ e₂).length = 2 * L.W + 2 := by
  rw [chainClause, List.length_append, List.length_cons, List.length_append,
    negRange_length, negRange_length, List.length_cons, List.length_nil]
  ring

theorem chainClause_getElem?_zero (j e₁ e₂ : ℕ) :
    (L.chainClause j e₁ e₂)[0]? = some (false, L.yAt j) := by
  rw [chainClause]
  rfl

theorem chainClause_getElem?_first (j e₁ e₂ i : ℕ) (hi : i < L.W) :
    (L.chainClause j e₁ e₂)[i + 1]? = some (false, e₁ + i) := by
  rw [chainClause, List.getElem?_append_left (by
      rw [List.length_cons, List.length_append, negRange_length, negRange_length]
      omega),
    List.getElem?_cons_succ,
    List.getElem?_append_left (by rw [negRange_length]; exact hi),
    negRange_getElem? _ _ _ hi]

theorem chainClause_getElem?_second (j e₁ e₂ i : ℕ) (hi : i < L.W) :
    (L.chainClause j e₁ e₂)[L.W + 1 + i]? = some (false, e₂ + i) := by
  have hrw : L.W + 1 + i = (L.W + i) + 1 := by omega
  rw [chainClause, hrw, List.getElem?_append_left (by
      rw [List.length_cons, List.length_append, negRange_length, negRange_length]
      omega),
    List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [negRange_length]; omega), negRange_length]
  have hi' : L.W + i - L.W = i := by omega
  rw [hi', negRange_getElem? _ _ _ hi]

theorem chainClause_getElem?_last (j e₁ e₂ : ℕ) :
    (L.chainClause j e₁ e₂)[2 * L.W + 1]? = some (true, L.yAt (j + 1)) := by
  rw [chainClause, List.getElem?_append_right (by
      rw [List.length_cons, List.length_append, negRange_length, negRange_length]
      omega), List.length_cons, List.length_append, negRange_length, negRange_length]
  have hrw : 2 * L.W + 1 - (L.W + L.W + 1) = 0 := by omega
  rw [hrw]
  rfl

/-- **The chain clause as an indexed family.** -/
theorem chainClause_eq_map (j e₁ e₂ : ℕ) :
    L.chainClause j e₁ e₂
      = (List.range (2 * L.W + 2)).map fun i =>
          if i = 0 then ((false, L.yAt j) : CLit)
          else if i - 1 < L.W then (false, e₁ + (i - 1))
          else if i - 1 - L.W < L.W then (false, e₂ + (i - 1 - L.W))
          else (true, L.yAt (j + 1)) := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < 2 * L.W + 2
  · have hr : i < (List.range (2 * L.W + 2)).length := by
      rw [List.length_range]
      exact hi
    rw [List.getElem?_map, List.getElem?_eq_getElem hr, List.getElem_range]
    simp only [Option.map_some]
    by_cases c0 : i = 0
    · subst c0
      rw [if_pos rfl]
      exact L.chainClause_getElem?_zero j e₁ e₂
    · rw [if_neg c0]
      by_cases c1 : i - 1 < L.W
      · rw [if_pos c1]
        have h := L.chainClause_getElem?_first j e₁ e₂ (i - 1) c1
        rw [show i - 1 + 1 = i from by omega] at h
        exact h
      · rw [if_neg c1]
        by_cases c2 : i - 1 - L.W < L.W
        · rw [if_pos c2]
          have h := L.chainClause_getElem?_second j e₁ e₂ (i - 1 - L.W) c2
          rw [show L.W + 1 + (i - 1 - L.W) = i from by omega] at h
          exact h
        · rw [if_neg c2]
          have h := L.chainClause_getElem?_last j e₁ e₂
          rw [show 2 * L.W + 1 = i from by omega] at h
          exact h
  · rw [List.getElem?_eq_none (by rw [L.chainClause_length j e₁ e₂]; omega),
      List.getElem?_eq_none (by rw [List.length_map, List.length_range]; omega)]

/-- What one level's clauses say. -/
def LevelHolds (validC : ℕ → List (List CLit)) (j : ℕ) (α : ℕ → Bool) : Prop :=
  (α (L.yAt j) = true → eval α (cnfQBF (validC (L.mid j))) = true) ∧
  (∀ i, i < L.W → α (L.eUA j + i) = (α (L.uBlk j + i) == α (L.leftOf j + i))) ∧
  (∀ i, i < L.W → α (L.eVM j + i) = (α (L.vBlk j + i) == α (L.mid j + i))) ∧
  (∀ i, i < L.W → α (L.eUM j + i) = (α (L.uBlk j + i) == α (L.mid j + i))) ∧
  (∀ i, i < L.W → α (L.eVB j + i) = (α (L.vBlk j + i) == α (L.rightOf j + i))) ∧
  ((α (L.yAt j) = true ∧ (∀ i, i < L.W → α (L.eUA j + i) = true) ∧
      (∀ i, i < L.W → α (L.eVM j + i) = true)) → α (L.yAt (j + 1)) = true) ∧
  ((α (L.yAt j) = true ∧ (∀ i, i < L.W → α (L.eUM j + i) = true) ∧
      (∀ i, i < L.W → α (L.eVB j + i) = true)) → α (L.yAt (j + 1)) = true)

theorem eval_levelClauses (α : ℕ → Bool) (j : ℕ) :
    eval α (cnfQBF (L.levelClauses validC j)) = true ↔ L.LevelHolds validC j α := by
  rw [levelClauses, eval_cnfQBF_append, eval_cnfQBF_append, eval_cnfQBF_append,
    eval_cnfQBF_append, eval_cnfQBF_append, eval_disjLit, eval_eqAuxCNF, eval_eqAuxCNF,
    eval_eqAuxCNF, eval_eqAuxCNF, eval_litQBF]
  have hpair : eval α (cnfQBF [L.chainClause j (L.eUA j) (L.eVM j),
      L.chainClause j (L.eUM j) (L.eVB j)]) = true ↔
      (eval α (clauseQBF (L.chainClause j (L.eUA j) (L.eVM j))) = true ∧
        eval α (clauseQBF (L.chainClause j (L.eUM j) (L.eVB j))) = true) := by
    rw [eval_cnfQBF_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rw [hpair, eval_chainClause, eval_chainClause]
  rw [LevelHolds]
  have hy : ((α (L.yAt j) == false) = true) ↔ ¬ (α (L.yAt j) = true) := by
    cases hb : α (L.yAt j) <;> simp
  rw [show (((α (L.yAt j) == false) = true ∨ eval α (cnfQBF (validC (L.mid j))) = true) ↔
      (α (L.yAt j) = true → eval α (cnfQBF (validC (L.mid j))) = true)) from by
    rw [hy]
    tauto]
  tauto

/-! ## The nested reading of the same clauses -/

variable (baseC : ℕ → ℕ → ℕ → List (List CLit))

/-- The formula from level `j` on, with `m` levels left: choose the midpoint, let the verifier
choose the two blocks, then choose the equality bits and the next chain bit. This is the flat
matrix under the flat prefix, read as a nest so it can be inducted on. -/
noncomputable def tailQBF : ℕ → ℕ → QBF
  | 0, j =>
      toQBF (blockQ false L.scr L.Ws)
        (cnfQBF (disjLit (false, L.yAt j) (baseC (L.leftOf j) (L.rightOf j) L.scr)))
  | m + 1, j =>
      toQBF (blockQ false (L.mid j) L.W)
        (toQBF (blockQ true (L.uBlk j) L.W)
          (toQBF (blockQ true (L.vBlk j) L.W)
            (toQBF (blockQ false (L.eUA j) L.W)
              (toQBF (blockQ false (L.eVM j) L.W)
                (toQBF (blockQ false (L.eUM j) L.W)
                  (toQBF (blockQ false (L.eVB j) L.W)
                    (toQBF (blockQ false (L.yAt (j + 1)) 1)
                      (conj (cnfQBF (L.levelClauses validC j))
                        (tailQBF m (j + 1))))))))))

theorem tailQBF_zero (j : ℕ) :
    L.tailQBF validC baseC 0 j
      = toQBF (blockQ false L.scr L.Ws)
        (cnfQBF (disjLit (false, L.yAt j) (baseC (L.leftOf j) (L.rightOf j) L.scr))) := rfl

theorem tailQBF_succ (m j : ℕ) :
    L.tailQBF validC baseC (m + 1) j
      = toQBF (blockQ false (L.mid j) L.W)
          (toQBF (blockQ true (L.uBlk j) L.W)
            (toQBF (blockQ true (L.vBlk j) L.W)
              (toQBF (blockQ false (L.eUA j) L.W)
                (toQBF (blockQ false (L.eVM j) L.W)
                  (toQBF (blockQ false (L.eUM j) L.W)
                    (toQBF (blockQ false (L.eVB j) L.W)
                      (toQBF (blockQ false (L.yAt (j + 1)) 1)
                        (conj (cnfQBF (L.levelClauses validC j))
                          (L.tailQBF validC baseC m (j + 1)))))))))) := rfl

/-! ## The flat reading of the same clauses -/

/-- The quantifiers introduced by one level, in flat order. -/
noncomputable def levelQs (j : ℕ) : Prefix :=
  blockQ false (L.mid j) L.W ++ (blockQ true (L.uBlk j) L.W ++
    (blockQ true (L.vBlk j) L.W ++ blockQ false (L.eUA j) (4 * L.W + 1)))

/-- The quantifiers of the levels from `j` on, then the scratch block. -/
noncomputable def tailPrefix : ℕ → ℕ → Prefix
  | 0, _ => blockQ false L.scr L.Ws
  | m + 1, j => L.levelQs j ++ tailPrefix m (j + 1)

/-- The clauses of the levels from `j` on, then the base clauses. -/
noncomputable def tailClauses : ℕ → ℕ → List (List CLit)
  | 0, j => disjLit (false, L.yAt j) (baseC (L.leftOf j) (L.rightOf j) L.scr)
  | m + 1, j => L.levelClauses validC j ++ tailClauses m (j + 1)

theorem tailPrefix_succ (m j : ℕ) :
    L.tailPrefix (m + 1) j = L.levelQs j ++ L.tailPrefix m (j + 1) := rfl

theorem tailClauses_succ (m j : ℕ) :
    L.tailClauses validC baseC (m + 1) j
      = L.levelClauses validC j ++ L.tailClauses validC baseC m (j + 1) := rfl

theorem mem_levelQs (j : ℕ) (q : Bool × ℕ) (hq : q ∈ L.levelQs j) :
    L.levStart j ≤ q.2 ∧ q.2 < L.levStart (j + 1) := by
  have h1 : L.mid j = L.levStart j := rfl
  have h2 : L.uBlk j = L.levStart j + L.W := rfl
  have h3 : L.vBlk j = L.levStart j + 2 * L.W := rfl
  have h4 : L.eUA j = L.levStart j + 3 * L.W := rfl
  have h5 : L.levStart (j + 1) = L.levStart j + (7 * L.W + 1) := by
    rw [L.levStart_succ j, levelSize]
  rw [levelQs] at hq
  rcases List.mem_append.mp hq with h | h
  · have := SavitchData.mem_blockQ _ _ _ _ h; omega
  · rcases List.mem_append.mp h with h | h
    · have := SavitchData.mem_blockQ _ _ _ _ h; omega
    · rcases List.mem_append.mp h with h | h
      · have := SavitchData.mem_blockQ _ _ _ _ h; omega
      · have := SavitchData.mem_blockQ _ _ _ _ h; omega

theorem mem_tailPrefix : ∀ (m j : ℕ), L.levStart j + L.levelSize * m ≤ L.scr →
    ∀ q ∈ L.tailPrefix m j, L.levStart j ≤ q.2
  | 0, j, hs, q, hq => by
      rw [Nat.mul_zero] at hs
      rw [tailPrefix] at hq
      have := SavitchData.mem_blockQ _ _ _ _ hq
      omega
  | m + 1, j, hs, q, hq => by
      have hstep : L.levStart (j + 1) + L.levelSize * m ≤ L.scr := by
        rw [L.levStart_succ j]
        have : L.levelSize * (m + 1) = L.levelSize + L.levelSize * m := by ring
        omega
      have hmono : L.levStart j ≤ L.levStart (j + 1) := by
        rw [L.levStart_succ j]
        omega
      rw [tailPrefix] at hq
      rcases List.mem_append.mp hq with h | h
      · exact (L.mem_levelQs j q h).1
      · exact le_trans hmono (mem_tailPrefix m (j + 1) hstep q h)

theorem mem_negRange_vars (W off : ℕ) (l : CLit) (hl : l ∈ negRange W off) :
    ∃ i, i < W ∧ l.2 = off + i := by
  rw [negRange, List.mem_map] at hl
  obtain ⟨i, hi, rfl⟩ := hl
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem mem_chainClause_vars (j e₁ e₂ : ℕ) (l : CLit) (hl : l ∈ L.chainClause j e₁ e₂) :
    l.2 = L.yAt j ∨ l.2 = L.yAt (j + 1) ∨
      (∃ i, i < L.W ∧ l.2 = e₁ + i) ∨ (∃ i, i < L.W ∧ l.2 = e₂ + i) := by
  rw [chainClause] at hl
  rcases List.mem_append.mp hl with h | h
  · rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · rcases List.mem_append.mp h with h | h
      · exact Or.inr (Or.inr (Or.inl (mem_negRange_vars _ _ _ h)))
      · exact Or.inr (Or.inr (Or.inr (mem_negRange_vars _ _ _ h)))
  · rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr (Or.inl rfl)
    · exact absurd h (by simp)

theorem mem_levelClauses_vars (j : ℕ)
    (hvarsC : ∀ (off : ℕ), ∀ c ∈ validC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W)
    (hl : L.leftOf j + L.W ≤ L.levStart j) (hr : L.rightOf j + L.W ≤ L.levStart j) :
    ∀ c ∈ L.levelClauses validC j, ∀ l ∈ c, l.2 < L.levStart (j + 1) := by
  have h1 : L.mid j = L.levStart j := rfl
  have h2 : L.uBlk j = L.levStart j + L.W := rfl
  have h3 : L.vBlk j = L.levStart j + 2 * L.W := rfl
  have h4 : L.eUA j = L.levStart j + 3 * L.W := rfl
  have h5 : L.eVM j = L.levStart j + 4 * L.W := rfl
  have h6 : L.eUM j = L.levStart j + 5 * L.W := rfl
  have h7 : L.eVB j = L.levStart j + 6 * L.W := rfl
  have h8 : L.levStart (j + 1) = L.levStart j + (7 * L.W + 1) := by
    rw [L.levStart_succ j, levelSize]
  have h9 : L.yAt j < L.levStart j := L.yAt_lt_levStart j
  have h10 : L.yAt (j + 1) = L.levStart j + 7 * L.W := L.yAt_succ j
  intro c hc l hl'
  have key : (∃ i, i < L.W ∧ (l.2 = L.eUA j + i ∨ l.2 = L.eVM j + i ∨ l.2 = L.eUM j + i ∨
        l.2 = L.eVB j + i ∨ l.2 = L.uBlk j + i ∨ l.2 = L.vBlk j + i ∨ l.2 = L.mid j + i ∨
        l.2 = L.leftOf j + i ∨ l.2 = L.rightOf j + i)) ∨
      l.2 = L.yAt j ∨ l.2 = L.yAt (j + 1) ∨ (L.mid j ≤ l.2 ∧ l.2 < L.mid j + L.W) := by
    rw [levelClauses, List.mem_append] at hc
    rcases hc with h | h
    · rcases mem_disjLits_vars _ _ c h l hl' with h' | ⟨c', hc', hl''⟩
      · rw [List.mem_cons] at h'
        rcases h' with rfl | h'
        · exact Or.inr (Or.inl rfl)
        · simp at h'
      · exact Or.inr (Or.inr (Or.inr (hvarsC (L.mid j) c' hc' l hl'')))
    · rw [List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_append] at h
        rcases h with h | h
        · rcases mem_eqAuxCNF_vars _ _ _ _ c h l hl' with
            ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩ <;> exact Or.inl ⟨i, hi, by tauto⟩
        · rcases mem_eqAuxCNF_vars _ _ _ _ c h l hl' with
            ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩ <;> exact Or.inl ⟨i, hi, by tauto⟩
      · rw [List.mem_append] at h
        rcases h with h | h
        · rw [List.mem_append] at h
          rcases h with h | h
          · rcases mem_eqAuxCNF_vars _ _ _ _ c h l hl' with
              ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩ <;> exact Or.inl ⟨i, hi, by tauto⟩
          · rcases mem_eqAuxCNF_vars _ _ _ _ c h l hl' with
              ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩ <;> exact Or.inl ⟨i, hi, by tauto⟩
        · rw [List.mem_cons, List.mem_cons] at h
          rcases h with rfl | rfl | h
          · rcases L.mem_chainClause_vars j (L.eUA j) (L.eVM j) l hl' with
              hv | hv | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩
            · exact Or.inr (Or.inl hv)
            · exact Or.inr (Or.inr (Or.inl hv))
            · exact Or.inl ⟨i, hi, by tauto⟩
            · exact Or.inl ⟨i, hi, by tauto⟩
          · rcases L.mem_chainClause_vars j (L.eUM j) (L.eVB j) l hl' with
              hv | hv | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩
            · exact Or.inr (Or.inl hv)
            · exact Or.inr (Or.inr (Or.inl hv))
            · exact Or.inl ⟨i, hi, by tauto⟩
            · exact Or.inl ⟨i, hi, by tauto⟩
          · simp at h
  clear hc hl'
  rcases key with ⟨i, hi, hv⟩ | hv | hv | hv <;> omega

theorem tailQBF_succ_flat (m j : ℕ) :
    L.tailQBF validC baseC (m + 1) j
      = toQBF (L.levelQs j) (conj (cnfQBF (L.levelClauses validC j))
          (L.tailQBF validC baseC m (j + 1))) := by
  have hq : blockQ false (L.eUA j) (4 * L.W + 1) =
      blockQ false (L.eUA j) L.W ++ (blockQ false (L.eVM j) L.W ++
        (blockQ false (L.eUM j) L.W ++ (blockQ false (L.eVB j) L.W ++
          blockQ false (L.yAt (j + 1)) 1))) := by
    rw [L.yAt_succ_eq j, L.eVB_eq j, L.eUM_eq j, L.eVM_eq j, blockQ_append, blockQ_append,
      blockQ_append, blockQ_append]
    congr 1
    omega
  rw [L.tailQBF_succ validC baseC m j, levelQs, toQBF_append, toQBF_append, toQBF_append,
    hq, toQBF_append, toQBF_append, toQBF_append, toQBF_append]

/-- **The nest and the flat form agree.** -/
theorem eval_tailQBF_flat
    (hvarsC : ∀ (off : ℕ), ∀ c ∈ validC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W) :
    ∀ (m j : ℕ), L.leftOf j + L.W ≤ L.levStart j → L.rightOf j + L.W ≤ L.levStart j →
      L.levStart j + L.levelSize * m ≤ L.scr → ∀ α : ℕ → Bool,
        eval α (L.tailQBF validC baseC m j) = true ↔
          eval α (toQBF (L.tailPrefix m j)
            (cnfQBF (L.tailClauses validC baseC m j))) = true
  | 0, _, _, _, _, _ => Iff.rfl
  | m + 1, j, hl, hr, hs, α => by
      have hstep : L.levStart (j + 1) + L.levelSize * m ≤ L.scr := by
        rw [L.levStart_succ j]
        have : L.levelSize * (m + 1) = L.levelSize + L.levelSize * m := by ring
        omega
      have hl' : L.leftOf (j + 1) + L.W ≤ L.levStart (j + 1) := by
        rw [L.leftOf_succ j, L.levStart_succ j, uBlk, levelSize]
        omega
      have hr' : L.rightOf (j + 1) + L.W ≤ L.levStart (j + 1) := by
        rw [L.rightOf_succ j, L.levStart_succ j, vBlk, levelSize]
        omega
      have hfv : ∀ q ∈ L.tailPrefix m (j + 1),
          q.2 ∉ freeVars (cnfQBF (L.levelClauses validC j)) := by
        intro q hq hmem
        obtain ⟨c, hc, l, hl'', heq⟩ := mem_freeVars_cnfQBF _ _ hmem
        have h1 := L.mem_levelClauses_vars validC j hvarsC hl hr c hc l hl''
        have h2 := L.mem_tailPrefix m (j + 1) hstep q hq
        omega
      have hcong : ∀ δ : ℕ → Bool,
          eval δ (conj (cnfQBF (L.levelClauses validC j))
              (L.tailQBF validC baseC m (j + 1)))
            = eval δ (toQBF (L.tailPrefix m (j + 1))
              (cnfQBF (L.tailClauses validC baseC (m + 1) j))) := by
        intro δ
        rw [Bool.eq_iff_iff, eval_conj, Bool.and_eq_true,
          eval_tailQBF_flat hvarsC m (j + 1) hl' hr' hstep δ, tailClauses_succ,
          SavitchData.eval_toQBF_congr (L.tailPrefix m (j + 1))
            (cnfQBF (L.levelClauses validC j ++ L.tailClauses validC baseC m (j + 1)))
            (conj (cnfQBF (L.levelClauses validC j))
              (cnfQBF (L.tailClauses validC baseC m (j + 1))))
            (fun γ => by rw [Bool.eq_iff_iff, eval_conj, Bool.and_eq_true, eval_cnfQBF_append])
            δ,
          eval_toQBF_conj_left _ _ _ _ hfv]
      rw [L.tailQBF_succ_flat validC baseC m j, tailPrefix_succ, toQBF_append,
        SavitchData.eval_toQBF_congr (L.levelQs j) _ _ hcong α]

/-! ## Indexing one level -/

section LevelIndex

variable (VC : ℕ) (hVC : ∀ off, (validC off).length = VC) (j : ℕ)

/-- One level's clauses, right-associated. -/
theorem levelClauses_flat :
    L.levelClauses validC j
      = disjLit (false, L.yAt j) (validC (L.mid j)) ++
        (eqAuxCNF L.W (L.eUA j) (L.uBlk j) (L.leftOf j) ++
          (eqAuxCNF L.W (L.eVM j) (L.vBlk j) (L.mid j) ++
            (eqAuxCNF L.W (L.eUM j) (L.uBlk j) (L.mid j) ++
              (eqAuxCNF L.W (L.eVB j) (L.vBlk j) (L.rightOf j) ++
                [L.chainClause j (L.eUA j) (L.eVM j),
                  L.chainClause j (L.eUM j) (L.eVB j)])))) := by
  rw [levelClauses]
  simp only [List.append_assoc]

include hVC

theorem levelClauses_length : (L.levelClauses validC j).length = VC + 4 * (L.W * 4) + 2 := by
  rw [levelClauses_flat]
  simp only [List.length_append, disjLit_length, hVC, eqAuxCNF_length, List.length_cons,
    List.length_nil]
  ring

variable {j}

theorem levelClauses_getElem?_valid {p : ℕ} (hp : p < VC) :
    (L.levelClauses validC j)[p]?
      = ((validC (L.mid j))[p]?).map fun c => (false, L.yAt j) :: c := by
  have h0 : (disjLit (false, L.yAt j) (validC (L.mid j))).length = VC := by
    rw [disjLit_length, hVC]
  rw [levelClauses_flat, List.getElem?_append_left (by rw [h0]; exact hp), disjLit_getElem?]

theorem levelClauses_getElem?_eqUA {p : ℕ} (h₁ : VC ≤ p) (h₂ : p < VC + L.W * 4) :
    (L.levelClauses validC j)[p]?
      = (eqAuxCNF L.W (L.eUA j) (L.uBlk j) (L.leftOf j))[p - VC]? := by
  have h0 : (disjLit (false, L.yAt j) (validC (L.mid j))).length = VC := by
    rw [disjLit_length, hVC]
  have e1 : (eqAuxCNF L.W (L.eUA j) (L.uBlk j) (L.leftOf j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  rw [levelClauses_flat, List.getElem?_append_right (by rw [h0]; exact h₁), h0,
    List.getElem?_append_left (by rw [e1]; omega)]

theorem levelClauses_getElem?_eqVM {p : ℕ} (h₁ : VC + L.W * 4 ≤ p)
    (h₂ : p < VC + 2 * (L.W * 4)) :
    (L.levelClauses validC j)[p]?
      = (eqAuxCNF L.W (L.eVM j) (L.vBlk j) (L.mid j))[p - VC - L.W * 4]? := by
  have h0 : (disjLit (false, L.yAt j) (validC (L.mid j))).length = VC := by
    rw [disjLit_length, hVC]
  have e1 : (eqAuxCNF L.W (L.eUA j) (L.uBlk j) (L.leftOf j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e2 : (eqAuxCNF L.W (L.eVM j) (L.vBlk j) (L.mid j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  rw [levelClauses_flat, List.getElem?_append_right (by rw [h0]; omega), h0,
    List.getElem?_append_right (by rw [e1]; omega), e1,
    List.getElem?_append_left (by rw [e2]; omega)]

theorem levelClauses_getElem?_eqUM {p : ℕ} (h₁ : VC + 2 * (L.W * 4) ≤ p)
    (h₂ : p < VC + 3 * (L.W * 4)) :
    (L.levelClauses validC j)[p]?
      = (eqAuxCNF L.W (L.eUM j) (L.uBlk j) (L.mid j))[p - VC - 2 * (L.W * 4)]? := by
  have h0 : (disjLit (false, L.yAt j) (validC (L.mid j))).length = VC := by
    rw [disjLit_length, hVC]
  have e1 : (eqAuxCNF L.W (L.eUA j) (L.uBlk j) (L.leftOf j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e2 : (eqAuxCNF L.W (L.eVM j) (L.vBlk j) (L.mid j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e3 : (eqAuxCNF L.W (L.eUM j) (L.uBlk j) (L.mid j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  rw [levelClauses_flat, List.getElem?_append_right (by rw [h0]; omega), h0,
    List.getElem?_append_right (by rw [e1]; omega), e1,
    List.getElem?_append_right (by rw [e2]; omega), e2,
    List.getElem?_append_left (by rw [e3]; omega)]
  congr 1
  omega

theorem levelClauses_getElem?_eqVB {p : ℕ} (h₁ : VC + 3 * (L.W * 4) ≤ p)
    (h₂ : p < VC + 4 * (L.W * 4)) :
    (L.levelClauses validC j)[p]?
      = (eqAuxCNF L.W (L.eVB j) (L.vBlk j) (L.rightOf j))[p - VC - 3 * (L.W * 4)]? := by
  have h0 : (disjLit (false, L.yAt j) (validC (L.mid j))).length = VC := by
    rw [disjLit_length, hVC]
  have e1 : (eqAuxCNF L.W (L.eUA j) (L.uBlk j) (L.leftOf j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e2 : (eqAuxCNF L.W (L.eVM j) (L.vBlk j) (L.mid j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e3 : (eqAuxCNF L.W (L.eUM j) (L.uBlk j) (L.mid j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e4 : (eqAuxCNF L.W (L.eVB j) (L.vBlk j) (L.rightOf j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  rw [levelClauses_flat, List.getElem?_append_right (by rw [h0]; omega), h0,
    List.getElem?_append_right (by rw [e1]; omega), e1,
    List.getElem?_append_right (by rw [e2]; omega), e2,
    List.getElem?_append_right (by rw [e3]; omega), e3,
    List.getElem?_append_left (by rw [e4]; omega)]
  congr 1
  omega

theorem levelClauses_getElem?_chain (p : ℕ) (h₁ : VC + 4 * (L.W * 4) ≤ p) :
    (L.levelClauses validC j)[p]?
      = [L.chainClause j (L.eUA j) (L.eVM j),
          L.chainClause j (L.eUM j) (L.eVB j)][p - VC - 4 * (L.W * 4)]? := by
  have h0 : (disjLit (false, L.yAt j) (validC (L.mid j))).length = VC := by
    rw [disjLit_length, hVC]
  have e1 : (eqAuxCNF L.W (L.eUA j) (L.uBlk j) (L.leftOf j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e2 : (eqAuxCNF L.W (L.eVM j) (L.vBlk j) (L.mid j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e3 : (eqAuxCNF L.W (L.eUM j) (L.uBlk j) (L.mid j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  have e4 : (eqAuxCNF L.W (L.eVB j) (L.vBlk j) (L.rightOf j)).length = L.W * 4 :=
    eqAuxCNF_length _ _ _ _
  rw [levelClauses_flat, List.getElem?_append_right (by rw [h0]; omega), h0,
    List.getElem?_append_right (by rw [e1]; omega), e1,
    List.getElem?_append_right (by rw [e2]; omega), e2,
    List.getElem?_append_right (by rw [e3]; omega), e3,
    List.getElem?_append_right (by rw [e4]; omega), e4]
  congr 1
  omega

end LevelIndex

/-! ## Indexing the clause list -/

theorem tailClauses_length (LC BC : ℕ)
    (hLC : ∀ j, (L.levelClauses validC j).length = LC)
    (hBC : ∀ u v s, (baseC u v s).length = BC) :
    ∀ (m j : ℕ), (L.tailClauses validC baseC m j).length = LC * m + BC
  | 0, j => by
      rw [tailClauses, disjLit, disjLits, List.length_map, hBC]
      simp
  | m + 1, j => by
      rw [tailClauses_succ, List.length_append, hLC,
        tailClauses_length LC BC hLC hBC m (j + 1)]
      ring

/-- **A clause inside the levels**: level `t / LC`, position `t % LC`. -/
theorem tailClauses_getElem?_lev (LC : ℕ) (hpos : 0 < LC)
    (hLC : ∀ j, (L.levelClauses validC j).length = LC) :
    ∀ (m j t : ℕ), t < LC * m →
      (L.tailClauses validC baseC m j)[t]?
        = (L.levelClauses validC (j + t / LC))[t % LC]?
  | 0, _, t, ht => by simp at ht
  | m + 1, j, t, ht => by
      rw [tailClauses_succ]
      by_cases hlt : t < LC
      · rw [List.getElem?_append_left (by rw [hLC]; exact hlt), Nat.div_eq_of_lt hlt,
          Nat.mod_eq_of_lt hlt, Nat.add_zero]
      · have hge : LC ≤ t := by omega
        have hsub : t - LC + LC = t := by omega
        have hdiv : t / LC = (t - LC) / LC + 1 := by
          conv_lhs => rw [← hsub]
          rw [Nat.add_div_right _ hpos]
        have hmod : t % LC = (t - LC) % LC := by
          conv_lhs => rw [← hsub]
          rw [Nat.add_mod_right]
        have hlt' : t - LC < LC * m := by
          have : LC * (m + 1) = LC * m + LC := by ring
          omega
        rw [List.getElem?_append_right (by rw [hLC]; omega), hLC,
          tailClauses_getElem?_lev LC hpos hLC m (j + 1) (t - LC) hlt', hdiv, hmod]
        congr 2
        omega

/-- **A clause after the levels** is a base clause. -/
theorem tailClauses_getElem?_base (LC : ℕ)
    (hLC : ∀ j, (L.levelClauses validC j).length = LC) :
    ∀ (m j t : ℕ), LC * m ≤ t →
      (L.tailClauses validC baseC m j)[t]?
        = (disjLit (false, L.yAt (j + m))
            (baseC (L.leftOf (j + m)) (L.rightOf (j + m)) L.scr))[t - LC * m]?
  | 0, j, t, _ => by
      rw [tailClauses]
      simp
  | m + 1, j, t, ht => by
      have hexp : LC * (m + 1) = LC + LC * m := by ring
      have h1 : j + 1 + m = j + (m + 1) := by omega
      have h2 : t - LC - LC * m = t - LC * (m + 1) := by omega
      rw [tailClauses_succ, List.getElem?_append_right (by rw [hLC]; omega), hLC,
        tailClauses_getElem?_base LC hLC m (j + 1) (t - LC) (by omega), h1, h2]

/-! ## The whole prefix -/

/-- The full quantifier prefix: the two endpoints, the first chain bit, then every level. -/
noncomputable def fullPrefix : Prefix :=
  blockQ false 0 L.W ++ (blockQ false L.bStart L.W ++
    (blockQ false L.y0 1 ++ L.tailPrefix L.n 0))

theorem levelQs_length (j : ℕ) : (L.levelQs j).length = L.levelSize := by
  rw [levelQs, List.length_append, List.length_append, List.length_append,
    blockQ_length, blockQ_length, blockQ_length, blockQ_length, levelSize]
  ring

theorem tailPrefix_length : ∀ (m j : ℕ), (L.tailPrefix m j).length = L.levelSize * m + L.Ws
  | 0, _ => by
      rw [tailPrefix, blockQ_length, Nat.mul_zero, Nat.zero_add]
  | m + 1, j => by
      rw [tailPrefix, List.length_append, L.levelQs_length j, tailPrefix_length m (j + 1)]
      ring

theorem fullPrefix_length : L.fullPrefix.length = L.nvar := by
  rw [fullPrefix, List.length_append, List.length_append, List.length_append, blockQ_length,
    blockQ_length, blockQ_length, L.tailPrefix_length L.n 0, nvar, scr]
  ring

theorem listed_levelQs (j : ℕ) (hj : j < L.n) :
    SavitchData.Listed L.flatKind (L.levStart j) (L.levelQs j) := by
  have h1 : SavitchData.Listed L.flatKind (L.mid j) (blockQ false (L.mid j) L.W) :=
    SavitchData.listed_blockQ fun i hi => L.flatKind_mid j i hj hi
  have h2 : SavitchData.Listed L.flatKind (L.uBlk j) (blockQ true (L.uBlk j) L.W) :=
    SavitchData.listed_blockQ fun i hi => L.flatKind_uBlk j i hj hi
  have h3 : SavitchData.Listed L.flatKind (L.vBlk j) (blockQ true (L.vBlk j) L.W) :=
    SavitchData.listed_blockQ fun i hi => L.flatKind_vBlk j i hj hi
  have h4 : SavitchData.Listed L.flatKind (L.eUA j) (blockQ false (L.eUA j) (4 * L.W + 1)) :=
    SavitchData.listed_blockQ fun i hi => L.flatKind_eblk j i hj hi
  rw [levelQs]
  refine SavitchData.Listed.append h1 ?_
  rw [blockQ_length, show L.levStart j + L.W = L.uBlk j from rfl]
  refine SavitchData.Listed.append h2 ?_
  rw [blockQ_length, show L.uBlk j + L.W = L.vBlk j from (L.vBlk_eq j).symm]
  refine SavitchData.Listed.append h3 ?_
  rw [blockQ_length, show L.vBlk j + L.W = L.eUA j from (L.eUA_eq j).symm]
  exact h4

theorem listed_tailPrefix : ∀ (m j : ℕ), j + m ≤ L.n → L.levStart j + L.levelSize * m = L.scr →
    SavitchData.Listed L.flatKind (L.levStart j) (L.tailPrefix m j)
  | 0, j, _, hs => by
      rw [Nat.mul_zero, Nat.add_zero] at hs
      rw [tailPrefix, hs]
      exact SavitchData.listed_blockQ fun i _ => L.flatKind_scr _ (by omega)
  | m + 1, j, hj, hs => by
      have hstep : L.levStart (j + 1) + L.levelSize * m = L.scr := by
        rw [L.levStart_succ j]
        have : L.levelSize * (m + 1) = L.levelSize + L.levelSize * m := by ring
        omega
      rw [tailPrefix]
      refine SavitchData.Listed.append (L.listed_levelQs j (by omega)) ?_
      rw [L.levelQs_length j, ← L.levStart_succ j]
      exact listed_tailPrefix m (j + 1) (by omega) hstep

theorem listed_fullPrefix : SavitchData.Listed L.flatKind 0 L.fullPrefix := by
  have hs : L.levStart 0 + L.levelSize * L.n = L.scr := by
    rw [levStart, scr]
    ring
  have h1 : SavitchData.Listed L.flatKind 0 (blockQ false 0 L.W) :=
    SavitchData.listed_blockQ fun i hi => L.flatKind_below _ (by omega)
  have h2 : SavitchData.Listed L.flatKind L.bStart (blockQ false L.bStart L.W) :=
    SavitchData.listed_blockQ fun i hi => L.flatKind_below _ (by rw [bStart]; omega)
  have h3 : SavitchData.Listed L.flatKind L.y0 (blockQ false L.y0 1) :=
    SavitchData.listed_blockQ fun i hi => L.flatKind_below _ (by rw [y0]; omega)
  rw [fullPrefix]
  refine SavitchData.Listed.append h1 ?_
  rw [blockQ_length, Nat.zero_add]
  refine SavitchData.Listed.append h2 ?_
  rw [blockQ_length, show L.W + L.W = L.y0 from by rw [y0]; ring]
  refine SavitchData.Listed.append h3 ?_
  rw [blockQ_length, show L.y0 + 1 = L.levStart 0 from by rw [y0, levStart]; ring]
  exact L.listed_tailPrefix L.n 0 (by omega) hs

/-- **The prefix is the flat one**: the quantifiers name `0, …, nvar - 1` in order. -/
theorem fullPrefix_eq : L.fullPrefix = L.flatPrefix :=
  L.listed_fullPrefix.eq_of_length L.flatPrefix_listed
    (by rw [L.fullPrefix_length, L.flatPrefix_length])

/-! ## The base case of the recursion -/

variable {Ws : ℕ} (D : SavitchData L.W Ws)

/-- **The innermost formula is one base step.** -/
theorem eval_tailQBF_zero (hWs : L.Ws = Ws)
    (hbase : ∀ (α : ℕ → Bool) (u v s : ℕ),
      D.Valid (blockOf L.W α u) → D.Valid (blockOf L.W α v) →
      (eval α (cnfQBF (baseC u v s)) = true ↔
        D.Base (blockOf L.W α u) (blockOf L.W α v) (blockOf Ws α s)))
    (j : ℕ) (α : ℕ → Bool)
    (hl : L.leftOf j + L.W ≤ L.scr) (hr : L.rightOf j + L.W ≤ L.scr)
    (hy : L.yAt j < L.scr)
    (hval : α (L.yAt j) = true →
      D.Valid (blockOf L.W α (L.leftOf j)) ∧ D.Valid (blockOf L.W α (L.rightOf j))) :
    eval α (L.tailQBF validC baseC 0 j) = true ↔
      (α (L.yAt j) = true →
        D.ReachPow 0 (blockOf L.W α (L.leftOf j)) (blockOf L.W α (L.rightOf j))) := by
  subst hWs
  rw [tailQBF_zero, toQBF_blockQ_false, eval_exs_iff]
  constructor
  · rintro ⟨β, hβ, h⟩ hyt
    have hlb : blockOf L.W β (L.leftOf j) = blockOf L.W α (L.leftOf j) :=
      blockOf_eq_of_agree L.W α β _ fun i _ hi => hβ i (Or.inl (by omega))
    have hrb : blockOf L.W β (L.rightOf j) = blockOf L.W α (L.rightOf j) :=
      blockOf_eq_of_agree L.W α β _ fun i _ hi => hβ i (Or.inl (by omega))
    have hyb : β (L.yAt j) = α (L.yAt j) := hβ _ (Or.inl hy)
    obtain ⟨hva, hvb⟩ := hval hyt
    rw [eval_disjLit, eval_litQBF] at h
    rcases h with h | h
    · rw [hyb, hyt] at h
      exact absurd h (by simp)
    · rw [hbase β _ _ _ (by rw [hlb]; exact hva) (by rw [hrb]; exact hvb), hlb, hrb] at h
      exact ⟨hva, hvb, _, h⟩
  · intro h
    by_cases hyt : α (L.yAt j) = true
    · obtain ⟨hva, hvb, σ, hσ⟩ := h hyt
      refine ⟨SavitchData.setBlock α L.scr σ, SavitchData.setBlock_agree α L.scr σ, ?_⟩
      have hlb : blockOf L.W (SavitchData.setBlock α L.scr σ) (L.leftOf j)
          = blockOf L.W α (L.leftOf j) :=
        blockOf_eq_of_agree L.W α _ _ fun i _ hi =>
          SavitchData.setBlock_agree α L.scr σ i (by omega)
      have hrb : blockOf L.W (SavitchData.setBlock α L.scr σ) (L.rightOf j)
          = blockOf L.W α (L.rightOf j) :=
        blockOf_eq_of_agree L.W α _ _ fun i _ hi =>
          SavitchData.setBlock_agree α L.scr σ i (by omega)
      rw [eval_disjLit]
      refine Or.inr ?_
      rw [hbase _ _ _ _ (by rw [hlb]; exact hva) (by rw [hrb]; exact hvb), hlb, hrb,
        SavitchData.blockOf_setBlock_self]
      exact hσ
    · refine ⟨α, fun _ _ => rfl, ?_⟩
      rw [eval_disjLit, eval_litQBF]
      exact Or.inl (by
        rw [Bool.eq_false_iff.mpr hyt]
        rfl)

/-! ## The inductive step -/

/-- **One level of the nest is one Savitch halving.** -/
theorem eval_tailQBF_succ (hWs : L.Ws = Ws)
    (hvalidC : ∀ (α : ℕ → Bool) (off : ℕ),
      eval α (cnfQBF (validC off)) = true ↔ D.Valid (blockOf L.W α off))
    (m j : ℕ) (α : ℕ → Bool)
    (hl : L.leftOf j + L.W ≤ L.levStart j) (hr : L.rightOf j + L.W ≤ L.levStart j)
    (hval : α (L.yAt j) = true →
      D.Valid (blockOf L.W α (L.leftOf j)) ∧ D.Valid (blockOf L.W α (L.rightOf j)))
    (IH : ∀ α' : ℕ → Bool,
      (α' (L.yAt (j + 1)) = true →
        D.Valid (blockOf L.W α' (L.uBlk j)) ∧ D.Valid (blockOf L.W α' (L.vBlk j))) →
      (eval α' (L.tailQBF validC baseC m (j + 1)) = true ↔
        (α' (L.yAt (j + 1)) = true →
          D.ReachPow m (blockOf L.W α' (L.uBlk j)) (blockOf L.W α' (L.vBlk j))))) :
    eval α (L.tailQBF validC baseC (m + 1) j) = true ↔
      (α (L.yAt j) = true →
        D.ReachPow (m + 1) (blockOf L.W α (L.leftOf j)) (blockOf L.W α (L.rightOf j))) := by
  subst hWs
  rw [L.tailQBF_succ validC baseC m j, toQBF_blockQ_false, eval_exs_iff]
  simp only [eval_toQBF_blockQ_true_iff, toQBF_blockQ_false, eval_exs_iff, eval_conj,
    Bool.and_eq_true, L.exists_aux_blocks j]
  classical
  have hmid : L.mid j = L.levStart j := rfl
  have hu : L.uBlk j = L.levStart j + L.W := rfl
  have hv : L.vBlk j = L.levStart j + 2 * L.W := rfl
  have he : L.eUA j = L.levStart j + 3 * L.W := rfl
  have he2 : L.eVM j = L.levStart j + 4 * L.W := rfl
  have he3 : L.eUM j = L.levStart j + 5 * L.W := rfl
  have he4 : L.eVB j = L.levStart j + 6 * L.W := rfl
  have hy1 : L.yAt (j + 1) = L.levStart j + 7 * L.W := L.yAt_succ j
  have hyj : L.yAt j < L.levStart j := L.yAt_lt_levStart j
  have bval : ∀ (X : ℕ → Bool) (off : ℕ) (c : Fin L.W → Bool), blockOf L.W X off = c →
      ∀ i (hi : i < L.W), X (off + i) = c ⟨i, hi⟩ :=
    fun _ _ _ hc i hi => congrFun hc ⟨i, hi⟩
  constructor
  · rintro ⟨β, aβ, hfa⟩ hyt
    obtain ⟨hva, hvb⟩ := hval hyt
    have aβ' : ∀ i, i < L.levStart j → β i = α i := fun i hi => aβ i (Or.inl (by omega))
    have main : ∀ U V : Fin L.W → Bool, ∃ ε : ℕ → Bool,
        blockOf L.W ε (L.leftOf j) = blockOf L.W α (L.leftOf j) ∧
        blockOf L.W ε (L.rightOf j) = blockOf L.W α (L.rightOf j) ∧
        blockOf L.W ε (L.mid j) = blockOf L.W β (L.mid j) ∧
        blockOf L.W ε (L.uBlk j) = U ∧ blockOf L.W ε (L.vBlk j) = V ∧
        ε (L.yAt j) = true ∧ L.LevelHolds validC j ε ∧
        eval ε (L.tailQBF validC baseC m (j + 1)) = true := by
      intro U V
      obtain ⟨γ, hγdef⟩ : ∃ γ, γ = SavitchData.setBlock β (L.uBlk j) U := ⟨_, rfl⟩
      obtain ⟨δ, hδdef⟩ : ∃ δ, δ = SavitchData.setBlock γ (L.vBlk j) V := ⟨_, rfl⟩
      have aγ : ∀ i, (i < L.uBlk j ∨ L.uBlk j + L.W ≤ i) → γ i = β i := by
        rw [hγdef]; exact SavitchData.setBlock_agree β (L.uBlk j) U
      have aδ : ∀ i, (i < L.vBlk j ∨ L.vBlk j + L.W ≤ i) → δ i = γ i := by
        rw [hδdef]; exact SavitchData.setBlock_agree γ (L.vBlk j) V
      have hγU : blockOf L.W γ (L.uBlk j) = U := by
        rw [hγdef]; exact SavitchData.blockOf_setBlock_self β (L.uBlk j) U
      have hδV : blockOf L.W δ (L.vBlk j) = V := by
        rw [hδdef]; exact SavitchData.blockOf_setBlock_self γ (L.vBlk j) V
      obtain ⟨ε, aε, hlevε, htailε⟩ := hfa γ aγ δ aδ
      have aεδ : ∀ i, i < L.eUA j → ε i = δ i := fun i hi => aε i (Or.inl hi)
      have aεβ : ∀ i, i < L.uBlk j → ε i = β i := fun i hi => by
        rw [aεδ i (by omega), aδ i (Or.inl (by omega)), aγ i (Or.inl hi)]
      refine ⟨ε, ?_, ?_, ?_, ?_, ?_, ?_,
        (L.eval_levelClauses validC ε j).mp hlevε, htailε⟩
      · exact blockOf_eq_of_agree L.W α ε _ fun i _ hi => by
          rw [aεβ i (by omega), aβ' i (by omega)]
      · exact blockOf_eq_of_agree L.W α ε _ fun i _ hi => by
          rw [aεβ i (by omega), aβ' i (by omega)]
      · exact blockOf_eq_of_agree L.W β ε _ fun i _ hi => aεβ i (by omega)
      · rw [← hγU]
        exact blockOf_eq_of_agree L.W γ ε _ fun i _ hi => by
          rw [aεδ i (by omega), aδ i (Or.inl (by omega))]
      · rw [← hδV]
        exact blockOf_eq_of_agree L.W δ ε _ fun i _ hi => aεδ i (by omega)
      · rw [aεβ _ (by omega), aβ' _ hyj]
        exact hyt
    obtain ⟨ε₁, e1l, e1r, e1m, e1u, e1v, e1y, e1lev, e1t⟩ :=
      main (blockOf L.W α (L.leftOf j)) (blockOf L.W β (L.mid j))
    have hall1 : ∀ i, i < L.W → ε₁ (L.eUA j + i) = true := by
      intro i hi
      rw [e1lev.2.1 i hi, bval ε₁ _ _ e1u i hi, bval ε₁ _ _ e1l i hi]
      simp
    have hall2 : ∀ i, i < L.W → ε₁ (L.eVM j + i) = true := by
      intro i hi
      rw [e1lev.2.2.1 i hi, bval ε₁ _ _ e1v i hi, bval ε₁ _ _ e1m i hi]
      simp
    have hvM : D.Valid (blockOf L.W β (L.mid j)) := by
      have hq := e1lev.1 e1y
      rw [hvalidC, e1m] at hq
      exact hq
    have r1 : D.ReachPow m (blockOf L.W α (L.leftOf j)) (blockOf L.W β (L.mid j)) := by
      have hq := (IH ε₁ (fun _ => by rw [e1u, e1v]; exact ⟨hva, hvM⟩)).mp e1t
        (e1lev.2.2.2.2.2.1 ⟨e1y, hall1, hall2⟩)
      rwa [e1u, e1v] at hq
    obtain ⟨ε₂, e2l, e2r, e2m, e2u, e2v, e2y, e2lev, e2t⟩ :=
      main (blockOf L.W β (L.mid j)) (blockOf L.W α (L.rightOf j))
    have hall3 : ∀ i, i < L.W → ε₂ (L.eUM j + i) = true := by
      intro i hi
      rw [e2lev.2.2.2.1 i hi, bval ε₂ _ _ e2u i hi, bval ε₂ _ _ e2m i hi]
      simp
    have hall4 : ∀ i, i < L.W → ε₂ (L.eVB j + i) = true := by
      intro i hi
      rw [e2lev.2.2.2.2.1 i hi, bval ε₂ _ _ e2v i hi, bval ε₂ _ _ e2r i hi]
      simp
    have r2 : D.ReachPow m (blockOf L.W β (L.mid j)) (blockOf L.W α (L.rightOf j)) := by
      have hq := (IH ε₂ (fun _ => by rw [e2u, e2v]; exact ⟨hvM, hvb⟩)).mp e2t
        (e2lev.2.2.2.2.2.2 ⟨e2y, hall3, hall4⟩)
      rwa [e2u, e2v] at hq
    exact ⟨_, r1, r2⟩
  · intro h
    obtain ⟨M, hM⟩ : ∃ M : Fin L.W → Bool, α (L.yAt j) = true →
        D.ReachPow m (blockOf L.W α (L.leftOf j)) M ∧
        D.ReachPow m M (blockOf L.W α (L.rightOf j)) := by
      by_cases hyt : α (L.yAt j) = true
      · obtain ⟨M, h1, h2⟩ := h hyt
        exact ⟨M, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨fun _ => false, fun hc => absurd hc hyt⟩
    refine ⟨SavitchData.setBlock α (L.mid j) M, SavitchData.setBlock_agree α (L.mid j) M, ?_⟩
    intro γ aγ δ aδ
    have aδα : ∀ i, i < L.mid j → δ i = α i := fun i hi => by
      rw [aδ i (Or.inl (by omega)), aγ i (Or.inl (by omega)),
        SavitchData.setBlock_agree α (L.mid j) M i (Or.inl hi)]
    have hδM : blockOf L.W δ (L.mid j) = M := by
      rw [← SavitchData.blockOf_setBlock_self α (L.mid j) M]
      exact blockOf_eq_of_agree L.W _ δ _ fun i _ hi => by
        rw [aδ i (Or.inl (by omega)), aγ i (Or.inl (by omega))]
    have hδA : blockOf L.W δ (L.leftOf j) = blockOf L.W α (L.leftOf j) :=
      blockOf_eq_of_agree L.W α δ _ fun i _ hi => aδα i (by omega)
    have hδB : blockOf L.W δ (L.rightOf j) = blockOf L.W α (L.rightOf j) :=
      blockOf_eq_of_agree L.W α δ _ fun i _ hi => aδα i (by omega)
    have hδy : δ (L.yAt j) = α (L.yAt j) := aδα _ (by omega)
    obtain ⟨Y, hY⟩ : ∃ Y : Prop, Y = (α (L.yAt j) = true ∧
        ((blockOf L.W δ (L.uBlk j) = blockOf L.W α (L.leftOf j) ∧
            blockOf L.W δ (L.vBlk j) = M) ∨
          (blockOf L.W δ (L.uBlk j) = M ∧
            blockOf L.W δ (L.vBlk j) = blockOf L.W α (L.rightOf j)))) := ⟨_, rfl⟩
    obtain ⟨ev, hev⟩ : ∃ ev : Fin (4 * L.W + 1) → Bool, ev = fun t =>
        if t.val < L.W then (δ (L.uBlk j + t.val) == δ (L.leftOf j + t.val))
        else if t.val < 2 * L.W then
          (δ (L.vBlk j + (t.val - L.W)) == δ (L.mid j + (t.val - L.W)))
        else if t.val < 3 * L.W then
          (δ (L.uBlk j + (t.val - 2 * L.W)) == δ (L.mid j + (t.val - 2 * L.W)))
        else if t.val < 4 * L.W then
          (δ (L.vBlk j + (t.val - 3 * L.W)) == δ (L.rightOf j + (t.val - 3 * L.W)))
        else decide Y := ⟨_, rfl⟩
    obtain ⟨ε, hεdef⟩ : ∃ ε, ε = SavitchData.setBlock δ (L.eUA j) ev := ⟨_, rfl⟩
    have aεδ : ∀ i, (i < L.eUA j ∨ L.eUA j + (4 * L.W + 1) ≤ i) → ε i = δ i := by
      rw [hεdef]; exact SavitchData.setBlock_agree δ (L.eUA j) ev
    have hεb : blockOf (4 * L.W + 1) ε (L.eUA j) = ev := by
      rw [hεdef]; exact SavitchData.blockOf_setBlock_self δ (L.eUA j) ev
    have hvalε : ∀ t (ht : t < 4 * L.W + 1), ε (L.eUA j + t) = ev ⟨t, ht⟩ :=
      fun t ht => congrFun hεb ⟨t, ht⟩
    have hεδ : ∀ i, i < L.eUA j → ε i = δ i := fun i hi => aεδ i (Or.inl hi)
    have hεU : blockOf L.W ε (L.uBlk j) = blockOf L.W δ (L.uBlk j) :=
      blockOf_eq_of_agree L.W δ ε _ fun i _ hi => hεδ i (by omega)
    have hεV : blockOf L.W ε (L.vBlk j) = blockOf L.W δ (L.vBlk j) :=
      blockOf_eq_of_agree L.W δ ε _ fun i _ hi => hεδ i (by omega)
    have hεM : blockOf L.W ε (L.mid j) = M := by
      rw [← hδM]
      exact blockOf_eq_of_agree L.W δ ε _ fun i _ hi => hεδ i (by omega)
    have hεA : blockOf L.W ε (L.leftOf j) = blockOf L.W α (L.leftOf j) := by
      rw [← hδA]
      exact blockOf_eq_of_agree L.W δ ε _ fun i _ hi => hεδ i (by omega)
    have hεB : blockOf L.W ε (L.rightOf j) = blockOf L.W α (L.rightOf j) := by
      rw [← hδB]
      exact blockOf_eq_of_agree L.W δ ε _ fun i _ hi => hεδ i (by omega)
    have hεy : ε (L.yAt j) = α (L.yAt j) := by rw [hεδ _ (by omega), hδy]
    have vUA : ∀ i, i < L.W → ε (L.eUA j + i) = (ε (L.uBlk j + i) == ε (L.leftOf j + i)) := by
      intro i hi
      rw [hvalε i (by omega)]
      simp only [hev]
      rw [if_pos hi, hεδ _ (by omega), hεδ _ (by omega)]
    have vVM : ∀ i, i < L.W → ε (L.eVM j + i) = (ε (L.vBlk j + i) == ε (L.mid j + i)) := by
      intro i hi
      rw [show L.eVM j + i = L.eUA j + (L.W + i) from by omega, hvalε (L.W + i) (by omega)]
      simp only [hev]
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
        hεδ _ (by omega), hεδ _ (by omega)]
    have vUM : ∀ i, i < L.W → ε (L.eUM j + i) = (ε (L.uBlk j + i) == ε (L.mid j + i)) := by
      intro i hi
      rw [show L.eUM j + i = L.eUA j + (2 * L.W + i) from by omega,
        hvalε (2 * L.W + i) (by omega)]
      simp only [hev]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
        hεδ _ (by omega), hεδ _ (by omega)]
    have vVB : ∀ i, i < L.W → ε (L.eVB j + i) = (ε (L.vBlk j + i) == ε (L.rightOf j + i)) := by
      intro i hi
      rw [show L.eVB j + i = L.eUA j + (3 * L.W + i) from by omega,
        hvalε (3 * L.W + i) (by omega)]
      simp only [hev]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        Nat.add_sub_cancel_left, hεδ _ (by omega), hεδ _ (by omega)]
    have vY : ε (L.yAt (j + 1)) = decide Y := by
      rw [show L.yAt (j + 1) = L.eUA j + 4 * L.W from by omega, hvalε (4 * L.W) (by omega)]
      simp only [hev]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    refine ⟨ε, aεδ, ?_, ?_⟩
    · rw [L.eval_levelClauses validC ε j]
      refine ⟨?_, vUA, vVM, vUM, vVB, ?_, ?_⟩
      · intro hq
        rw [hεy] at hq
        rw [hvalidC, hεM]
        exact SavitchData.ReachPow.valid_right D m (hM hq).1
      · rintro ⟨hq, hu1, hv1⟩
        rw [hεy] at hq
        rw [vY]
        refine decide_eq_true ?_
        rw [hY]
        refine ⟨hq, Or.inl ⟨?_, ?_⟩⟩
        · rw [← hεU, ← hεA]
          funext i
          have hb := hu1 i.val i.isLt
          rw [vUA i.val i.isLt] at hb
          exact beq_iff_eq.mp hb
        · rw [← hεV, ← hεM]
          funext i
          have hb := hv1 i.val i.isLt
          rw [vVM i.val i.isLt] at hb
          exact beq_iff_eq.mp hb
      · rintro ⟨hq, hu1, hv1⟩
        rw [hεy] at hq
        rw [vY]
        refine decide_eq_true ?_
        rw [hY]
        refine ⟨hq, Or.inr ⟨?_, ?_⟩⟩
        · rw [← hεU, ← hεM]
          funext i
          have hb := hu1 i.val i.isLt
          rw [vUM i.val i.isLt] at hb
          exact beq_iff_eq.mp hb
        · rw [← hεV, ← hεB]
          funext i
          have hb := hv1 i.val i.isLt
          rw [vVB i.val i.isLt] at hb
          exact beq_iff_eq.mp hb
    · refine (IH ε ?_).mpr ?_
      · intro hq
        rw [vY] at hq
        have hq' : Y := of_decide_eq_true hq
        rw [hY] at hq'
        obtain ⟨hyt, hc⟩ := hq'
        rw [hεU, hεV]
        rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
        · rw [hc1, hc2]
          exact ⟨(hval hyt).1, SavitchData.ReachPow.valid_right D m (hM hyt).1⟩
        · rw [hc1, hc2]
          exact ⟨SavitchData.ReachPow.valid_right D m (hM hyt).1, (hval hyt).2⟩
      · intro hq
        rw [vY] at hq
        have hq' : Y := of_decide_eq_true hq
        rw [hY] at hq'
        obtain ⟨hyt, hc⟩ := hq'
        rw [hεU, hεV]
        rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
        · rw [hc1, hc2]
          exact (hM hyt).1
        · rw [hc1, hc2]
          exact (hM hyt).2

/-- **The nest computes reachability in `2 ^ m` steps.** -/
theorem eval_tailQBF (hWs : L.Ws = Ws)
    (hvalidC : ∀ (α : ℕ → Bool) (off : ℕ),
      eval α (cnfQBF (validC off)) = true ↔ D.Valid (blockOf L.W α off))
    (hbase : ∀ (α : ℕ → Bool) (u v s : ℕ),
      D.Valid (blockOf L.W α u) → D.Valid (blockOf L.W α v) →
      (eval α (cnfQBF (baseC u v s)) = true ↔
        D.Base (blockOf L.W α u) (blockOf L.W α v) (blockOf Ws α s))) :
    ∀ (m j : ℕ) (α : ℕ → Bool), L.leftOf j + L.W ≤ L.levStart j →
      L.rightOf j + L.W ≤ L.levStart j → L.levStart j + L.levelSize * m ≤ L.scr →
      (α (L.yAt j) = true →
        D.Valid (blockOf L.W α (L.leftOf j)) ∧ D.Valid (blockOf L.W α (L.rightOf j))) →
      (eval α (L.tailQBF validC baseC m j) = true ↔
        (α (L.yAt j) = true →
          D.ReachPow m (blockOf L.W α (L.leftOf j)) (blockOf L.W α (L.rightOf j))))
  | 0, j, α, hl, hr, hs, hva => by
      have hle : L.levStart j ≤ L.scr := by
        rw [Nat.mul_zero] at hs
        omega
      exact L.eval_tailQBF_zero validC baseC D hWs hbase j α (by omega) (by omega)
        (by have := L.yAt_lt_levStart j; omega) hva
  | m + 1, j, α, hl, hr, hs, hva => by
      refine L.eval_tailQBF_succ validC baseC D hWs hvalidC m j α hl hr hva fun α' hva' => ?_
      have hstep : L.levStart (j + 1) + L.levelSize * m ≤ L.scr := by
        rw [L.levStart_succ j]
        have : L.levelSize * (m + 1) = L.levelSize + L.levelSize * m := by ring
        omega
      have hl' : L.leftOf (j + 1) + L.W ≤ L.levStart (j + 1) := by
        rw [L.leftOf_succ j, L.levStart_succ j, uBlk, levelSize]
        omega
      have hr' : L.rightOf (j + 1) + L.W ≤ L.levStart (j + 1) := by
        rw [L.rightOf_succ j, L.levStart_succ j, vBlk, levelSize]
        omega
      have := eval_tailQBF hWs hvalidC hbase m (j + 1) α' hl' hr' hstep
        (by rw [L.leftOf_succ j, L.rightOf_succ j]; exact hva')
      rw [L.leftOf_succ j, L.rightOf_succ j] at this
      exact this

/-! ## The whole formula -/

variable (accC : ℕ → List (List CLit))

/-- The guards: the left endpoint is the initial block, both endpoints are valid, the right one
accepts, and the chain starts. -/
noncomputable def guardClauses (init : Fin L.W → Bool) : List (List CLit) :=
  constClauses L.W 0 init ++
    (validC 0 ++ (validC L.bStart ++ (accC L.bStart ++ [[(true, L.y0)]])))

/-- The whole matrix. -/
noncomputable def fullClauses (init : Fin L.W → Bool) : List (List CLit) :=
  L.guardClauses validC accC init ++ L.tailClauses validC baseC L.n 0

theorem leftOf_zero : L.leftOf 0 = 0 := rfl
theorem rightOf_zero : L.rightOf 0 = L.bStart := rfl
theorem yAt_zero : L.yAt 0 = L.y0 := rfl

theorem levStart_zero : L.levStart 0 = 2 * L.W + 1 := by
  rw [levStart, Nat.mul_zero, Nat.add_zero]

theorem mem_guardClauses_vars (init : Fin L.W → Bool)
    (hvarsC : ∀ (off : ℕ), ∀ c ∈ validC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W)
    (hvarsA : ∀ (off : ℕ), ∀ c ∈ accC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W) :
    ∀ c ∈ L.guardClauses validC accC init, ∀ l ∈ c, l.2 < L.levStart 0 := by
  have hb : L.bStart = L.W := rfl
  have hy : L.y0 = 2 * L.W := rfl
  have hz : L.levStart 0 = 2 * L.W + 1 := L.levStart_zero
  intro c hc l hl
  rw [guardClauses, List.mem_append] at hc
  rcases hc with h | h
  · rw [constClauses, List.mem_map] at h
    obtain ⟨i, -, rfl⟩ := h
    rw [List.mem_cons] at hl
    rcases hl with rfl | hl
    · have := i.isLt
      simp only []
      omega
    · simp at hl
  · rw [List.mem_append] at h
    rcases h with h | h
    · have := hvarsC 0 c h l hl
      omega
    · rw [List.mem_append] at h
      rcases h with h | h
      · have := hvarsC L.bStart c h l hl
        omega
      · rw [List.mem_append] at h
        rcases h with h | h
        · have := hvarsA L.bStart c h l hl
          omega
        · rw [List.mem_cons] at h
          rcases h with rfl | h
          · rw [List.mem_cons] at hl
            rcases hl with rfl | hl
            · omega
            · simp at hl
          · simp at h

theorem mem_tailClauses_vars
    (hvarsC : ∀ (off : ℕ), ∀ c ∈ validC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W)
    (hvarsB : ∀ (u v s : ℕ), ∀ c ∈ baseC u v s, ∀ l ∈ c,
      (u ≤ l.2 ∧ l.2 < u + L.W) ∨ (v ≤ l.2 ∧ l.2 < v + L.W) ∨ (s ≤ l.2 ∧ l.2 < s + L.Ws)) :
    ∀ (m j : ℕ), L.leftOf j + L.W ≤ L.levStart j → L.rightOf j + L.W ≤ L.levStart j →
      L.levStart j + L.levelSize * m ≤ L.scr →
      ∀ c ∈ L.tailClauses validC baseC m j, ∀ l ∈ c, l.2 < L.nvar
  | 0, j, hl, hr, hs, c, hc, l, hl' => by
      have hy : L.yAt j < L.levStart j := L.yAt_lt_levStart j
      have hn : L.scr + L.Ws = L.nvar := rfl
      rw [Nat.mul_zero, Nat.add_zero] at hs
      rw [tailClauses] at hc
      rcases mem_disjLits_vars _ _ c hc l hl' with h | ⟨c', hc', hl''⟩
      · rw [List.mem_cons] at h
        rcases h with rfl | h
        · omega
        · simp at h
      · rcases hvarsB _ _ _ c' hc' l hl'' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  | m + 1, j, hl, hr, hs, c, hc, l, hl' => by
      have hstep : L.levStart (j + 1) + L.levelSize * m ≤ L.scr := by
        rw [L.levStart_succ j]
        have : L.levelSize * (m + 1) = L.levelSize + L.levelSize * m := by ring
        omega
      have hl' : L.leftOf (j + 1) + L.W ≤ L.levStart (j + 1) := by
        rw [L.leftOf_succ j, L.levStart_succ j, uBlk, levelSize]
        omega
      have hr' : L.rightOf (j + 1) + L.W ≤ L.levStart (j + 1) := by
        rw [L.rightOf_succ j, L.levStart_succ j, vBlk, levelSize]
        omega
      rw [tailClauses_succ, List.mem_append] at hc
      rcases hc with h | h
      · have h1 := L.mem_levelClauses_vars validC j hvarsC hl hr c h l ‹l ∈ c›
        have h2 : L.levStart (j + 1) ≤ L.scr := by
          rw [L.levStart_succ j] at hstep ⊢
          omega
        have hn : L.scr + L.Ws = L.nvar := rfl
        omega
      · exact mem_tailClauses_vars hvarsC hvarsB m (j + 1) hl' hr' hstep c h l ‹l ∈ c›

/-- **The instance is well formed** in the sense Shen's protocol needs. -/
theorem wellFormed_flat (init : Fin L.W → Bool)
    (hvarsC : ∀ (off : ℕ), ∀ c ∈ validC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W)
    (hvarsA : ∀ (off : ℕ), ∀ c ∈ accC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W)
    (hvarsB : ∀ (u v s : ℕ), ∀ c ∈ baseC u v s, ∀ l ∈ c,
      (u ≤ l.2 ∧ l.2 < u + L.W) ∨ (v ≤ l.2 ∧ l.2 < v + L.W) ∨ (s ≤ l.2 ∧ l.2 < s + L.Ws)) :
    WellFormed (L.fullPrefix, L.fullClauses validC baseC accC init) := by
  have hsc : L.levStart 0 + L.levelSize * L.n ≤ L.scr := by
    rw [levStart, scr]
    omega
  have hlz : L.leftOf 0 + L.W ≤ L.levStart 0 := by
    rw [leftOf_zero, L.levStart_zero]
    omega
  have hrz : L.rightOf 0 + L.W ≤ L.levStart 0 := by
    rw [rightOf_zero, L.levStart_zero, bStart]
    omega
  constructor
  · intro i hi
    have hlen : L.fullPrefix.length = L.nvar := L.fullPrefix_length
    have := L.listed_fullPrefix.getElem hi
    rw [this, Nat.zero_add]
  · intro c hc l hl
    dsimp only at hc ⊢
    rw [L.fullPrefix_length]
    rw [fullClauses, List.mem_append] at hc
    rcases hc with h | h
    · have h1 := L.mem_guardClauses_vars validC accC init hvarsC hvarsA c h l hl
      have h2 : L.levStart 0 ≤ L.scr := by omega
      have hn : L.scr + L.Ws = L.nvar := rfl
      omega
    · exact L.mem_tailClauses_vars validC baseC hvarsC hvarsB L.n 0 hlz hrz hsc c h l hl

/-! ## Indexing the guards and the whole matrix -/

theorem constClauses_length (W off : ℕ) (b : Fin W → Bool) :
    (constClauses W off b).length = W := by
  rw [constClauses, List.length_map, List.length_finRange]

theorem constClauses_getElem? (W off : ℕ) (b : Fin W → Bool) (p : ℕ) (hp : p < W) :
    (constClauses W off b)[p]? = some [(b ⟨p, hp⟩, off + p)] := by
  rw [constClauses, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [List.length_finRange]; exact hp)]
  simp

section GuardIndex

variable (VC AC : ℕ) (hVC : ∀ off, (validC off).length = VC)
  (hAC : ∀ off, (accC off).length = AC) (init : Fin L.W → Bool)

include hVC hAC

theorem guardClauses_length :
    (L.guardClauses validC accC init).length = L.W + (VC + (VC + (AC + 1))) := by
  rw [guardClauses]
  simp only [List.length_append, constClauses_length, hVC, hAC, List.length_cons,
    List.length_nil]

omit hVC hAC in
theorem guardClauses_getElem?_const {p : ℕ} (hp : p < L.W) :
    (L.guardClauses validC accC init)[p]? = some [(init ⟨p, hp⟩, 0 + p)] := by
  rw [guardClauses, List.getElem?_append_left (by rw [constClauses_length]; exact hp),
    constClauses_getElem? _ _ _ _ hp]

omit hAC in
theorem guardClauses_getElem?_validA {p : ℕ} (h₁ : L.W ≤ p) (h₂ : p < L.W + VC) :
    (L.guardClauses validC accC init)[p]? = (validC 0)[p - L.W]? := by
  rw [guardClauses, List.getElem?_append_right (by rw [constClauses_length]; exact h₁),
    constClauses_length, List.getElem?_append_left (by rw [hVC]; omega)]

omit hAC in
theorem guardClauses_getElem?_validB {p : ℕ} (h₁ : L.W + VC ≤ p) (h₂ : p < L.W + VC + VC) :
    (L.guardClauses validC accC init)[p]? = (validC L.bStart)[p - L.W - VC]? := by
  rw [guardClauses, List.getElem?_append_right (by rw [constClauses_length]; omega),
    constClauses_length, List.getElem?_append_right (by rw [hVC]; omega), hVC,
    List.getElem?_append_left (by rw [hVC]; omega)]

theorem guardClauses_getElem?_acc {p : ℕ} (h₁ : L.W + VC + VC ≤ p)
    (h₂ : p < L.W + VC + VC + AC) :
    (L.guardClauses validC accC init)[p]? = (accC L.bStart)[p - L.W - VC - VC]? := by
  rw [guardClauses, List.getElem?_append_right (by rw [constClauses_length]; omega),
    constClauses_length, List.getElem?_append_right (by rw [hVC]; omega), hVC,
    List.getElem?_append_right (by rw [hVC]; omega), hVC,
    List.getElem?_append_left (by rw [hAC]; omega)]

theorem guardClauses_getElem?_unit {p : ℕ} (h₁ : L.W + VC + VC + AC ≤ p) :
    (L.guardClauses validC accC init)[p]?
      = [[(true, L.y0)]][p - L.W - VC - VC - AC]? := by
  rw [guardClauses, List.getElem?_append_right (by rw [constClauses_length]; omega),
    constClauses_length, List.getElem?_append_right (by rw [hVC]; omega), hVC,
    List.getElem?_append_right (by rw [hVC]; omega), hVC,
    List.getElem?_append_right (by rw [hAC]; omega), hAC]

theorem fullClauses_getElem?_guard {p : ℕ}
    (hp : p < L.W + (VC + (VC + (AC + 1)))) :
    (L.fullClauses validC baseC accC init)[p]?
      = (L.guardClauses validC accC init)[p]? := by
  rw [fullClauses, List.getElem?_append_left (by
    rw [L.guardClauses_length validC accC VC AC hVC hAC init]; exact hp)]

theorem fullClauses_getElem?_tail {p : ℕ}
    (hp : L.W + (VC + (VC + (AC + 1))) ≤ p) :
    (L.fullClauses validC baseC accC init)[p]?
      = (L.tailClauses validC baseC L.n 0)[p - (L.W + (VC + (VC + (AC + 1))))]? := by
  rw [fullClauses, List.getElem?_append_right (by
      rw [L.guardClauses_length validC accC VC AC hVC hAC init]; exact hp),
    L.guardClauses_length validC accC VC AC hVC hAC init]

end GuardIndex

/-- **The whole formula says exactly what Savitch's recursion should.** -/
theorem eval_fullQBF (hWs : L.Ws = Ws)
    (hvalidC : ∀ (α : ℕ → Bool) (off : ℕ),
      eval α (cnfQBF (validC off)) = true ↔ D.Valid (blockOf L.W α off))
    (haccC : ∀ (α : ℕ → Bool) (off : ℕ),
      eval α (cnfQBF (accC off)) = true ↔ D.Acc (blockOf L.W α off))
    (hbase : ∀ (α : ℕ → Bool) (u v s : ℕ),
      D.Valid (blockOf L.W α u) → D.Valid (blockOf L.W α v) →
      (eval α (cnfQBF (baseC u v s)) = true ↔
        D.Base (blockOf L.W α u) (blockOf L.W α v) (blockOf Ws α s)))
    (hvarsC : ∀ (off : ℕ), ∀ c ∈ validC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W)
    (hvarsA : ∀ (off : ℕ), ∀ c ∈ accC off, ∀ l ∈ c, off ≤ l.2 ∧ l.2 < off + L.W)
    (init : Fin L.W → Bool) (α : ℕ → Bool) :
    eval α (toQBF L.fullPrefix (cnfQBF (L.fullClauses validC baseC accC init))) = true ↔
      (D.Valid init ∧
        ∃ B : Fin L.W → Bool, D.Valid B ∧ D.Acc B ∧ D.ReachPow L.n init B) := by
  subst hWs
  have hz : L.levStart 0 = 2 * L.W + 1 := L.levStart_zero
  have hb : L.bStart = L.W := rfl
  have hy : L.y0 = 2 * L.W := rfl
  have hsc : L.levStart 0 + L.levelSize * L.n ≤ L.scr := by
    rw [levStart, scr]
    omega
  have hlz : L.leftOf 0 + L.W ≤ L.levStart 0 := by rw [leftOf_zero]; omega
  have hrz : L.rightOf 0 + L.W ≤ L.levStart 0 := by rw [rightOf_zero]; omega
  -- the guards, read off an assignment
  have hguard : ∀ δ : ℕ → Bool,
      eval δ (cnfQBF (L.guardClauses validC accC init)) = true ↔
        (blockOf L.W δ 0 = init ∧ D.Valid (blockOf L.W δ 0) ∧
          D.Valid (blockOf L.W δ L.bStart) ∧ D.Acc (blockOf L.W δ L.bStart) ∧
          δ L.y0 = true) := by
    intro δ
    rw [guardClauses, eval_cnfQBF_append, eval_cnfQBF_append, eval_cnfQBF_append,
      eval_cnfQBF_append, eval_constClauses, hvalidC, hvalidC, haccC]
    have hunit : eval δ (cnfQBF [[(true, L.y0)]]) = true ↔ δ L.y0 = true := by
      simp [eval_cnfQBF_iff, eval_clauseQBF_iff, eval_litQBF]
    rw [hunit]
  -- the guards do not mention the quantifiers of the levels
  have hfv : ∀ q ∈ L.tailPrefix L.n 0,
      q.2 ∉ freeVars (cnfQBF (L.guardClauses validC accC init)) := by
    intro q hq hmem
    obtain ⟨c, hc, l, hl, heq⟩ := mem_freeVars_cnfQBF _ _ hmem
    have h1 := L.mem_guardClauses_vars validC accC init hvarsC hvarsA c hc l hl
    have h2 := L.mem_tailPrefix L.n 0 hsc q hq
    omega
  have hsplit : ∀ δ : ℕ → Bool,
      eval δ (toQBF (L.tailPrefix L.n 0)
          (cnfQBF (L.fullClauses validC baseC accC init))) = true ↔
        (eval δ (cnfQBF (L.guardClauses validC accC init)) = true ∧
          eval δ (toQBF (L.tailPrefix L.n 0)
            (cnfQBF (L.tailClauses validC baseC L.n 0))) = true) := by
    intro δ
    rw [fullClauses, SavitchData.eval_toQBF_congr (L.tailPrefix L.n 0)
      (cnfQBF (L.guardClauses validC accC init ++ L.tailClauses validC baseC L.n 0))
      (conj (cnfQBF (L.guardClauses validC accC init))
        (cnfQBF (L.tailClauses validC baseC L.n 0)))
      (fun γ => by rw [Bool.eq_iff_iff, eval_conj, Bool.and_eq_true, eval_cnfQBF_append]) δ,
      eval_toQBF_conj_left _ _ _ _ hfv]
  rw [fullPrefix, toQBF_append, toQBF_append, toQBF_append]
  simp only [toQBF_blockQ_false, eval_exs_iff, hsplit, hguard]
  constructor
  · rintro ⟨βA, -, βB, -, βy, -, ⟨hinit, hvA, hvB, haB, hy1⟩, htail⟩
    rw [← L.eval_tailQBF_flat validC baseC hvarsC L.n 0 hlz hrz hsc] at htail
    have hreach := (L.eval_tailQBF validC baseC D rfl hvalidC hbase L.n 0 βy hlz hrz hsc
      (fun _ => by rw [leftOf_zero, rightOf_zero]; exact ⟨hvA, hvB⟩)).mp htail
      (by rw [yAt_zero]; exact hy1)
    rw [leftOf_zero, rightOf_zero, hinit] at hreach
    rw [hinit] at hvA
    exact ⟨hvA, blockOf L.W βy L.bStart, hvB, haB, hreach⟩
  · rintro ⟨hvi, B, hvB, haB, hreach⟩
    obtain ⟨βA, hβA⟩ : ∃ βA, βA = SavitchData.setBlock α 0 init := ⟨_, rfl⟩
    obtain ⟨βB, hβB⟩ : ∃ βB, βB = SavitchData.setBlock βA L.bStart B := ⟨_, rfl⟩
    obtain ⟨βy, hβy⟩ : ∃ βy, βy = SavitchData.setBlock (W := 1) βB L.y0 (fun _ => true) :=
      ⟨_, rfl⟩
    have aA : ∀ i, (i < 0 ∨ 0 + L.W ≤ i) → βA i = α i := by
      rw [hβA]; exact SavitchData.setBlock_agree α 0 init
    have aB : ∀ i, (i < L.bStart ∨ L.bStart + L.W ≤ i) → βB i = βA i := by
      rw [hβB]; exact SavitchData.setBlock_agree βA L.bStart B
    have ay : ∀ i, (i < L.y0 ∨ L.y0 + 1 ≤ i) → βy i = βB i := by
      rw [hβy]; exact SavitchData.setBlock_agree (W := 1) βB L.y0 fun _ => true
    have hA0 : blockOf L.W βy 0 = init := by
      rw [show init = blockOf L.W βA 0 from (by rw [hβA, SavitchData.blockOf_setBlock_self])]
      refine blockOf_eq_of_agree L.W βA βy 0 fun i _ hi => ?_
      rw [ay i (by omega), aB i (by omega)]
    have hB0 : blockOf L.W βy L.bStart = B := by
      rw [show B = blockOf L.W βB L.bStart from (by rw [hβB, SavitchData.blockOf_setBlock_self])]
      refine blockOf_eq_of_agree L.W βB βy L.bStart fun i _ hi => ay i (by omega)
    have hy1 : βy L.y0 = true := by
      rw [hβy]
      exact congrFun (SavitchData.blockOf_setBlock_self (W := 1) βB L.y0 fun _ => true) ⟨0, by
        omega⟩
    refine ⟨βA, aA, βB, aB, βy, ay, ⟨hA0, ?_, ?_, ?_, hy1⟩, ?_⟩
    · rw [hA0]; exact hvi
    · rw [hB0]; exact hvB
    · rw [hB0]; exact haB
    · rw [← L.eval_tailQBF_flat validC baseC hvarsC L.n 0 hlz hrz hsc]
      refine (L.eval_tailQBF validC baseC D rfl hvalidC hbase L.n 0 βy hlz hrz hsc
        (fun _ => by rw [leftOf_zero, rightOf_zero, hA0, hB0]; exact ⟨hvi, hvB⟩)).mpr ?_
      intro _
      rw [leftOf_zero, rightOf_zero, hA0, hB0]
      exact hreach

end FlatLayout

end Complexity
