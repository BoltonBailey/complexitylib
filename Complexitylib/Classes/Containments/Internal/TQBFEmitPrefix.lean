/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFEmitArith
public import Complexitylib.Classes.Containments.Internal.EmitList
public import Complexitylib.Classes.PCP.Internal.UnaryDivMod
public import Complexitylib.Classes.PCP.Internal.UnaryList
public import Complexitylib.Classes.PCP.Internal.NatEncode
public import Complexitylib.Classes.PCP.Internal.Materialize

/-!
# Emitting the flat prefix

⚠️ Unreviewed by Bolton

`flatKind` is pure arithmetic on the layout's sizes — a comparison, a division and a remainder —
so it is an `FP` function of the input paired with the variable index in unary. That makes the
whole quantifier prefix an indexed family, which `emit_list_mem_FP` turns into a single `FP`
function producing its encoding.

## Main results

- `kindEnc_eq` — the kind of a variable, encoded, as an `FP` function of `pair x ⌞i⌟`
- `prefixEnc_mem_FP` — the encoded prefix is an `FP` function of the input
-/

@[expose] public section

namespace Complexity

open Polynomial CircuitUnrolling

variable {k : ℕ} (tm : NTM k) (sp : Polynomial ℕ)

/-! ## The layout's sizes, read off a paired input -/

/-- The block width, in unary, from `pair x u`. -/
noncomputable def wRul (z : List Bool) : List Bool := polyRuler (widthP tm sp) (pairFst z)

/-- The number of levels, in unary, from `pair x u`. -/
noncomputable def nRul (z : List Bool) : List Bool := polyRuler (levelsP tm sp) (pairFst z)

/-- Where the levels start, in unary. -/
noncomputable def aRul (z : List Bool) : List Bool := mulC 2 (wRul tm sp z) ++ [false]

/-- One level's width, in unary. -/
noncomputable def sizeRul (z : List Bool) : List Bool := mulC 7 (wRul tm sp z) ++ [false]

/-- The offset of the index inside the levels. -/
noncomputable def offRul (z : List Bool) : List Bool :=
  (pairSnd z).drop (aRul tm sp z).length

/-- Which level the index falls in. -/
noncomputable def levIdx (z : List Bool) : List Bool :=
  divFn2 (pair (sizeRul tm sp z) (offRul tm sp z))

/-- Where inside its level the index falls. -/
noncomputable def posIdx (z : List Bool) : List Bool :=
  modFn2 (pair (sizeRul tm sp z) (offRul tm sp z))

@[simp] theorem wRul_length (x u : List Bool) :
    (wRul tm sp (pair x u)).length = (flatLayoutOf tm sp x).W := by
  rw [wRul, pairFst_pair, polyRuler_length, flatLayoutOf_W]

@[simp] theorem nRul_length (x u : List Bool) :
    (nRul tm sp (pair x u)).length = (flatLayoutOf tm sp x).n := by
  rw [nRul, pairFst_pair, polyRuler_length, flatLayoutOf_n]

@[simp] theorem aRul_length (x u : List Bool) :
    (aRul tm sp (pair x u)).length = 2 * (flatLayoutOf tm sp x).W + 1 := by
  rw [aRul, List.length_append, length_mulC, wRul_length]
  simp [Nat.mul_comm]

@[simp] theorem sizeRul_length (x u : List Bool) :
    (sizeRul tm sp (pair x u)).length = (flatLayoutOf tm sp x).levelSize := by
  rw [sizeRul, List.length_append, length_mulC, wRul_length, FlatLayout.levelSize]
  simp [Nat.mul_comm]

@[simp] theorem offRul_length (x u : List Bool) :
    (offRul tm sp (pair x u)).length = u.length - (2 * (flatLayoutOf tm sp x).W + 1) := by
  rw [offRul, List.length_drop, pairSnd_pair, aRul_length]

theorem levIdx_eq (x u : List Bool) :
    levIdx tm sp (pair x u)
      = List.replicate ((u.length - (2 * (flatLayoutOf tm sp x).W + 1)) /
          (flatLayoutOf tm sp x).levelSize) true := by
  rw [levIdx, divFn2_eq (by rw [sizeRul_length]; exact (flatLayoutOf tm sp x).levelSize_pos),
    offRul_length, sizeRul_length]

theorem posIdx_eq (x u : List Bool) :
    posIdx tm sp (pair x u)
      = List.replicate ((u.length - (2 * (flatLayoutOf tm sp x).W + 1)) %
          (flatLayoutOf tm sp x).levelSize) true := by
  rw [posIdx, modFn2_eq (by rw [sizeRul_length]; exact (flatLayoutOf tm sp x).levelSize_pos),
    offRul_length, sizeRul_length]

/-! ## Each of them is `FP` -/

theorem wRul_mem_FP : wRul tm sp ∈ FP :=
  polyRulerFn_mem_FP _ pairFst_mem_FP

theorem nRul_mem_FP : nRul tm sp ∈ FP :=
  polyRulerFn_mem_FP _ pairFst_mem_FP

theorem aRul_mem_FP : aRul tm sp ∈ FP :=
  Cobham.appendFn_mem_FP (mulC_mem_FP (wRul_mem_FP tm sp) 2) (constFn_mem_FP [false])

theorem sizeRul_mem_FP : sizeRul tm sp ∈ FP :=
  Cobham.appendFn_mem_FP (mulC_mem_FP (wRul_mem_FP tm sp) 7) (constFn_mem_FP [false])

theorem offRul_mem_FP : offRul tm sp ∈ FP :=
  dropLenFn_mem_FP (aRul_mem_FP tm sp) Cobham.sndBlock_mem_FP

theorem levIdx_mem_FP : levIdx tm sp ∈ FP :=
  mem_FP_comp (Cobham.pairFn_mem_FP (sizeRul_mem_FP tm sp) (offRul_mem_FP tm sp)) divFn2_mem_FP

theorem posIdx_mem_FP : posIdx tm sp ∈ FP :=
  mem_FP_comp (Cobham.pairFn_mem_FP (sizeRul_mem_FP tm sp) (offRul_mem_FP tm sp)) modFn2_mem_FP

/-! ## The kind of a variable -/

/-- `false`, encoded. -/
def encFalse : List Bool := DataEncode.bitstringEncode false

/-- `true`, encoded. -/
def encTrue : List Bool := DataEncode.bitstringEncode true

/-- The encoded kind of the variable whose index is the second component. -/
noncomputable def kindEnc (z : List Bool) : List Bool :=
  ifLtLen (pairSnd z) (aRul tm sp z) encFalse
    (ifLtLen (levIdx tm sp z) (nRul tm sp z)
      (ifLtLen (posIdx tm sp z) (wRul tm sp z) encFalse
        (ifLtLen (posIdx tm sp z) (mulC 3 (wRul tm sp z)) encTrue encFalse))
      encFalse)

theorem kindEnc_eq (x : List Bool) (i : ℕ) :
    kindEnc tm sp (pair x (List.replicate i true))
      = DataEncode.bitstringEncode ((flatLayoutOf tm sp x).flatKind i) := by
  have hu : (List.replicate i true).length = i := List.length_replicate
  have hlev : (flatLayoutOf tm sp x).levelSize = 7 * (flatLayoutOf tm sp x).W + 1 := rfl
  rw [kindEnc, FlatLayout.flatKind]
  rw [pairSnd_pair]
  by_cases h1 : i < 2 * (flatLayoutOf tm sp x).W + 1
  · rw [ifLtLen_pos (by rw [hu, aRul_length]; exact h1), decide_eq_false (by omega)]
    rfl
  · rw [ifLtLen_neg (by rw [hu, aRul_length]; omega)]
    rw [levIdx_eq, posIdx_eq, hu]
    by_cases h2 : (i - (2 * (flatLayoutOf tm sp x).W + 1)) /
        (flatLayoutOf tm sp x).levelSize < (flatLayoutOf tm sp x).n
    · rw [ifLtLen_pos (by rw [List.length_replicate, nRul_length]; exact h2)]
      by_cases h3 : (i - (2 * (flatLayoutOf tm sp x).W + 1)) %
          (flatLayoutOf tm sp x).levelSize < (flatLayoutOf tm sp x).W
      · rw [ifLtLen_pos (by rw [List.length_replicate, wRul_length]; exact h3),
          decide_eq_false (by omega)]
        rfl
      · rw [ifLtLen_neg (by rw [List.length_replicate, wRul_length]; omega)]
        by_cases h4 : (i - (2 * (flatLayoutOf tm sp x).W + 1)) %
            (flatLayoutOf tm sp x).levelSize < 3 * (flatLayoutOf tm sp x).W
        · rw [ifLtLen_pos (by
            rw [List.length_replicate, length_mulC, wRul_length]
            omega), decide_eq_true (by omega)]
          rfl
        · rw [ifLtLen_neg (by
            rw [List.length_replicate, length_mulC, wRul_length]
            omega), decide_eq_false (by omega)]
          rfl
    · rw [ifLtLen_neg (by rw [List.length_replicate, nRul_length]; exact h2),
        decide_eq_false (by omega)]
      rfl

theorem kindEnc_mem_FP : kindEnc tm sp ∈ FP := by
  have hw := wRul_mem_FP tm sp
  have hn := nRul_mem_FP tm sp
  have hp := posIdx_mem_FP tm sp
  exact ifLtLen_mem_FP Cobham.sndBlock_mem_FP (aRul_mem_FP tm sp) (constFn_mem_FP _)
    (ifLtLen_mem_FP (levIdx_mem_FP tm sp) hn
      (ifLtLen_mem_FP hp hw (constFn_mem_FP _)
        (ifLtLen_mem_FP hp (mulC_mem_FP hw 3) (constFn_mem_FP _) (constFn_mem_FP _)))
      (constFn_mem_FP _))

/-! ## The prefix as an indexed family -/

/-- A pair's encoding is its components' encodings, bracketed. -/
theorem bitstringEncode_pair {α β : Type} [DataEncode α] [DataEncode β] (a : α) (b : β) :
    DataEncode.bitstringEncode (a, b)
      = false :: (DataEncode.bitstringEncode a ++ DataEncode.bitstringEncode b) ++ [true] := by
  rw [DataEncode.bitstringEncode_def, DataEncode_pair, Data.toBits_l]
  simp [DataEncode.bitstringEncode_def]

/-- **A pair is emittable when its components are.** -/
theorem pair_emit_mem_FP {A B : Type} [DataEncode A] [DataEncode B]
    (f : List Bool → A) (g : List Bool → B)
    (hf : (fun x => DataEncode.bitstringEncode (f x)) ∈ FP)
    (hg : (fun x => DataEncode.bitstringEncode (g x)) ∈ FP) :
    (fun x => DataEncode.bitstringEncode ((f x, g x) : A × B)) ∈ FP := by
  have hbody := Cobham.appendFn_mem_FP hf hg
  have hcons := Cobham.appendFn_mem_FP (constFn_mem_FP [false]) hbody
  refine mem_FP_of_eq (Cobham.appendFn_mem_FP hcons (constFn_mem_FP [true])) fun x => ?_
  rw [bitstringEncode_pair]
  simp

/-- The `i`-th entry of the prefix, encoded. -/
noncomputable def prefEntry (z : List Bool) : List Bool :=
  false :: (kindEnc tm sp z ++
    natEncodeFn (pair (polyRuler (nvarP tm sp) (pairFst z)) (pairSnd z))) ++ [true]

theorem prefEntry_mem_FP : prefEntry tm sp ∈ FP := by
  have hpair : (fun z => pair (polyRuler (nvarP tm sp) (pairFst z)) (pairSnd z)) ∈ FP :=
    Cobham.pairFn_mem_FP (polyRulerFn_mem_FP (nvarP tm sp) pairFst_mem_FP)
      Cobham.sndBlock_mem_FP
  have hnat : (fun z => natEncodeFn (pair (polyRuler (nvarP tm sp) (pairFst z)) (pairSnd z)))
      ∈ FP := mem_FP_of_eq (mem_FP_comp hpair natEncodeFn_mem_FP) fun z => rfl
  have hbody := Cobham.appendFn_mem_FP (kindEnc_mem_FP tm sp) hnat
  have hcons := Cobham.appendFn_mem_FP (constFn_mem_FP [false]) hbody
  exact mem_FP_of_eq (Cobham.appendFn_mem_FP hcons (constFn_mem_FP [true])) fun z => by
    rw [prefEntry]
    simp

theorem prefEntry_eq (x : List Bool) (i : ℕ) (hi : i < (flatLayoutOf tm sp x).nvar) :
    prefEntry tm sp (pair x (List.replicate i true))
      = DataEncode.bitstringEncode ((flatLayoutOf tm sp x).flatKind i, i) := by
  have hlt : (List.replicate i true).length
      < 2 ^ (polyRuler (nvarP tm sp) x).length := by
    rw [List.length_replicate, polyRuler_length, nvarP_eval]
    exact lt_of_lt_of_le hi (Nat.le_of_lt Nat.lt_two_pow_self)
  rw [prefEntry, bitstringEncode_pair, kindEnc_eq, pairFst_pair, pairSnd_pair]
  congr 2
  rw [natEncodeFn_eq (by rw [pairFst_pair, pairSnd_pair]; exact hlt), pairSnd_pair,
    List.length_replicate]

/-- **The quantifier prefix is emittable.** -/
theorem prefixEnc_mem_FP :
    (fun x => DataEncode.bitstringEncode (flatLayoutOf tm sp x).flatPrefix) ∈ FP := by
  have hlen : (fun x => List.replicate ((flatLayoutOf tm sp x).flatPrefix).length true) ∈ FP := by
    refine mem_FP_of_eq (divC_mem_FP (polyRulerFn_mem_FP (nvarP tm sp) id_mem_FP) 1) fun x => ?_
    rw [divC_eq (by norm_num), polyRuler_length, FlatLayout.flatPrefix_length]
    simp
  refine emit_list_mem_FP (prefEntry_mem_FP tm sp) hlen fun x i hi => ?_
  have hnv : i < (flatLayoutOf tm sp x).nvar := by
    rw [FlatLayout.flatPrefix_length] at hi
    exact hi
  rw [prefEntry_eq tm sp x i hnv]
  congr 1
  simp only [FlatLayout.flatPrefix, List.getElem_map, List.getElem_range]

end Complexity
