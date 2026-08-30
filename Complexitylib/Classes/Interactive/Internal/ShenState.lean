/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenSchedule
public import Complexitylib.Classes.Interactive.Internal.Horner
public import Complexitylib.Classes.Interactive.Internal.SampledChain
public import Mathlib.Algebra.Field.ZMod

/-!
# One round of the concrete verifier

⚠️ Unreviewed by Bolton

The polynomial-time pieces of a single round of Shen's protocol, on strings:

- `replaceBlock` puts a challenge into the point;
- `dropChild` removes the first operator from the encoded schedule;
- `reduceMod` reduces a coin block modulo `p` (multiplication by one);
- `opCheck` is the verifier's consistency check `Op.check` on a coefficient string, evaluated
  with Horner's rule.

Each comes with its value lemma on well-formed inputs and its `FP` membership.

## Main results

- `replaceBlock_pointStr` — replacing a block updates the assignment
- `dropChild_bitstringEncode` — dropping the first child is `List.tail`
- `reduceMod_eq` — reduction is `reduceBits`
- `opCheck_eq` — the string check is `Op.check` on residues
-/

@[expose] public section

namespace Complexity

open Cobham OpChain

/-! ## Replacing a block of the point -/

/-- Replace the `|u|`-th block of width `|q|` of `pt` by `t`. -/
def replaceBlock (pt q u t : List Bool) : List Bool :=
  pt.take (mulLen u q).length ++ t ++ pt.drop (mulLen u q ++ q).length

theorem replaceBlock_mem_FP {a b c d : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) (hd : d ∈ FP) : (fun z => replaceBlock (a z) (b z) (c z) (d z)) ∈ FP :=
  Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (Cobham.takeLenFn_mem_FP (mulLen_mem_FP hc hb) ha) hd)
    (dropLenFn_mem_FP (Cobham.appendFn_mem_FP (mulLen_mem_FP hc hb) hb) ha)

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
/-- **Replacing a block updates the assignment.** -/
theorem replaceBlock_pointStr (w m : ℕ) (a : ℕ → ZMod p) (q : List Bool) (hq : q.length = w)
    {i : ℕ} (hi : i < m) (t : ZMod p) :
    replaceBlock (pointStr w m a) q (List.replicate i true) (encZMod w t)
      = pointStr w m (Function.update a i t) := by
  rw [replaceBlock, length_mulLen, List.length_append, length_mulLen, List.length_replicate, hq,
    pointStr, pointStr]
  have hsplit : ∀ (f : ℕ → ZMod p) (n : ℕ), n ≤ m →
      ((List.range m).map fun j => encZMod w (f j)).flatten
        = ((List.range n).map fun j => encZMod w (f j)).flatten
          ++ ((List.range (m - n)).map fun j => encZMod w (f (n + j))).flatten := by
    intro f n hn
    conv_lhs => rw [show m = n + (m - n) by omega, List.range_add]
    rw [List.map_append, List.map_map, List.flatten_append]
    rfl
  have hlen : ∀ (f : ℕ → ZMod p) (n : ℕ),
      (((List.range n).map fun j => encZMod w (f j)).flatten).length = n * w := by
    intro f n
    rw [List.length_flatten, List.map_map]
    have : ((List.range n).map (List.length ∘ fun j => encZMod w (f j)))
        = (List.range n).map fun _ => w := List.map_congr_left fun j _ => by simp
    rw [this, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  rw [hsplit a i hi.le, hsplit (Function.update a i t) i hi.le,
    List.take_left' (hlen a i),
    show i * w + w = (((List.range i).map fun j => encZMod w (a j)).flatten).length + w by
      rw [hlen],
    ← List.drop_drop, List.drop_left]
  have hrest : ∀ f : ℕ → ZMod p,
      ((List.range (m - i)).map fun j => encZMod w (f (i + j))).flatten
        = encZMod w (f i)
          ++ ((List.range (m - i - 1)).map fun j => encZMod w (f (i + 1 + j))).flatten := by
    intro f
    rw [show m - i = (m - i - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons,
      List.flatten_cons, List.map_map, Nat.add_zero]
    congr 2
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp]
    congr 2
    omega
  rw [hrest a, hrest (Function.update a i t), List.drop_left' (by simp), Function.update_self,
    List.append_assoc]
  congr 1
  · congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [Function.update_of_ne (by rw [List.mem_range] at hj; omega)]
  · congr 2
    refine List.map_congr_left fun j _ => ?_
    rw [Function.update_of_ne (by omega)]

/-! ## Dropping the first operator -/

/-- Remove the first entry of an encoded list. -/
noncomputable def dropChild (e : List Bool) : List Bool :=
  false :: (posInner e).drop (posAt e 0).length ++ [true]

theorem dropChild_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => dropChild (a z)) ∈ FP := by
  have hpos : (fun z => posAt (a z) 0) ∈ FP := by
    simpa using posAt_mem_FP (constFn_mem_FP []) ha
  have hcat : (fun z => (posInner (a z)).drop (posAt (a z) 0).length ++ [true]) ∈ FP :=
    Cobham.appendFn_mem_FP (dropLenFn_mem_FP hpos (posInner_mem_FP ha)) (constFn_mem_FP _)
  have := mem_FP_comp hcat (Cobham.cons_mem_FP false)
  simpa [Function.comp, dropChild] using this

/-- **Dropping the first child is `List.tail`.** -/
theorem dropChild_bitstringEncode {α : Type} [DataEncode α] (l : List α) :
    dropChild (DataEncode.bitstringEncode l) = DataEncode.bitstringEncode l.tail := by
  cases l with
  | nil =>
      rw [dropChild, posInner_bitstringEncode, posAt_eq_nil (by simp)]
      simp [DataEncode.bitstringEncode_def, Data.toBits_l]
  | cons x l =>
      rw [dropChild, posAt_eq_of_lt (l := x :: l) (i := 0) (by simp), List.getElem_cons_zero,
        List.tail_cons, bitstringEncode_eq_posInner l, posInner_bitstringEncode,
        posInner_bitstringEncode, List.map_cons, List.map_cons, List.flatten_cons,
        List.drop_left' (by rw [DataEncode.bitstringEncode_def])]

/-! ## Reducing a coin block -/

/-- A string reduced modulo `q`: multiplication by one. -/
noncomputable def reduceMod (q v : List Bool) : List Bool := mulMod q (oneStr q) v

theorem reduceMod_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => reduceMod (a z) (b z)) ∈ FP :=
  mulModFn_mem_FP ha (oneStrFn_mem_FP ha) hb

/-- **Reduction is `reduceBits`**, as a residue. -/
theorem reduceMod_eq (w : ℕ) (hp : p < 2 ^ w) (hp1 : 1 < p) {k : ℕ} (v : Fin k → Bool) :
    reduceMod (bitsOfLenLE w p) (BitString.toList v) = encZMod w (reduceBits k p v) := by
  have hpv : binValLE (bitsOfLenLE w p) = p := binValLE_bitsOfLenLE w p hp
  have hw : 0 < w := by
    by_contra h0
    have : w = 0 := by omega
    subst this
    simp at hp
    omega
  have hone := binValLE_oneStr (bitsOfLenLE w p)
  have honel : (oneStr (bitsOfLenLE w p)).length = (bitsOfLenLE w p).length :=
    oneStr_length _ (by simpa using hw)
  obtain ⟨hval, hlen⟩ := binValLE_mulMod (bitsOfLenLE w p) (oneStr (bitsOfLenLE w p))
    (BitString.toList v) honel (by rw [hone, hpv]; exact hp1)
  refine eq_of_binValLE_eq ?_ ?_
  · rw [reduceMod, hlen, bitsOfLenLE_length, encZMod_length]
  · rw [reduceMod, hval, hone, hpv, one_mul, binValLE_encZMod w hp, reduceBits, ZMod.val_natCast]

/-! ## The consistency check -/

/-- The verifier's check of the coefficient string `s` against the claim `C`, for the operator
of kind `kind` on the variable whose current value is `av`: the check value of `Op.check`. -/
noncomputable def opCheckVal (q kind av s : List Bool) : List Bool :=
  let s0 := hornerEval q (List.replicate q.length false) s
  let s1 := hornerEval q (oneStr q) s
  selectHead (emptyFlag kind) (mulMod q s0 s1)
    (selectHead (lenLeFlag [false] kind)
      (oneMinusMod q (mulMod q (oneMinusMod q s0) (oneMinusMod q s1)))
      (addMod q (mulMod q (oneMinusMod q av) s0) (mulMod q av s1)))

theorem opCheckVal_mem_FP {a b c d : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP)
    (hc : c ∈ FP) (hd : d ∈ FP) : (fun z => opCheckVal (a z) (b z) (c z) (d z)) ∈ FP := by
  have hs0 : (fun z => hornerEval (a z) (List.replicate (a z).length false) (d z)) ∈ FP :=
    hornerEvalFn_mem_FP ha (zeroBlockFn_mem_FP ha) hd
  have hs1 : (fun z => hornerEval (a z) (oneStr (a z)) (d z)) ∈ FP :=
    hornerEvalFn_mem_FP ha (oneStrFn_mem_FP ha) hd
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP hb) (mulModFn_mem_FP ha hs0 hs1)
    (Cobham.selectHeadFn_mem_FP (lenLeFlagFn_mem_FP (constFn_mem_FP _) hb)
      (oneMinusModFn_mem_FP ha (mulModFn_mem_FP ha (oneMinusModFn_mem_FP ha hs0)
        (oneMinusModFn_mem_FP ha hs1)))
      (addModFn_mem_FP ha (mulModFn_mem_FP ha (oneMinusModFn_mem_FP ha hc) hs0)
        (mulModFn_mem_FP ha hc hs1)))

end Complexity

namespace Complexity

open Cobham OpChain

/-- **The string check is `Op.check` on residues**, the kind codes being the ones `decodeOp`
reads. -/
theorem opCheckVal_eq {p : ℕ} [hpr : Fact p.Prime] (w : ℕ) (hp : p < 2 ^ w) (hw : 0 < w)
    (c : OpCode) (a : ℕ → ZMod p) (f : Polynomial (ZMod p)) (n : ℕ) (hn : f.natDegree < n) :
    opCheckVal (bitsOfLenLE w p) c.1 (encZMod w (a (decodeOp c).var)) (coeffBlocks w f n).flatten
      = encZMod w ((decodeOp c).check a f) := by
  haveI : NeZero p := ⟨hpr.out.ne_zero⟩
  have hp1 : 1 < p := hpr.out.one_lt
  have hzero : List.replicate (bitsOfLenLE w p).length false = encZMod w (0 : ZMod p) := by
    refine eq_of_binValLE_eq ?_ ?_
    · simp
    · rw [binValLE_replicate_false, binValLE_encZMod w hp, ZMod.val_zero]
  have hone : oneStr (bitsOfLenLE w p) = encZMod w (1 : ZMod p) := oneStr_encZMod w hp hp1
  simp only [opCheckVal]
  rw [hzero, hone, hornerEval_encZMod w hp hw f n hn, hornerEval_encZMod w hp hw f n hn]
  rcases c with ⟨kind, v⟩
  rcases kind with _ | ⟨b, _ | ⟨b', rest⟩⟩
  · rw [emptyFlag_nil, selectHead_cons_true, mulMod_encZMod w hp]
    rfl
  · rw [emptyFlag_cons, selectHead_cons_false]
    have : lenLeFlag [false] [b] = [true] := (lenLeFlag_eq_true_iff _ _).mpr (by simp)
    rw [this, selectHead_cons_true, oneMinusMod_encZMod w hp hp1, oneMinusMod_encZMod w hp hp1,
      mulMod_encZMod w hp, oneMinusMod_encZMod w hp hp1]
    rfl
  · rw [emptyFlag_cons, selectHead_cons_false]
    have : lenLeFlag [false] (b :: b' :: rest) = [false] := by
      rcases lenLeFlag_flag [false] (b :: b' :: rest) with h | h
      · have := (lenLeFlag_eq_true_iff _ _).mp h
        simp at this
      · exact h
    rw [this, selectHead_cons_false, oneMinusMod_encZMod w hp hp1, mulMod_encZMod w hp,
      mulMod_encZMod w hp, addMod_encZMod w hp]
    rfl

end Complexity
