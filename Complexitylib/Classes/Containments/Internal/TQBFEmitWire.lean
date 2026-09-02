/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFEmitValid
public import Complexitylib.Classes.PCP.Internal.FiniteKey

/-!
# Table lookups and wire arithmetic

⚠️ Unreviewed by Bolton

The emitter has to turn a decoded descriptor — a tape, a position, a symbol — into the wire
index of the atom it names. Two ingredients: a lookup into a constant-size table, which is `FP`
for free because it depends on its input only through a bounded key; and `configIndex`, which is
a polynomial in the tape index, the position and the symbol index.

## Main results

- `tableU` / `tableU_length` / `tableU_mem_FP` — a bounded table lookup, in unary
- `headWireU` / `cellWireU` and their length lemmas — the wire of a head or cell atom
-/

@[expose] public section

namespace Complexity

open CircuitUnrolling

/-! ## Bounded table lookups -/

/-- The `f`-value of the entry of `l` at the index `s` names, in unary. -/
noncomputable def tableU {A : Type} (l : List A) (f : A → ℕ) (s : List Bool) : List Bool :=
  List.replicate (match l[s.length]? with
    | some a => f a
    | none => 0) true

theorem tableU_length {A : Type} (l : List A) (f : A → ℕ) (s : List Bool)
    (h : s.length < l.length) : (tableU l f s).length = f (l[s.length]'h) := by
  rw [tableU, List.length_replicate, List.getElem?_eq_getElem h]

theorem tableU_mem_FP {A : Type} (l : List A) (f : A → ℕ) {idx : List Bool → List Bool}
    (hidx : idx ∈ FP) {B : ℕ} (hB : ∀ z, (idx z).length ≤ B) :
    (fun z => tableU l f (idx z)) ∈ FP :=
  mem_FP_of_bounded_key hidx hB (tableU l f)

/-! ## Wires -/

variable {k : ℕ} (tm : NTM k) (T : ℕ)

/-- The wire of a head atom, in unary: `off + |Q| + tape * (T + 1) + position`. -/
noncomputable def headWireU (off qU tapeU posU horU : List Bool) : List Bool :=
  off ++ (qU ++ (mulLen tapeU horU ++ posU))

theorem headWireU_length (off qU tapeU posU horU : List Bool) :
    (headWireU off qU tapeU posU horU).length
      = off.length + (qU.length + (tapeU.length * horU.length + posU.length)) := by
  rw [headWireU, List.length_append, List.length_append, List.length_append, length_mulLen]

theorem headWireU_eq (off : ℕ) (tape : TapeSlot k) (p : Fin (T + 1))
    {offU qU tapeU posU horU : List Bool} (hoff : offU.length = off)
    (hq : qU.length = Fintype.card tm.Q) (htape : tapeU.length = tape.index.val)
    (hpos : posU.length = p.val) (hhor : horU.length = T + 1) :
    (headWireU offU qU tapeU posU horU).length
      = configWire tm T off (.head tape p) := by
  rw [headWireU_length, hoff, hq, htape, hpos, hhor, configWire, configIndex]
  ring

/-- The wire of a cell atom, in unary. -/
noncomputable def cellWireU (offU qU hdU tapeU posU horU symU : List Bool) : List Bool :=
  offU ++ (qU ++ (hdU ++ (mulC 4 (mulLen tapeU horU ++ posU) ++ symU)))

theorem cellWireU_length (offU qU hdU tapeU posU horU symU : List Bool) :
    (cellWireU offU qU hdU tapeU posU horU symU).length
      = offU.length + (qU.length + (hdU.length +
          ((tapeU.length * horU.length + posU.length) * 4 + symU.length))) := by
  rw [cellWireU, List.length_append, List.length_append, List.length_append,
    List.length_append, length_mulC, List.length_append, length_mulLen]

theorem cellWireU_eq (off : ℕ) (tape : TapeSlot k) (p : Fin (T + 2)) (sym : Γ)
    {offU qU hdU tapeU posU horU symU : List Bool} (hoff : offU.length = off)
    (hq : qU.length = Fintype.card tm.Q) (hhd : hdU.length = (k + 2) * (T + 1))
    (htape : tapeU.length = tape.index.val) (hpos : posU.length = p.val)
    (hhor : horU.length = T + 2) (hsym : symU.length = symbolIndex sym) :
    (cellWireU offU qU hdU tapeU posU horU symU).length
      = configWire tm T off (.cell tape p sym) := by
  rw [cellWireU_length, hoff, hq, hhd, htape, hpos, hhor, hsym, configWire, configIndex]
  ring

theorem headWireU_mem_FP {off qU tapeU posU horU : List Bool → List Bool}
    (hoff : off ∈ FP) (hq : qU ∈ FP) (htape : tapeU ∈ FP) (hpos : posU ∈ FP)
    (hhor : horU ∈ FP) :
    (fun z => headWireU (off z) (qU z) (tapeU z) (posU z) (horU z)) ∈ FP :=
  Cobham.appendFn_mem_FP hoff (Cobham.appendFn_mem_FP hq
    (Cobham.appendFn_mem_FP (mulLen_mem_FP htape hhor) hpos))

theorem cellWireU_mem_FP {off qU hdU tapeU posU horU symU : List Bool → List Bool}
    (hoff : off ∈ FP) (hq : qU ∈ FP) (hhd : hdU ∈ FP) (htape : tapeU ∈ FP)
    (hpos : posU ∈ FP) (hhor : horU ∈ FP) (hsym : symU ∈ FP) :
    (fun z => cellWireU (off z) (qU z) (hdU z) (tapeU z) (posU z) (horU z) (symU z)) ∈ FP :=
  Cobham.appendFn_mem_FP hoff (Cobham.appendFn_mem_FP hq
    (Cobham.appendFn_mem_FP hhd (Cobham.appendFn_mem_FP
      (mulC_mem_FP (Cobham.appendFn_mem_FP (mulLen_mem_FP htape hhor) hpos) 4) hsym)))

/-! ## The at-most-one clauses -/

/-- One at-most-one clause, from the two wires it compares. -/
noncomputable def amoEnc (w aW bW : List Bool) : List Bool :=
  ifEqLen aW bW (clause2 w [] aW [true] aW) (clause2 w [] aW [] bW)

theorem amoEnc_eq (w aW bW : List Bool) (h₁ : aW.length ≤ w.length)
    (h₂ : bW.length ≤ w.length) :
    amoEnc w aW bW
      = DataEncode.bitstringEncode
          (if aW.length = bW.length then
              [(false, aW.length), (true, aW.length)]
            else [(false, aW.length), (false, bW.length)]) := by
  rw [amoEnc]
  by_cases hc : aW.length = bW.length
  · rw [ifEqLen_pos hc, if_pos hc,
      clause2_eq false true (litEnc_neg h₁) (litEnc_pos (by simp) h₁)]
  · rw [ifEqLen_neg hc, if_neg hc, clause2_eq false false (litEnc_neg h₁) (litEnc_neg h₂)]

theorem amoEnc_mem_FP {w aW bW : List Bool → List Bool} (hw : w ∈ FP) (ha : aW ∈ FP)
    (hb : bW ∈ FP) : (fun z => amoEnc (w z) (aW z) (bW z)) ∈ FP :=
  ifEqLen_mem_FP ha hb
    (clause2_mem_FP hw (constFn_mem_FP []) ha (constFn_mem_FP [true]) ha)
    (clause2_mem_FP hw (constFn_mem_FP []) ha (constFn_mem_FP []) hb)

/-! ## The equality-bit clauses -/

/-- The `t`-th clause of an equality-bit block, encoded. -/
noncomputable def eqAuxEnc (w eU uU vU tU : List Bool) : List Bool :=
  ifEqLen (modC 4 tU) []
    (clause3 w [] (eU ++ divC 4 tU) [] (uU ++ divC 4 tU) [true] (vU ++ divC 4 tU))
    (ifEqLen (modC 4 tU) [true]
      (clause3 w [] (eU ++ divC 4 tU) [true] (uU ++ divC 4 tU) [] (vU ++ divC 4 tU))
      (ifEqLen (modC 4 tU) [true, true]
        (clause3 w [true] (eU ++ divC 4 tU) [] (uU ++ divC 4 tU) [] (vU ++ divC 4 tU))
        (clause3 w [true] (eU ++ divC 4 tU) [true] (uU ++ divC 4 tU) [true]
          (vU ++ divC 4 tU))))

theorem eqAuxEnc_eq (w eU uU vU tU : List Bool)
    (h₁ : eU.length + tU.length / 4 ≤ w.length)
    (h₂ : uU.length + tU.length / 4 ≤ w.length)
    (h₃ : vU.length + tU.length / 4 ≤ w.length) :
    eqAuxEnc w eU uU vU tU
      = DataEncode.bitstringEncode
          (if tU.length % 4 = 0 then
              [(false, eU.length + tU.length / 4), (false, uU.length + tU.length / 4),
                (true, vU.length + tU.length / 4)]
            else if tU.length % 4 = 1 then
              [(false, eU.length + tU.length / 4), (true, uU.length + tU.length / 4),
                (false, vU.length + tU.length / 4)]
            else if tU.length % 4 = 2 then
              [(true, eU.length + tU.length / 4), (false, uU.length + tU.length / 4),
                (false, vU.length + tU.length / 4)]
            else [(true, eU.length + tU.length / 4), (true, uU.length + tU.length / 4),
                (true, vU.length + tU.length / 4)]) := by
  have hd : (divC 4 tU).length = tU.length / 4 := by
    rw [divC_eq (by norm_num), List.length_replicate]
  have hm : (modC 4 tU).length = tU.length % 4 := by
    rw [modC_eq (by norm_num), List.length_replicate]
  have he : (eU ++ divC 4 tU).length = eU.length + tU.length / 4 := by
    rw [List.length_append, hd]
  have hu : (uU ++ divC 4 tU).length = uU.length + tU.length / 4 := by
    rw [List.length_append, hd]
  have hv : (vU ++ divC 4 tU).length = vU.length + tU.length / 4 := by
    rw [List.length_append, hd]
  rw [eqAuxEnc]
  by_cases c0 : tU.length % 4 = 0
  · rw [ifEqLen_pos (by rw [hm, c0]; rfl), if_pos c0,
      clause3_eq false false true (litEnc_neg (by rw [he]; exact h₁))
        (litEnc_neg (by rw [hu]; exact h₂))
        (litEnc_pos (by simp) (by rw [hv]; exact h₃)), he, hu, hv]
  · rw [ifEqLen_neg (by rw [hm]; simpa using c0), if_neg c0]
    by_cases c1 : tU.length % 4 = 1
    · rw [ifEqLen_pos (by rw [hm, c1]; rfl), if_pos c1,
        clause3_eq false true false (litEnc_neg (by rw [he]; exact h₁))
          (litEnc_pos (by simp) (by rw [hu]; exact h₂))
          (litEnc_neg (by rw [hv]; exact h₃)), he, hu, hv]
    · rw [ifEqLen_neg (by rw [hm]; simpa using c1), if_neg c1]
      by_cases c2 : tU.length % 4 = 2
      · rw [ifEqLen_pos (by rw [hm, c2]; rfl), if_pos c2,
          clause3_eq true false false (litEnc_pos (by simp) (by rw [he]; exact h₁))
            (litEnc_neg (by rw [hu]; exact h₂))
            (litEnc_neg (by rw [hv]; exact h₃)), he, hu, hv]
      · rw [ifEqLen_neg (by rw [hm]; simpa using c2), if_neg c2,
          clause3_eq true true true (litEnc_pos (by simp) (by rw [he]; exact h₁))
            (litEnc_pos (by simp) (by rw [hu]; exact h₂))
            (litEnc_pos (by simp) (by rw [hv]; exact h₃)), he, hu, hv]

/-- **An equality-bit clause matches the family it indexes.** -/
theorem eqAuxEnc_replicate_eq (w eU uU vU : List Bool) (W t : ℕ) (ht : t < W * 4)
    (h₁ : eU.length + t / 4 ≤ w.length) (h₂ : uU.length + t / 4 ≤ w.length)
    (h₃ : vU.length + t / 4 ≤ w.length) :
    ((QBF.eqAuxCNF W eU.length uU.length vU.length)[t]?).map DataEncode.bitstringEncode
      = some (eqAuxEnc w eU uU vU (List.replicate t true)) := by
  rw [eqAuxCNF_getElem?_eq W eU.length uU.length vU.length t ht,
    eqAuxEnc_eq w eU uU vU (List.replicate t true)
      (by rwa [List.length_replicate]) (by rwa [List.length_replicate])
      (by rwa [List.length_replicate]), List.length_replicate, Option.map_some]

theorem eqAuxEnc_mem_FP {w eU uU vU tU : List Bool → List Bool} (hw : w ∈ FP) (he : eU ∈ FP)
    (hu : uU ∈ FP) (hv : vU ∈ FP) (ht : tU ∈ FP) :
    (fun z => eqAuxEnc (w z) (eU z) (uU z) (vU z) (tU z)) ∈ FP := by
  have hd : (fun z => divC 4 (tU z)) ∈ FP := divC_mem_FP ht 4
  have hm : (fun z => modC 4 (tU z)) ∈ FP := modC_mem_FP ht 4
  have hE := Cobham.appendFn_mem_FP he hd
  have hU := Cobham.appendFn_mem_FP hu hd
  have hV := Cobham.appendFn_mem_FP hv hd
  have c₀ := clause3_mem_FP hw (constFn_mem_FP []) hE (constFn_mem_FP []) hU
    (constFn_mem_FP [true]) hV
  have c₁ := clause3_mem_FP hw (constFn_mem_FP []) hE (constFn_mem_FP [true]) hU
    (constFn_mem_FP []) hV
  have c₂ := clause3_mem_FP hw (constFn_mem_FP [true]) hE (constFn_mem_FP []) hU
    (constFn_mem_FP []) hV
  have c₃ := clause3_mem_FP hw (constFn_mem_FP [true]) hE (constFn_mem_FP [true]) hU
    (constFn_mem_FP [true]) hV
  exact ifEqLen_mem_FP hm (constFn_mem_FP []) c₀
    (ifEqLen_mem_FP hm (constFn_mem_FP [true]) c₁
      (ifEqLen_mem_FP hm (constFn_mem_FP [true, true]) c₂ c₃))

/-! ## Clauses that are a run of consecutive positive literals -/

/-- A clause of consecutive positive literals: variables `base, …, base + m - 1`, each clamped
to the width so that the emitter needs no side condition. -/
noncomputable def runEnc (wU baseU mU : List Bool) : List Bool :=
  DataEncode.bitstringEncode
    ((List.range mU.length).map fun j =>
      ((true, min (baseU.length + j) wU.length) : CLit))

theorem runEnc_eq (wU baseU mU : List Bool)
    (h : ∀ j, j < mU.length → baseU.length + j ≤ wU.length) :
    runEnc wU baseU mU
      = DataEncode.bitstringEncode
          ((List.range mU.length).map fun j => ((true, baseU.length + j) : CLit)) := by
  rw [runEnc]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  rw [Nat.min_eq_left (h j hj)]

/-- **The at-least-one clause of a one-hot group is emittable.** Its literals are positive and
its variables are consecutive, so the whole clause is one indexed family. -/
theorem runEnc_mem_FP {w baseU mU : List Bool → List Bool} (hw : w ∈ FP) (hb : baseU ∈ FP)
    (hm : mU ∈ FP) :
    (fun z => runEnc (w z) (baseU z) (mU z)) ∈ FP := by
  simp only [runEnc]
  have hwf : (fun y => w (pairFst y)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp pairFst_mem_FP hw) fun _ => rfl
  have hbf : (fun y => baseU (pairFst y)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp pairFst_mem_FP hb) fun _ => rfl
  refine emit_list_mem_FP (E := fun y => litEnc (w (pairFst y)) [true]
      (baseU (pairFst y) ++ pairSnd y)) ?_ ?_ ?_
  · exact litEnc_mem_FP hwf (constFn_mem_FP [true])
      (Cobham.appendFn_mem_FP hbf Cobham.sndBlock_mem_FP)
  · refine mem_FP_of_eq (divC_mem_FP hm 1) fun z => ?_
    rw [divC_eq (by norm_num), List.length_map, List.length_range, Nat.div_one]
  · intro z j hj
    rw [List.length_map, List.length_range] at hj
    have hlen : (baseU z ++ List.replicate j true).length = (baseU z).length + j := by
      rw [List.length_append, List.length_replicate]
    show litEnc (w (pairFst (pair z (List.replicate j true)))) [true]
      (baseU (pairFst (pair z (List.replicate j true)))
        ++ pairSnd (pair z (List.replicate j true))) = _
    rw [pairFst_pair, pairSnd_pair, litEnc_pos' (by simp), hlen]
    congr 1
    rw [List.getElem_map, List.getElem_range]

/-! ## One clause of a one-hot group -/

/-- One clause of a one-hot group: the at-least-one clause at index `0`, then the at-most-one
clauses, addressed by row and column. -/
noncomputable def oneHotEnc (w baseU base0U mU nU pU : List Bool) : List Bool :=
  ifEqLen pU [] (runEnc w baseU mU)
    (amoEnc w (base0U ++ divFn2 (pair nU (dropOne pU)))
      (base0U ++ modFn2 (pair nU (dropOne pU))))

theorem oneHotEnc_zero (w baseU base0U mU nU : List Bool) :
    oneHotEnc w baseU base0U mU nU [] = runEnc w baseU mU := by
  rw [oneHotEnc, ifEqLen_pos rfl]

theorem oneHotEnc_succ (w baseU base0U mU nU pU : List Bool) (hp : pU ≠ [])
    (hn : 0 < nU.length)
    (h₁ : base0U.length + (pU.length - 1) / nU.length ≤ w.length)
    (h₂ : base0U.length + (pU.length - 1) % nU.length ≤ w.length) :
    oneHotEnc w baseU base0U mU nU pU
      = DataEncode.bitstringEncode
          (if base0U.length + (pU.length - 1) / nU.length
                = base0U.length + (pU.length - 1) % nU.length then
              [(false, base0U.length + (pU.length - 1) / nU.length),
                (true, base0U.length + (pU.length - 1) / nU.length)]
            else [(false, base0U.length + (pU.length - 1) / nU.length),
                (false, base0U.length + (pU.length - 1) % nU.length)]) := by
  have hlen : pU.length ≠ 0 := fun h => hp (List.eq_nil_of_length_eq_zero h)
  have hd : (dropOne pU).length = pU.length - 1 := by
    rw [dropOne, List.length_drop]
  have hrow : (base0U ++ divFn2 (pair nU (dropOne pU))).length
      = base0U.length + (pU.length - 1) / nU.length := by
    rw [List.length_append, divFn2_eq hn, List.length_replicate, hd]
  have hcol : (base0U ++ modFn2 (pair nU (dropOne pU))).length
      = base0U.length + (pU.length - 1) % nU.length := by
    rw [List.length_append, modFn2_eq hn, List.length_replicate, hd]
  rw [oneHotEnc, ifEqLen_neg (by simpa using hlen),
    amoEnc_eq _ _ _ (by rw [hrow]; exact h₁) (by rw [hcol]; exact h₂), hrow, hcol]

theorem oneHotEnc_mem_FP {w baseU base0U mU nU pU : List Bool → List Bool} (hw : w ∈ FP)
    (hb : baseU ∈ FP) (hb0 : base0U ∈ FP) (hm : mU ∈ FP) (hn : nU ∈ FP) (hp : pU ∈ FP)
    :
    (fun z => oneHotEnc (w z) (baseU z) (base0U z) (mU z) (nU z) (pU z)) ∈ FP := by
  have hdrop : (fun z => dropOne (pU z)) ∈ FP := dropOneFn_mem_FP hp
  have hpair : (fun z => pair (nU z) (dropOne (pU z))) ∈ FP := Cobham.pairFn_mem_FP hn hdrop
  have hrow : (fun z => base0U z ++ divFn2 (pair (nU z) (dropOne (pU z)))) ∈ FP :=
    Cobham.appendFn_mem_FP hb0
      (mem_FP_of_eq (mem_FP_comp hpair divFn2_mem_FP) fun _ => rfl)
  have hcol : (fun z => base0U z ++ modFn2 (pair (nU z) (dropOne (pU z)))) ∈ FP :=
    Cobham.appendFn_mem_FP hb0
      (mem_FP_of_eq (mem_FP_comp hpair modFn2_mem_FP) fun _ => rfl)
  exact ifEqLen_mem_FP hp (constFn_mem_FP [])
    (runEnc_mem_FP hw hb hm) (amoEnc_mem_FP hw hrow hcol)

/-- A table lookup on two bounded indices, in unary. -/
noncomputable def tableU2 {A B : Type} (l : List A) (m : List B) (f : A → B → ℕ)
    (s t : List Bool) : List Bool :=
  List.replicate (match l[s.length]?, m[t.length]? with
    | some a, some b => f a b
    | _, _ => 0) true

theorem tableU2_length {A B : Type} (l : List A) (m : List B) (f : A → B → ℕ)
    (s t : List Bool) (hs : s.length < l.length) (ht : t.length < m.length) :
    (tableU2 l m f s t).length = f (l[s.length]'hs) (m[t.length]'ht) := by
  rw [tableU2, List.length_replicate, List.getElem?_eq_getElem hs,
    List.getElem?_eq_getElem ht]

theorem tableU2_mem_FP {A B : Type} (l : List A) (m : List B) (f : A → B → ℕ)
    {s t : List Bool → List Bool} (hs : s ∈ FP) (ht : t ∈ FP) {B₀ : ℕ}
    (hB : ∀ z, (pair (s z) (t z)).length ≤ B₀) :
    (fun z => tableU2 l m f (s z) (t z)) ∈ FP := by
  have hkey : (fun z => pair (s z) (t z)) ∈ FP := Cobham.pairFn_mem_FP hs ht
  have h := mem_FP_of_bounded_key hkey hB
    (fun p => tableU2 l m f (pairFst p) (pairSnd p))
  refine mem_FP_of_eq h fun z => ?_
  rw [pairFst_pair, pairSnd_pair]

/-! ## Powers, in unary -/

/-- One step of the unary power loop: keep the base, multiply the accumulator by it. -/
noncomputable def powStep (st : List Bool) : List Bool :=
  pair (pairFst st) (mulLen (pairSnd st) (pairFst st))

theorem powStep_iterate (b : List Bool) : ∀ (n m : ℕ),
    powStep^[n] (pair b (List.replicate m false))
      = pair b (List.replicate (m * b.length ^ n) false)
  | 0, m => by simp
  | n + 1, m => by
      rw [Function.iterate_succ_apply, powStep, pairFst_pair, pairSnd_pair, mulLen,
        List.length_replicate, powStep_iterate b n (m * b.length)]
      congr 2
      rw [Nat.pow_succ]
      ring

/-- `|base| ^ |t|`, in unary. -/
noncomputable def powU (baseU tU : List Bool) : List Bool :=
  pairSnd (powStep^[tU.length] (pair baseU [false]))

theorem powU_length (baseU tU : List Bool) :
    (powU baseU tU).length = baseU.length ^ tU.length := by
  rw [powU, show ([false] : List Bool) = List.replicate 1 false from rfl,
    powStep_iterate baseU tU.length 1, pairSnd_pair, List.length_replicate, Nat.one_mul]

theorem powStep_mem_FP : powStep ∈ FP :=
  Cobham.pairFn_mem_FP pairFst_mem_FP
    (mulLen_mem_FP Cobham.sndBlock_mem_FP pairFst_mem_FP)

/-- **The unary power is `FP`** as long as the exponent is bounded by a constant. -/
theorem powU_mem_FP {baseU tU : List Bool → List Bool} (hb : baseU ∈ FP) (ht : tU ∈ FP)
    (E : ℕ) (hE : ∀ z, (tU z).length ≤ E)
    {width : List Bool → List Bool} (hw : width ∈ FP)
    (hbound : ∀ z, (baseU z).length ^ E + 2 * (baseU z).length + 4 ≤ (width z).length) :
    (fun z => powU (baseU z) (tU z)) ∈ FP := by
  have hinit : (fun z => pair (baseU z) [false]) ∈ FP :=
    Cobham.pairFn_mem_FP hb (constFn_mem_FP [false])
  have hiter : (fun z => powStep^[(tU z).length] (pair (baseU z) [false])) ∈ FP := by
    refine Cobham.iterate_mem_FP powStep_mem_FP hinit ht hw fun z n hn => ?_
    rw [show ([false] : List Bool) = List.replicate 1 false from rfl,
      powStep_iterate (baseU z) n 1, pair_length, List.length_replicate, Nat.one_mul]
    have hmono : (baseU z).length ^ n ≤ (baseU z).length ^ E + 1 := by
      rcases Nat.eq_zero_or_pos (baseU z).length with h | h
      · rw [h]
        cases n with
        | zero => simp
        | succ m => simp
      · exact le_trans (Nat.pow_le_pow_right h (le_trans hn (hE z))) (by omega)
    have := hbound z
    omega
  exact mem_FP_of_eq (mem_FP_comp hiter Cobham.sndBlock_mem_FP) fun _ => rfl

/-- A view's head position on one tape, decoded from the view index. -/
noncomputable def headDigitU (horU tU iU : List Bool) : List Bool :=
  modFn2 (pair horU (divFn2 (pair (powU horU tU) iU)))

theorem headDigitU_length (horU tU iU : List Bool) (hhor : 0 < horU.length) :
    (headDigitU horU tU iU).length
      = iU.length / horU.length ^ tU.length % horU.length := by
  have hpow : 0 < (powU horU tU).length := by
    rw [powU_length]
    exact Nat.pow_pos hhor
  rw [headDigitU, modFn2_eq hhor, List.length_replicate, divFn2_eq hpow,
    List.length_replicate, powU_length]

/-- **The decoded digit is the view's head position.** -/
theorem headDigitU_eq_headTupleOf {k T : ℕ} (horU tU iU : List Bool)
    (i : Fin ((T + 1) ^ (k + 2))) (t : TapeSlot k) (hhor : horU.length = T + 1)
    (ht : tU.length = (tapeSlotEquiv k t).val) (hi : iU.length = i.val) :
    (headDigitU horU tU iU).length = (headTupleOf k T i t).val := by
  rw [headDigitU_length _ _ _ (by rw [hhor]; omega), hhor, ht, hi,
    headTupleOf_val k T i t]

theorem headDigitU_mem_FP {horU tU iU : List Bool → List Bool} (hhor : horU ∈ FP)
    (ht : tU ∈ FP) (hi : iU ∈ FP) (E : ℕ) (hE : ∀ z, (tU z).length ≤ E)
    {width : List Bool → List Bool} (hw : width ∈ FP)
    (hbound : ∀ z, (horU z).length ^ E + 2 * (horU z).length + 4 ≤ (width z).length) :
    (fun z => headDigitU (horU z) (tU z) (iU z)) ∈ FP := by
  have hpow : (fun z => powU (horU z) (tU z)) ∈ FP :=
    powU_mem_FP hhor ht E hE hw hbound
  have hdiv : (fun z => divFn2 (pair (powU (horU z) (tU z)) (iU z))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hpow hi) divFn2_mem_FP) fun _ => rfl
  exact mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hhor hdiv) modFn2_mem_FP)
    fun _ => rfl

/-! ## Reading a bit of the input -/

/-- The `j`-th bit of `x`, as a flag: non-empty exactly when that bit is `true`. -/
noncomputable def bitU (x jU : List Bool) : List Bool :=
  headFlag true (x.drop jU.length)

theorem bitU_eq (x jU : List Bool) :
    bitU x jU = if x[jU.length]? = some true then [false] else [] := by
  rw [bitU, headFlag, List.head?_drop]

theorem bitU_ne_nil_iff (x jU : List Bool) : bitU x jU ≠ [] ↔ x[jU.length]? = some true := by
  rw [bitU_eq]
  by_cases h : x[jU.length]? = some true
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    simp [h]

theorem bitU_mem_FP {x jU : List Bool → List Bool} (hx : x ∈ FP) (hj : jU ∈ FP) :
    (fun z => bitU (x z) (jU z)) ∈ FP := by
  have hdrop := dropLenFn_mem_FP hj hx
  exact mem_FP_of_eq (mem_FP_comp hdrop (headFlag_mem_FP true)) fun _ => rfl

/-- The index of the symbol the input tape holds at a position, in unary. -/
noncomputable def symStartInput (x pU : List Bool) : List Bool :=
  ifEqLen pU [] [false, false, false]
    (ifLtLen (dropOne pU) x (bitU x (dropOne pU)) [false, false])

theorem symStartInput_length (x pU : List Bool) :
    (symStartInput x pU).length
      = (symbolIndex ((Tape.init (x.map Γ.ofBool)).cells pU.length)).val := by
  have hd : (dropOne pU).length = pU.length - 1 := by rw [dropOne, List.length_drop]
  rw [symStartInput]
  by_cases h0 : pU.length = 0
  · rw [ifEqLen_pos (by rw [h0]; rfl), h0, Tape.init_cells_zero]
    rfl
  · rw [ifEqLen_neg (by simpa using h0)]
    by_cases hlt : pU.length - 1 < x.length
    · rw [ifLtLen_pos (by rw [hd]; simpa using hlt), bitU_eq]
      have hget : (x.map Γ.ofBool)[pU.length - 1]? = some (Γ.ofBool (x[pU.length - 1]'hlt)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hlt]
        rfl
      have hcell : (Tape.init (x.map Γ.ofBool)).cells pU.length
          = Γ.ofBool (x[pU.length - 1]'hlt) := by
        show (if pU.length = 0 then Γ.start
          else ((x.map Γ.ofBool)[pU.length - 1]?).getD Γ.blank) = _
        rw [if_neg h0, hget]
        rfl
      rw [hcell, hd]
      cases hb : x[pU.length - 1]'hlt
      · rw [if_neg (by rw [List.getElem?_eq_getElem hlt, hb]; simp)]
        rfl
      · rw [if_pos (by rw [List.getElem?_eq_getElem hlt, hb])]
        rfl
    · rw [ifLtLen_neg (by rw [hd]; simpa using hlt)]
      have hget : (x.map Γ.ofBool)[pU.length - 1]? = none := by
        rw [List.getElem?_eq_none (by rw [List.length_map]; omega)]
      have hcell : (Tape.init (x.map Γ.ofBool)).cells pU.length = Γ.blank := by
        show (if pU.length = 0 then Γ.start
          else ((x.map Γ.ofBool)[pU.length - 1]?).getD Γ.blank) = _
        rw [if_neg h0, hget]
        rfl
      rw [hcell]
      rfl

theorem symStartInput_mem_FP {x pU : List Bool → List Bool} (hx : x ∈ FP) (hp : pU ∈ FP) :
    (fun z => symStartInput (x z) (pU z)) ∈ FP :=
  ifEqLen_mem_FP hp (constFn_mem_FP []) (constFn_mem_FP _)
    (ifLtLen_mem_FP (dropOneFn_mem_FP hp) hx (bitU_mem_FP hx (dropOneFn_mem_FP hp))
      (constFn_mem_FP _))

/-- The symbol index a work or output tape holds at a position, in unary: blank beyond its
bound, otherwise the whole alphabet starting at index `0`. -/
noncomputable def symStartBeyond (boundU pU : List Bool) : List Bool :=
  ifLtLen boundU pU [false, false] []

/-- How many symbols such a cell may hold, in unary. -/
noncomputable def symCountBeyond (boundU pU : List Bool) : List Bool :=
  ifLtLen boundU pU [false] [false, false, false, false]

theorem symStartBeyond_length (boundU pU : List Bool) :
    (symStartBeyond boundU pU).length = if boundU.length < pU.length then 2 else 0 := by
  rw [symStartBeyond]
  by_cases h : boundU.length < pU.length
  · rw [ifLtLen_pos h, if_pos h]
    rfl
  · rw [ifLtLen_neg h, if_neg h]
    rfl

theorem symCountBeyond_length (boundU pU : List Bool) :
    (symCountBeyond boundU pU).length = if boundU.length < pU.length then 1 else 4 := by
  rw [symCountBeyond]
  by_cases h : boundU.length < pU.length
  · rw [ifLtLen_pos h, if_pos h]
    rfl
  · rw [ifLtLen_neg h, if_neg h]
    rfl

theorem symStartBeyond_mem_FP {boundU pU : List Bool → List Bool} (hb : boundU ∈ FP)
    (hp : pU ∈ FP) : (fun z => symStartBeyond (boundU z) (pU z)) ∈ FP :=
  ifLtLen_mem_FP hb hp (constFn_mem_FP _) (constFn_mem_FP _)

theorem symCountBeyond_mem_FP {boundU pU : List Bool → List Bool} (hb : boundU ∈ FP)
    (hp : pU ∈ FP) : (fun z => symCountBeyond (boundU z) (pU z)) ∈ FP :=
  ifLtLen_mem_FP hb hp (constFn_mem_FP _) (constFn_mem_FP _)

/-! ## The state group of a block -/

/-- One clause of a block's state group, encoded: the wires are `off, …, off + |Q| - 1`. -/
noncomputable def stateGroupEnc (w offU qU pU : List Bool) : List Bool :=
  oneHotEnc w offU offU qU qU pU

theorem stateGroupEnc_zero (w offU qU : List Bool) :
    stateGroupEnc w offU qU [] = runEnc w offU qU :=
  oneHotEnc_zero w offU offU qU qU

/-- **The state group's first clause is emitted correctly.** -/
theorem stateGroupEnc_zero_eq (w offU qU : List Bool)
    (hq : qU.length = Fintype.card tm.Q)
    (hb : ∀ j, j < qU.length → offU.length + j ≤ w.length) :
    stateGroupEnc w offU qU []
      = DataEncode.bitstringEncode (QBF.atLeastOneClause
          (fun q : tm.Q => configWire tm T offU.length (.state q)) (stateList tm)) := by
  rw [stateGroupEnc_zero, runEnc_eq w offU qU hb, atLeastOneClause_state_eq, hq]

/-- **The state group's later clauses are emitted correctly.** -/
theorem stateGroupEnc_succ_eq (w offU qU pU : List Bool) (hp : pU ≠ [])
    (hq : qU.length = Fintype.card tm.Q) (hpos : 0 < Fintype.card tm.Q)
    (h₁ : offU.length + (pU.length - 1) / Fintype.card tm.Q ≤ w.length)
    (h₂ : offU.length + (pU.length - 1) % Fintype.card tm.Q ≤ w.length) :
    stateGroupEnc w offU qU pU
      = DataEncode.bitstringEncode
          (if offU.length + (pU.length - 1) / Fintype.card tm.Q
                = offU.length + (pU.length - 1) % Fintype.card tm.Q then
              [(false, offU.length + (pU.length - 1) / Fintype.card tm.Q),
                (true, offU.length + (pU.length - 1) / Fintype.card tm.Q)]
            else [(false, offU.length + (pU.length - 1) / Fintype.card tm.Q),
                (false, offU.length + (pU.length - 1) % Fintype.card tm.Q)]) := by
  rw [stateGroupEnc, oneHotEnc_succ w offU offU qU qU pU hp (by rw [hq]; exact hpos)
    (by rw [hq]; exact h₁) (by rw [hq]; exact h₂), hq]

theorem stateGroupEnc_mem_FP {w offU qU pU : List Bool → List Bool} (hw : w ∈ FP)
    (hoff : offU ∈ FP) (hq : qU ∈ FP) (hp : pU ∈ FP)
    :
    (fun z => stateGroupEnc (w z) (offU z) (qU z) (pU z)) ∈ FP :=
  oneHotEnc_mem_FP hw hoff hoff hq hq hp

/-! ## The head group of a tape -/

/-- One clause of a tape's head group, encoded. -/
noncomputable def headGroupEnc (w offU qU tapeU horU mU pU : List Bool) : List Bool :=
  oneHotEnc w (headWireU offU qU tapeU [] horU) (headWireU offU qU tapeU [] horU) mU horU
    pU

/-- **The head group's first clause is emitted correctly.** -/
theorem headGroupEnc_zero_eq (w offU qU tapeU horU mU : List Bool) (tape : TapeSlot k)
    (n S : ℕ) (hq : qU.length = Fintype.card tm.Q) (htape : tapeU.length = tape.index.val)
    (hhor : horU.length = T + 1)
    (hm : mU.length = min (headBound n S tape + 1) (T + 1))
    (hb : ∀ j, j < mU.length →
      (headWireU offU qU tapeU [] horU).length + j ≤ w.length) :
    headGroupEnc w offU qU tapeU horU mU []
      = DataEncode.bitstringEncode (QBF.atLeastOneClause
          (fun p : Fin (T + 1) => configWire tm T offU.length (.head tape p))
          (allowedHeads T n S tape)) := by
  have hlist : (List.range mU.length).map
      (fun j => ((true, (headWireU offU qU tapeU [] horU).length + j) : CLit))
      = (List.range (min (headBound n S tape + 1) (T + 1))).map fun j =>
          ((true, offU.length + (Fintype.card tm.Q + tape.index.val * (T + 1) + j)) : CLit) := by
    rw [hm, headWireU_length, hq, htape, hhor]
    refine List.map_congr_left fun j _ => ?_
    congr 1
    simp only [List.length_nil]
    omega
  rw [headGroupEnc, oneHotEnc_zero,
    runEnc_eq w (headWireU offU qU tapeU [] horU) mU hb, hlist,
    ← atLeastOneClause_head_eq]

theorem headGroupEnc_mem_FP {w offU qU tapeU horU mU pU : List Bool → List Bool} (hw : w ∈ FP)
    (hoff : offU ∈ FP) (hq : qU ∈ FP) (htape : tapeU ∈ FP) (hhor : horU ∈ FP) (hm : mU ∈ FP)
    (hp : pU ∈ FP)
    :
    (fun z => headGroupEnc (w z) (offU z) (qU z) (tapeU z) (horU z) (mU z) (pU z)) ∈ FP :=
  oneHotEnc_mem_FP hw
    (headWireU_mem_FP hoff hq htape (constFn_mem_FP []) hhor)
    (headWireU_mem_FP hoff hq htape (constFn_mem_FP []) hhor) hm hhor hp

/-! ## The cell group of a position -/

/-- One clause of a cell group, encoded. -/
noncomputable def cellGroupEnc (w offU qU hdU tapeU posU horU startU mU pU : List Bool) :
    List Bool :=
  oneHotEnc w (cellWireU offU qU hdU tapeU posU horU startU)
    (cellWireU offU qU hdU tapeU posU horU []) mU [false, false, false, false] pU

/-- **The cell group's first clause is emitted correctly.** -/
theorem cellGroupEnc_zero_eq (w offU qU hdU tapeU posU horU startU mU : List Bool)
    (x : List Bool) (S : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2))
    (hq : qU.length = Fintype.card tm.Q) (hhd : hdU.length = (k + 2) * (T + 1))
    (htape : tapeU.length = tape.index.val) (hpos : posU.length = pos.val)
    (hhor : horU.length = T + 2) (hstart : startU.length = symStart T x S tape pos)
    (hm : mU.length = (allowedSyms T x S tape pos).length)
    (hb : ∀ j, j < mU.length →
      (cellWireU offU qU hdU tapeU posU horU startU).length + j ≤ w.length) :
    cellGroupEnc w offU qU hdU tapeU posU horU startU mU []
      = DataEncode.bitstringEncode (QBF.atLeastOneClause
          (fun s : Γ => configWire tm T offU.length (.cell tape pos s))
          (allowedSyms T x S tape pos)) := by
  have hlist : (List.range mU.length).map
      (fun j => ((true, (cellWireU offU qU hdU tapeU posU horU startU).length + j) : CLit))
      = (List.range (allowedSyms T x S tape pos).length).map fun j =>
          ((true, offU.length
            + (cellBase tm T tape pos + (symStart T x S tape pos + j))) : CLit) := by
    rw [hm, cellWireU_length, hq, hhd, htape, hpos, hhor, hstart]
    refine List.map_congr_left fun j _ => ?_
    congr 1
    rw [cellBase]
    omega
  rw [cellGroupEnc, oneHotEnc_zero,
    runEnc_eq w (cellWireU offU qU hdU tapeU posU horU startU) mU hb, hlist,
    ← atLeastOneClause_cell_eq]

theorem cellGroupEnc_mem_FP
    {w offU qU hdU tapeU posU horU startU mU pU : List Bool → List Bool} (hw : w ∈ FP)
    (hoff : offU ∈ FP) (hq : qU ∈ FP) (hhd : hdU ∈ FP) (htape : tapeU ∈ FP)
    (hpos : posU ∈ FP) (hhor : horU ∈ FP) (hstart : startU ∈ FP) (hm : mU ∈ FP)
    (hp : pU ∈ FP) :
    (fun z => cellGroupEnc (w z) (offU z) (qU z) (hdU z) (tapeU z) (posU z) (horU z)
      (startU z) (mU z) (pU z)) ∈ FP :=
  oneHotEnc_mem_FP hw (cellWireU_mem_FP hoff hq hhd htape hpos hhor hstart)
    (cellWireU_mem_FP hoff hq hhd htape hpos hhor (constFn_mem_FP [])) hm
    (constFn_mem_FP _) hp

/-! ## The tape-dependent parameters -/

/-- How far a tape's head may travel, in unary: the input tape spans the input and the work
space, the output tape one more cell than the work space, a work tape exactly it. -/
noncomputable def headBoundU (x SU tapeU lastU : List Bool) : List Bool :=
  ifEqLen tapeU [] (x ++ (SU ++ [false]))
    (ifEqLen tapeU lastU (SU ++ [false]) SU)

theorem headBoundU_input (x SU lastU : List Bool) :
    (headBoundU x SU [] lastU).length = x.length + SU.length + 1 := by
  rw [headBoundU, ifEqLen_pos rfl, List.length_append, List.length_append]
  simp
  omega

theorem headBoundU_mem_FP {x SU tapeU lastU : List Bool → List Bool} (hx : x ∈ FP)
    (hS : SU ∈ FP) (ht : tapeU ∈ FP) (hl : lastU ∈ FP) :
    (fun z => headBoundU (x z) (SU z) (tapeU z) (lastU z)) ∈ FP := by
  have hS1 : (fun z => SU z ++ [false]) ∈ FP :=
    Cobham.appendFn_mem_FP hS (constFn_mem_FP [false])
  exact ifEqLen_mem_FP ht (constFn_mem_FP [])
    (Cobham.appendFn_mem_FP hx hS1)
    (ifEqLen_mem_FP ht hl hS1 hS)

/-- How many head positions a tape's group allows, in unary. -/
noncomputable def headCountU (x SU tapeU lastU horU : List Bool) : List Bool :=
  horU.take (headBoundU x SU tapeU lastU ++ [false]).length

theorem headCountU_length (x SU tapeU lastU horU : List Bool) :
    (headCountU x SU tapeU lastU horU).length
      = min horU.length ((headBoundU x SU tapeU lastU).length + 1) := by
  rw [headCountU, List.length_take, List.length_append]
  simp only [List.length_cons, List.length_nil]
  omega

theorem headCountU_mem_FP {x SU tapeU lastU horU : List Bool → List Bool} (hx : x ∈ FP)
    (hS : SU ∈ FP) (ht : tapeU ∈ FP) (hl : lastU ∈ FP) (hhor : horU ∈ FP) :
    (fun z => headCountU (x z) (SU z) (tapeU z) (lastU z) (horU z)) ∈ FP :=
  Cobham.takeLenFn_mem_FP
    (Cobham.appendFn_mem_FP (headBoundU_mem_FP hx hS ht hl) (constFn_mem_FP [false])) hhor

/-- Where a cell's run of allowed symbols starts, in unary. -/
noncomputable def symStartU (x SU tapeU lastU posU : List Bool) : List Bool :=
  ifEqLen tapeU [] (symStartInput x posU)
    (ifEqLen tapeU lastU (symStartBeyond (SU ++ [false]) posU) (symStartBeyond SU posU))

/-- How many symbols a cell may hold, in unary. -/
noncomputable def symCountU (SU tapeU lastU posU : List Bool) : List Bool :=
  ifEqLen tapeU [] [false]
    (ifEqLen tapeU lastU (symCountBeyond (SU ++ [false]) posU) (symCountBeyond SU posU))

theorem symStartU_input (x SU lastU posU : List Bool) :
    symStartU x SU [] lastU posU = symStartInput x posU := by
  rw [symStartU, ifEqLen_pos rfl]

theorem symCountU_input (SU lastU posU : List Bool) :
    (symCountU SU [] lastU posU).length = 1 := by
  rw [symCountU, ifEqLen_pos rfl]
  rfl

theorem symStartU_mem_FP {x SU tapeU lastU posU : List Bool → List Bool} (hx : x ∈ FP)
    (hS : SU ∈ FP) (ht : tapeU ∈ FP) (hl : lastU ∈ FP) (hpos : posU ∈ FP) :
    (fun z => symStartU (x z) (SU z) (tapeU z) (lastU z) (posU z)) ∈ FP := by
  have hS1 : (fun z => SU z ++ [false]) ∈ FP :=
    Cobham.appendFn_mem_FP hS (constFn_mem_FP [false])
  exact ifEqLen_mem_FP ht (constFn_mem_FP []) (symStartInput_mem_FP hx hpos)
    (ifEqLen_mem_FP ht hl (symStartBeyond_mem_FP hS1 hpos)
      (symStartBeyond_mem_FP hS hpos))

theorem symCountU_mem_FP {SU tapeU lastU posU : List Bool → List Bool} (hS : SU ∈ FP)
    (ht : tapeU ∈ FP) (hl : lastU ∈ FP) (hpos : posU ∈ FP) :
    (fun z => symCountU (SU z) (tapeU z) (lastU z) (posU z)) ∈ FP := by
  have hS1 : (fun z => SU z ++ [false]) ∈ FP :=
    Cobham.appendFn_mem_FP hS (constFn_mem_FP [false])
  exact ifEqLen_mem_FP ht (constFn_mem_FP []) (constFn_mem_FP _)
    (ifEqLen_mem_FP ht hl (symCountBeyond_mem_FP hS1 hpos)
      (symCountBeyond_mem_FP hS hpos))

/-- **The tape branch computes the right head bound.** -/
theorem headBoundU_length (x SU tapeU lastU : List Bool) (tape : TapeSlot k)
    (htape : tapeU.length = tape.index.val) (hlast : lastU.length = k + 1) :
    (headBoundU x SU tapeU lastU).length = headBound x.length SU.length tape := by
  cases tape with
  | input =>
      rw [headBoundU, ifEqLen_pos (by rw [htape]; rfl)]
      simp [headBound]
      omega
  | work i =>
      have hne : tapeU.length ≠ ([] : List Bool).length := by
        rw [htape]
        simp [TapeSlot.index]
      have hne2 : tapeU.length ≠ lastU.length := by
        rw [htape, hlast]
        have := i.isLt
        simp only [TapeSlot.index]
        omega
      rw [headBoundU, ifEqLen_neg hne, ifEqLen_neg hne2]
      rfl
  | output =>
      have hne : tapeU.length ≠ ([] : List Bool).length := by
        rw [htape]
        simp [TapeSlot.index]
      rw [headBoundU, ifEqLen_neg hne, ifEqLen_pos (by rw [htape, hlast]; rfl)]
      simp [headBound]

theorem headCountU_length_eq (x SU tapeU lastU horU : List Bool) (tape : TapeSlot k)
    (htape : tapeU.length = tape.index.val) (hlast : lastU.length = k + 1)
    (hhor : horU.length = T + 1) :
    (headCountU x SU tapeU lastU horU).length
      = min (headBound x.length SU.length tape + 1) (T + 1) := by
  rw [headCountU_length, headBoundU_length x SU tapeU lastU tape htape hlast, hhor,
    Nat.min_comm]

/-! ## The validity clauses of a block -/

/-- The size of one cell group, in unary. -/
def cellSizeU : List Bool := List.replicate (1 + 4 * 4) false

@[simp] theorem cellSizeU_length : cellSizeU.length = 1 + 4 * 4 := by
  rw [cellSizeU, List.length_replicate]

/-- One clause of a tape's block: its head group, then one cell group per position. -/
noncomputable def tapeBlockEnc (w offU qU hdU horU hor2U x SU lastU tapeU hsU rU : List Bool) :
    List Bool :=
  ifLtLen rU hsU
    (headGroupEnc w offU qU tapeU horU (headCountU x SU tapeU lastU horU) rU)
    (cellGroupEnc w offU qU hdU tapeU
      (divFn2 (pair cellSizeU (rU.drop hsU.length))) hor2U
      (symStartU x SU tapeU lastU (divFn2 (pair cellSizeU (rU.drop hsU.length))))
      (symCountU SU tapeU lastU (divFn2 (pair cellSizeU (rU.drop hsU.length))))
      (modFn2 (pair cellSizeU (rU.drop hsU.length))))

/-- One clause of a block's validity group. -/
noncomputable def validEnc (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU : List Bool) :
    List Bool :=
  ifLtLen pU sqU (stateGroupEnc w offU qU pU)
    (tapeBlockEnc w offU qU hdU horU hor2U x SU lastU
      (divFn2 (pair tbU (pU.drop sqU.length))) hsU
      (modFn2 (pair tbU (pU.drop sqU.length))))

theorem tapeBlockEnc_mem_FP
    {w offU qU hdU horU hor2U x SU lastU tapeU hsU rU : List Bool → List Bool} (hw : w ∈ FP)
    (hoff : offU ∈ FP) (hq : qU ∈ FP) (hhd : hdU ∈ FP) (hhor : horU ∈ FP)
    (hhor2 : hor2U ∈ FP) (hx : x ∈ FP) (hS : SU ∈ FP) (hl : lastU ∈ FP)
    (ht : tapeU ∈ FP) (hhs : hsU ∈ FP) (hr : rU ∈ FP)
    :
    (fun z => tapeBlockEnc (w z) (offU z) (qU z) (hdU z) (horU z) (hor2U z) (x z) (SU z)
      (lastU z) (tapeU z) (hsU z) (rU z)) ∈ FP := by
  have hdrop : (fun z => (rU z).drop (hsU z).length) ∈ FP := dropLenFn_mem_FP hhs hr
  have hpair : (fun z => pair cellSizeU ((rU z).drop (hsU z).length)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP _) hdrop
  have hposF : (fun z => divFn2 (pair cellSizeU ((rU z).drop (hsU z).length))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hpair divFn2_mem_FP) fun _ => rfl
  have hcolF : (fun z => modFn2 (pair cellSizeU ((rU z).drop (hsU z).length))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hpair modFn2_mem_FP) fun _ => rfl
  exact ifLtLen_mem_FP hr hhs
    (headGroupEnc_mem_FP hw hoff hq ht hhor (headCountU_mem_FP hx hS ht hl hhor) hr)
    (cellGroupEnc_mem_FP hw hoff hq hhd ht hposF hhor2
      (symStartU_mem_FP hx hS ht hl hposF) (symCountU_mem_FP hS ht hl hposF) hcolF)

/-- The tape a validity clause index falls in. -/
noncomputable def tapeOfIdx (sqU tbU pU : List Bool) : List Bool :=
  divFn2 (pair tbU (pU.drop sqU.length))

/-- Where inside its tape block a validity clause index falls. -/
noncomputable def offInTape (sqU tbU pU : List Bool) : List Bool :=
  modFn2 (pair tbU (pU.drop sqU.length))

theorem tapeOfIdx_length (sqU tbU pU : List Bool) (htb : 0 < tbU.length) :
    (tapeOfIdx sqU tbU pU).length = (pU.length - sqU.length) / tbU.length := by
  rw [tapeOfIdx, divFn2_eq htb, List.length_replicate, List.length_drop]

theorem offInTape_length (sqU tbU pU : List Bool) (htb : 0 < tbU.length) :
    (offInTape sqU tbU pU).length = (pU.length - sqU.length) % tbU.length := by
  rw [offInTape, modFn2_eq htb, List.length_replicate, List.length_drop]

theorem tapeSlotEquiv_symm_index (i : Fin (k + 2)) :
    ((tapeSlotEquiv k).symm i).index.val = i.val :=
  congrArg Fin.val ((tapeSlotEquiv k).apply_symm_apply i)

theorem finRange_getElem? (n i : ℕ) (hi : i < n) :
    (List.finRange n)[i]? = some ⟨i, hi⟩ := by
  rw [List.getElem?_eq_getElem (by rw [List.length_finRange]; exact hi),
    List.getElem_finRange]
  rfl

theorem tapeList_getElem? (i : ℕ) (hi : i < k + 2) :
    (tapeList k)[i]? = some ((tapeSlotEquiv k).symm ⟨i, hi⟩) := by
  have hlen : i < (List.finRange (k + 2)).length := by
    rw [List.length_finRange]; exact hi
  rw [tapeList, List.getElem?_map, List.getElem?_eq_getElem hlen, List.getElem_finRange]
  rfl

theorem tapeOfIdx_mem_FP {sqU tbU pU : List Bool → List Bool} (hsq : sqU ∈ FP)
    (htb : tbU ∈ FP) (hp : pU ∈ FP) :
    (fun z => tapeOfIdx (sqU z) (tbU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP htb (dropLenFn_mem_FP hsq hp))
    divFn2_mem_FP) fun _ => rfl

theorem offInTape_mem_FP {sqU tbU pU : List Bool → List Bool} (hsq : sqU ∈ FP)
    (htb : tbU ∈ FP) (hp : pU ∈ FP) :
    (fun z => offInTape (sqU z) (tbU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP htb (dropLenFn_mem_FP hsq hp))
    modFn2_mem_FP) fun _ => rfl

theorem validEnc_eq_dispatch (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU : List Bool) :
    validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
      = ifLtLen pU sqU (stateGroupEnc w offU qU pU)
        (tapeBlockEnc w offU qU hdU horU hor2U x SU lastU
          (tapeOfIdx sqU tbU pU) hsU (offInTape sqU tbU pU)) := rfl

theorem validEnc_mem_FP
    {w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU : List Bool → List Bool}
    (hw : w ∈ FP) (hoff : offU ∈ FP) (hq : qU ∈ FP) (hsq : sqU ∈ FP) (htb : tbU ∈ FP)
    (hhd : hdU ∈ FP) (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP) (hx : x ∈ FP) (hS : SU ∈ FP)
    (hl : lastU ∈ FP) (hhs : hsU ∈ FP) (hp : pU ∈ FP)
    :
    (fun z => validEnc (w z) (offU z) (qU z) (sqU z) (tbU z) (hdU z) (horU z) (hor2U z)
      (x z) (SU z) (lastU z) (hsU z) (pU z)) ∈ FP := by
  refine mem_FP_of_eq (ifLtLen_mem_FP hp hsq (stateGroupEnc_mem_FP hw hoff hq hp)
    (tapeBlockEnc_mem_FP hw hoff hq hhd hhor hhor2 hx hS hl
      (tapeOfIdx_mem_FP hsq htb hp) hhs (offInTape_mem_FP hsq htb hp))) fun z => ?_
  rw [validEnc_eq_dispatch]

/-- **The validity dispatch emits the state group's first clause correctly.** -/
theorem validEnc_state_zero_eq (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU : List Bool)
    (hsqpos : 0 < sqU.length) (hq : qU.length = Fintype.card tm.Q)
    (hb : ∀ j, j < qU.length → offU.length + j ≤ w.length) :
    validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU []
      = DataEncode.bitstringEncode (QBF.atLeastOneClause
          (fun q : tm.Q => configWire tm T offU.length (.state q)) (stateList tm)) := by
  rw [validEnc, ifLtLen_pos (by simpa using hsqpos),
    stateGroupEnc_zero_eq tm T w offU qU hq hb]

/-- The state group's first clause is the first clause of the whole validity group. -/
theorem cfgValidC_getElem?_zero (x : List Bool) (S off : ℕ) :
    (cfgValidC tm T x S off)[0]?
      = some (QBF.atLeastOneClause
          (fun q : tm.Q => configWire tm T off (.state q)) (stateList tm)) := by
  rw [cfgValidC_getElem?_state tm T x S off 0 (by omega), stateGroupC,
    oneHotClauses_getElem?_head]

/-- The wire of the `j`-th state is `off + j`. -/
theorem configWire_stateList (off j : ℕ) (hj : j < Fintype.card tm.Q) :
    configWire tm T off (.state ((stateList tm)[j]'(by rw [stateList_length]; exact hj)))
      = off + j := by
  rw [configWire, configIndex, stateIndex_stateList tm j hj]

/-- **The state group's later clauses, spelled out.** -/
theorem stateGroupC_getElem?_succ (off p : ℕ) (hpos : 0 < Fintype.card tm.Q)
    (hp : p < Fintype.card tm.Q * Fintype.card tm.Q) :
    (stateGroupC tm T off)[p + 1]?
      = some (if off + p / Fintype.card tm.Q = off + p % Fintype.card tm.Q then
            [(false, off + p / Fintype.card tm.Q), (true, off + p / Fintype.card tm.Q)]
          else [(false, off + p / Fintype.card tm.Q),
            (false, off + p % Fintype.card tm.Q)]) := by
  have hlen : (stateList tm).length = Fintype.card tm.Q := stateList_length tm
  have hdiv : p / Fintype.card tm.Q < Fintype.card tm.Q :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hp)
  have hmod : p % Fintype.card tm.Q < Fintype.card tm.Q := Nat.mod_lt _ hpos
  rw [stateGroupC, oneHotClauses_getElem?_tail,
    atMostOneClauses_getElem? _ _ (by rw [hlen]; exact hpos) p (by rw [hlen]; exact hp), hlen,
    List.getElem?_eq_getElem (by rw [hlen]; exact hdiv),
    List.getElem?_eq_getElem (by rw [hlen]; exact hmod)]
  simp only [Option.bind_some, Option.map_some]
  rw [configWire_stateList tm T off _ hdiv, configWire_stateList tm T off _ hmod]

/-- The wire of the `j`-th head position of a tape. -/
theorem configWire_finRange_head (off j : ℕ) (hj : j < T + 1) (tape : TapeSlot k) :
    configWire tm T off
        (.head tape ((List.finRange (T + 1))[j]'(by rw [List.length_finRange]; exact hj)))
      = off + (Fintype.card tm.Q + tape.index.val * (T + 1) + j) := by
  rw [List.getElem_finRange, configWire, configIndex]
  rfl

/-- **The head group's later clauses, spelled out.** -/
theorem headGroupC_getElem?_succ (n S off p : ℕ) (tape : TapeSlot k)
    (hp : p < (T + 1) * (T + 1)) :
    (headGroupC tm T n S off tape)[p + 1]?
      = some (if off + (Fintype.card tm.Q + tape.index.val * (T + 1) + p / (T + 1))
                = off + (Fintype.card tm.Q + tape.index.val * (T + 1) + p % (T + 1)) then
            [(false, off + (Fintype.card tm.Q + tape.index.val * (T + 1) + p / (T + 1))),
              (true, off + (Fintype.card tm.Q + tape.index.val * (T + 1) + p / (T + 1)))]
          else
            [(false, off + (Fintype.card tm.Q + tape.index.val * (T + 1) + p / (T + 1))),
              (false, off + (Fintype.card tm.Q + tape.index.val * (T + 1)
                + p % (T + 1)))]) := by
  have hlen : (List.finRange (T + 1)).length = T + 1 := List.length_finRange
  have hdiv : p / (T + 1) < T + 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hp)
  have hmod : p % (T + 1) < T + 1 := Nat.mod_lt _ (by omega)
  rw [headGroupC, oneHotClauses_getElem?_tail,
    atMostOneClauses_getElem? _ _ (by rw [hlen]; omega) p (by rw [hlen]; exact hp), hlen,
    List.getElem?_eq_getElem (by rw [hlen]; exact hdiv),
    List.getElem?_eq_getElem (by rw [hlen]; exact hmod)]
  simp only [Option.bind_some, Option.map_some]
  rw [configWire_finRange_head tm T off _ hdiv tape,
    configWire_finRange_head tm T off _ hmod tape]

/-- The wire of a cell's symbol zero. -/
theorem cellWireU_zero (off : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2))
    {offU qU hdU tapeU posU horU : List Bool} (hoff : offU.length = off)
    (hq : qU.length = Fintype.card tm.Q) (hhd : hdU.length = (k + 2) * (T + 1))
    (htape : tapeU.length = tape.index.val) (hpos : posU.length = pos.val)
    (hhor : horU.length = T + 2) :
    (cellWireU offU qU hdU tapeU posU horU []).length = off + cellBase tm T tape pos := by
  rw [cellWireU_length, hoff, hq, hhd, htape, hpos, hhor, cellBase]
  simp only [List.length_nil]
  ring

/-- The wire of the `j`-th symbol of a cell. -/
theorem configWire_symbolList (off j : ℕ) (hj : j < 4) (tape : TapeSlot k)
    (pos : Fin (T + 2)) :
    configWire tm T off
        (.cell tape pos (symbolList[j]'(by rw [symbolList_length]; exact hj)))
      = off + (cellBase tm T tape pos + j) := by
  rw [configWire, configIndex, cellBase, symbolIndex_symbolList j hj]

/-- **The cell group's later clauses, spelled out.** -/
theorem cellGroupC_getElem?_succ (x : List Bool) (S off p : ℕ) (tape : TapeSlot k)
    (pos : Fin (T + 2)) (hp : p < 4 * 4) :
    (cellGroupC tm T x S off tape pos)[p + 1]?
      = some (if off + (cellBase tm T tape pos + p / 4)
                = off + (cellBase tm T tape pos + p % 4) then
            [(false, off + (cellBase tm T tape pos + p / 4)),
              (true, off + (cellBase tm T tape pos + p / 4))]
          else
            [(false, off + (cellBase tm T tape pos + p / 4)),
              (false, off + (cellBase tm T tape pos + p % 4))]) := by
  have hlen : symbolList.length = 4 := symbolList_length
  have hdiv : p / 4 < 4 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hp)
  have hmod : p % 4 < 4 := Nat.mod_lt _ (by omega)
  rw [cellGroupC, oneHotClauses_getElem?_tail,
    atMostOneClauses_getElem? _ _ (by rw [hlen]; omega) p (by rw [hlen]; exact hp), hlen,
    List.getElem?_eq_getElem (by rw [hlen]; exact hdiv),
    List.getElem?_eq_getElem (by rw [hlen]; exact hmod)]
  simp only [Option.bind_some, Option.map_some]
  rw [configWire_symbolList tm T off _ hdiv tape pos,
    configWire_symbolList tm T off _ hmod tape pos]

/-- **The validity dispatch emits the state group's later clauses correctly.** -/
theorem validEnc_state_succ_eq (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU : List Bool)
    (hlt : pU.length < sqU.length) (hp : pU ≠ [])
    (hq : qU.length = Fintype.card tm.Q) (hpos : 0 < Fintype.card tm.Q)
    (h₁ : offU.length + (pU.length - 1) / Fintype.card tm.Q ≤ w.length)
    (h₂ : offU.length + (pU.length - 1) % Fintype.card tm.Q ≤ w.length) :
    validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
      = DataEncode.bitstringEncode
          (if offU.length + (pU.length - 1) / Fintype.card tm.Q
                = offU.length + (pU.length - 1) % Fintype.card tm.Q then
              [(false, offU.length + (pU.length - 1) / Fintype.card tm.Q),
                (true, offU.length + (pU.length - 1) / Fintype.card tm.Q)]
            else [(false, offU.length + (pU.length - 1) / Fintype.card tm.Q),
                (false, offU.length + (pU.length - 1) % Fintype.card tm.Q)]) := by
  rw [validEnc, ifLtLen_pos hlt]
  exact stateGroupEnc_succ_eq tm w offU qU pU hp hq hpos h₁ h₂

/-- The state group's later clauses are the validity group's, at the same index. -/
theorem cfgValidC_getElem?_state_succ (x : List Bool) (S off p : ℕ)
    (hpos : 0 < Fintype.card tm.Q) (hp : p < Fintype.card tm.Q * Fintype.card tm.Q) :
    (cfgValidC tm T x S off)[p + 1]?
      = some (if off + p / Fintype.card tm.Q = off + p % Fintype.card tm.Q then
            [(false, off + p / Fintype.card tm.Q), (true, off + p / Fintype.card tm.Q)]
          else [(false, off + p / Fintype.card tm.Q),
            (false, off + p % Fintype.card tm.Q)]) := by
  rw [cfgValidC_getElem?_state tm T x S off (p + 1) (by omega),
    stateGroupC_getElem?_succ tm T off p hpos hp]

/-- **The state group of the validity family, encoded.** -/
theorem validEnc_state_eq (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU : List Bool)
    (S p : ℕ) (hp : p < sqU.length)
    (hsq : sqU.length = 1 + Fintype.card tm.Q * Fintype.card tm.Q)
    (hq : qU.length = Fintype.card tm.Q) (hpos : 0 < Fintype.card tm.Q)
    (hb : ∀ j, j < Fintype.card tm.Q → offU.length + j ≤ w.length) :
    ((cfgValidC tm T x S offU.length)[p]?).map DataEncode.bitstringEncode
      = some (validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
          (List.replicate p true)) := by
  have hpq : p < 1 + Fintype.card tm.Q * Fintype.card tm.Q := by omega
  rcases Nat.eq_zero_or_pos p with rfl | hpos'
  · rw [cfgValidC_getElem?_zero, Option.map_some, List.replicate_zero,
      validEnc_state_zero_eq tm T w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
        (by omega) hq (fun j hj => hb j (by omega))]
  · obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
    have hdiv : r / Fintype.card tm.Q < Fintype.card tm.Q := by
      have : r < Fintype.card tm.Q * Fintype.card tm.Q := by omega
      exact Nat.div_lt_of_lt_mul (by omega)
    have hmod : r % Fintype.card tm.Q < Fintype.card tm.Q := Nat.mod_lt _ hpos
    rw [cfgValidC_getElem?_state tm T x S offU.length (r + 1) hpq,
      stateGroupC_getElem?_succ tm T offU.length r hpos (by omega), Option.map_some,
      validEnc_state_succ_eq tm w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
        (List.replicate (r + 1) true) (by rw [List.length_replicate]; omega)
        (by simp) hq hpos
        (by rw [List.length_replicate]; simpa using hb _ hdiv)
        (by rw [List.length_replicate]; simpa using hb _ hmod),
      List.length_replicate, Nat.add_sub_cancel]

/-- **The validity dispatch emits a head group's first clause correctly.** -/
theorem validEnc_head_zero_eq (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU : List Bool)
    (tape : TapeSlot k) (hge : sqU.length ≤ pU.length)
    (htape : (tapeOfIdx sqU tbU pU).length = tape.index.val)
    (hzero : offInTape sqU tbU pU = []) (hhspos : 0 < hsU.length)
    (hlast : lastU.length = k + 1) (hhor : horU.length = T + 1)
    (hq : qU.length = Fintype.card tm.Q)
    (hb : ∀ j, j < (headCountU x SU (tapeOfIdx sqU tbU pU) lastU horU).length →
      (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length + j ≤ w.length) :
    validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
      = DataEncode.bitstringEncode (QBF.atLeastOneClause
          (fun p : Fin (T + 1) => configWire tm T offU.length (.head tape p))
          (allowedHeads T x.length SU.length tape)) := by
  rw [validEnc_eq_dispatch, ifLtLen_neg (by omega), tapeBlockEnc, hzero,
    ifLtLen_pos (by simpa using hhspos)]
  exact headGroupEnc_zero_eq tm T w offU qU (tapeOfIdx sqU tbU pU) horU
    (headCountU x SU (tapeOfIdx sqU tbU pU) lastU horU) tape x.length SU.length hq htape hhor
    (headCountU_length_eq T x SU (tapeOfIdx sqU tbU pU) lastU horU tape htape hlast hhor) hb

/-- **The head group's later clauses are emitted correctly.** -/
theorem headGroupEnc_succ_eq (w offU qU tapeU horU mU rU : List Bool) (hr : rU ≠ [])
    (hhor : 0 < horU.length)
    (h₁ : (headWireU offU qU tapeU [] horU).length + (rU.length - 1) / horU.length
      ≤ w.length)
    (h₂ : (headWireU offU qU tapeU [] horU).length + (rU.length - 1) % horU.length
      ≤ w.length) :
    headGroupEnc w offU qU tapeU horU mU rU
      = DataEncode.bitstringEncode
          (if (headWireU offU qU tapeU [] horU).length + (rU.length - 1) / horU.length
                = (headWireU offU qU tapeU [] horU).length
                  + (rU.length - 1) % horU.length then
              [(false, (headWireU offU qU tapeU [] horU).length
                  + (rU.length - 1) / horU.length),
                (true, (headWireU offU qU tapeU [] horU).length
                  + (rU.length - 1) / horU.length)]
            else [(false, (headWireU offU qU tapeU [] horU).length
                  + (rU.length - 1) / horU.length),
                (false, (headWireU offU qU tapeU [] horU).length
                  + (rU.length - 1) % horU.length)]) :=
  oneHotEnc_succ w (headWireU offU qU tapeU [] horU) (headWireU offU qU tapeU [] horU) mU
    horU rU hr hhor h₁ h₂

theorem headWireU_zero_add (off : ℕ) (tape : TapeSlot k) (i : ℕ) (hi : i < T + 1)
    {offU qU tapeU horU : List Bool} (hoff : offU.length = off)
    (hq : qU.length = Fintype.card tm.Q) (htape : tapeU.length = tape.index.val)
    (hhor : horU.length = T + 1) :
    (headWireU offU qU tapeU [] horU).length + i
      = configWire tm T off (.head tape ⟨i, hi⟩) := by
  rw [headWireU_length, hoff, hq, htape, hhor, configWire, configIndex]
  simp only [List.length_nil]
  ring

/-- **A tape's head one-hot clause, encoded.** -/
theorem validEnc_head_zero (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU : List Bool)
    (S p : ℕ) (hsq : sqU.length = 1 + Fintype.card tm.Q * Fintype.card tm.Q)
    (htb : tbU.length = tapeBlockSize T) (hhspos : 0 < hsU.length)
    (hSU : SU.length = S) (hlast : lastU.length = k + 1) (hhor : horU.length = T + 1)
    (hq : qU.length = Fintype.card tm.Q)
    (h₁ : sqU.length ≤ p) (h₂ : p < sqU.length + (k + 2) * tapeBlockSize T)
    (hoff : (p - sqU.length) % tapeBlockSize T = 0)
    (hb : ∀ j, j < (headCountU x SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU
        horU).length →
      (headWireU offU qU (tapeOfIdx sqU tbU (List.replicate p true)) [] horU).length + j
        ≤ w.length) :
    ((cfgValidC tm T x S offU.length)[p]?).map DataEncode.bitstringEncode
      = some (validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
          (List.replicate p true)) := by
  have htbpos : 0 < tapeBlockSize T := tapeBlockSize_pos T
  have hcomm : (k + 2) * tapeBlockSize T = tapeBlockSize T * (k + 2) := Nat.mul_comm _ _
  have hi : (p - sqU.length) / tapeBlockSize T < k + 2 :=
    Nat.div_lt_of_lt_mul (by omega)
  have hlenrep : (List.replicate p true).length = p := List.length_replicate
  have htape : (tapeOfIdx sqU tbU (List.replicate p true)).length
      = ((tapeSlotEquiv k).symm ⟨(p - sqU.length) / tapeBlockSize T, hi⟩).index.val := by
    rw [tapeOfIdx_length _ _ _ (by omega), hlenrep, htb, tapeSlotEquiv_symm_index]
  have hzero : offInTape sqU tbU (List.replicate p true) = [] := by
    refine List.eq_nil_of_length_eq_zero ?_
    rw [offInTape_length _ _ _ (by omega), hlenrep, htb, hoff]
  rw [cfgValidC_getElem?_tape tm T x S offU.length p (by omega) (by omega), ← hsq,
    tapeList_getElem? _ hi, Option.bind_some, hoff,
    List.getElem?_append_left (by rw [headGroupC_length]; omega), headGroupC,
    oneHotClauses_getElem?_head, Option.map_some,
    validEnc_head_zero_eq tm T w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
      (List.replicate p true) _ (by rw [hlenrep]; omega) htape hzero hhspos hlast hhor hq
      hb, hSU]

/-- **The validity dispatch emits a head group's later clauses correctly.** -/
theorem validEnc_head_succ_eq (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU : List Bool)
    (hge : sqU.length ≤ pU.length)
    (hlt : (offInTape sqU tbU pU).length < hsU.length) :
    validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
      = headGroupEnc w offU qU (tapeOfIdx sqU tbU pU) horU
          (headCountU x SU (tapeOfIdx sqU tbU pU) lastU horU) (offInTape sqU tbU pU) := by
  rw [validEnc_eq_dispatch, ifLtLen_neg (by omega), tapeBlockEnc, ifLtLen_pos hlt]

/-- **A tape's head at-most-one clauses, encoded.** -/
theorem validEnc_head_succ (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU : List Bool)
    (S p : ℕ) (hsq : sqU.length = 1 + Fintype.card tm.Q * Fintype.card tm.Q)
    (htb : tbU.length = tapeBlockSize T) (hhs : hsU.length = 1 + (T + 1) * (T + 1))
    (hhor : horU.length = T + 1) (hq : qU.length = Fintype.card tm.Q)
    (h₁ : sqU.length ≤ p) (h₂ : p < sqU.length + (k + 2) * tapeBlockSize T)
    (hoff0 : 0 < (p - sqU.length) % tapeBlockSize T)
    (hofflt : (p - sqU.length) % tapeBlockSize T < hsU.length)
    (hb : ∀ i, i < T + 1 →
      (headWireU offU qU (tapeOfIdx sqU tbU (List.replicate p true)) [] horU).length + i
        ≤ w.length) :
    ((cfgValidC tm T x S offU.length)[p]?).map DataEncode.bitstringEncode
      = some (validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
          (List.replicate p true)) := by
  have htbpos : 0 < tapeBlockSize T := tapeBlockSize_pos T
  have hcomm : (k + 2) * tapeBlockSize T = tapeBlockSize T * (k + 2) := Nat.mul_comm _ _
  have hi : (p - sqU.length) / tapeBlockSize T < k + 2 := Nat.div_lt_of_lt_mul (by omega)
  have hlenrep : (List.replicate p true).length = p := List.length_replicate
  have htape : (tapeOfIdx sqU tbU (List.replicate p true)).length
      = ((tapeSlotEquiv k).symm ⟨(p - sqU.length) / tapeBlockSize T, hi⟩).index.val := by
    rw [tapeOfIdx_length _ _ _ (by omega), hlenrep, htb, tapeSlotEquiv_symm_index]
  have hr : (offInTape sqU tbU (List.replicate p true)).length
      = (p - sqU.length) % tapeBlockSize T := by
    rw [offInTape_length _ _ _ (by omega), hlenrep, htb]
  obtain ⟨s, hs⟩ : ∃ s, (p - sqU.length) % tapeBlockSize T = s + 1 :=
    ⟨(p - sqU.length) % tapeBlockSize T - 1, by omega⟩
  have hslt : s < (T + 1) * (T + 1) := by omega
  have hdiv : s / (T + 1) < T + 1 := Nat.div_lt_of_lt_mul (by omega)
  have hmod : s % (T + 1) < T + 1 := Nat.mod_lt _ (by omega)
  have hfin : ∀ (i : ℕ) (hi' : i < T + 1),
      (List.finRange (T + 1))[i]? = some ⟨i, hi'⟩ := by
    intro i hi'
    rw [List.getElem?_eq_getElem (by rw [List.length_finRange]; exact hi'),
      List.getElem_finRange]
    rfl
  rw [cfgValidC_getElem?_tape tm T x S offU.length p (by omega) (by omega), ← hsq,
    tapeList_getElem? _ hi, Option.bind_some, hs,
    List.getElem?_append_left (by rw [headGroupC_length]; omega), headGroupC,
    oneHotClauses_getElem?_tail,
    atMostOneClauses_getElem? _ _ (by rw [List.length_finRange]; omega) s
      (by rw [List.length_finRange]; exact hslt),
    List.length_finRange, hfin _ hdiv, Option.bind_some, hfin _ hmod, Option.map_some,
    Option.map_some,
    validEnc_head_succ_eq w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
      (List.replicate p true) (by rw [hlenrep]; omega) (by rw [hr, hs]; omega),
    headGroupEnc_succ_eq w offU qU (tapeOfIdx sqU tbU (List.replicate p true)) horU
      (headCountU x SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU horU)
      (offInTape sqU tbU (List.replicate p true))
      (by
        intro hnil
        rw [hnil, List.length_nil] at hr
        omega)
      (by omega)
      (by rw [hr, hs, hhor, Nat.add_sub_cancel]; exact hb _ hdiv)
      (by rw [hr, hs, hhor, Nat.add_sub_cancel]; exact hb _ hmod),
    hr, hs, hhor, Nat.add_sub_cancel,
    headWireU_zero_add tm T offU.length _ (s / (T + 1)) hdiv rfl hq htape hhor,
    headWireU_zero_add tm T offU.length _ (s % (T + 1)) hmod rfl hq htape hhor]

/-- **The validity dispatch routes past the head group into a cell group.** -/
theorem validEnc_cell_eq (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU : List Bool)
    (hge : sqU.length ≤ pU.length)
    (hge2 : hsU.length ≤ (offInTape sqU tbU pU).length) :
    validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
      = cellGroupEnc w offU qU hdU (tapeOfIdx sqU tbU pU)
          (divFn2 (pair cellSizeU ((offInTape sqU tbU pU).drop hsU.length))) hor2U
          (symStartU x SU (tapeOfIdx sqU tbU pU) lastU
            (divFn2 (pair cellSizeU ((offInTape sqU tbU pU).drop hsU.length))))
          (symCountU SU (tapeOfIdx sqU tbU pU) lastU
            (divFn2 (pair cellSizeU ((offInTape sqU tbU pU).drop hsU.length))))
          (modFn2 (pair cellSizeU ((offInTape sqU tbU pU).drop hsU.length))) := by
  rw [validEnc_eq_dispatch, ifLtLen_neg (by omega), tapeBlockEnc, ifLtLen_neg (by omega)]

/-- **The symbol count branch agrees with the allowed symbols.** -/
theorem symCountU_length_eq (x SU tapeU lastU posU : List Bool) (tape : TapeSlot k)
    (pos : Fin (T + 2)) (htape : tapeU.length = tape.index.val) (hlast : lastU.length = k + 1)
    (hpos : posU.length = pos.val) :
    (symCountU SU tapeU lastU posU).length
      = (allowedSyms T x SU.length tape pos).length := by
  cases tape with
  | input =>
      have ht0 : tapeU.length = ([] : List Bool).length := by
        rw [htape]
        rfl
      rw [symCountU, ifEqLen_pos ht0,
        allowedSyms_length_of_some T x SU.length _ pos (fixedSym_input x SU.length pos.val)]
      rfl
  | work i =>
      have hne : tapeU.length ≠ ([] : List Bool).length := by
        rw [htape]
        simp [TapeSlot.index]
      have hne2 : tapeU.length ≠ lastU.length := by
        rw [htape, hlast]
        have := i.isLt
        simp only [TapeSlot.index]
        omega
      rw [symCountU, ifEqLen_neg hne, ifEqLen_neg hne2, symCountBeyond_length, hpos]
      by_cases hc : SU.length < pos.val
      · rw [if_pos hc, allowedSyms_length_of_some T x SU.length _ pos
          (by rw [fixedSym_work, if_pos hc])]
      · rw [if_neg hc, allowedSyms_length_of_none T x SU.length _ pos
          (by rw [fixedSym_work, if_neg hc])]
  | output =>
      have hne : tapeU.length ≠ ([] : List Bool).length := by
        rw [htape]
        simp [TapeSlot.index]
      have hlen1 : (SU ++ [false]).length = SU.length + 1 := by
        rw [List.length_append]
        rfl
      rw [symCountU, ifEqLen_neg hne, ifEqLen_pos (by rw [htape, hlast]; rfl),
        symCountBeyond_length, hlen1, hpos]
      by_cases hc : SU.length + 1 < pos.val
      · rw [if_pos hc, allowedSyms_length_of_some T x SU.length _ pos
          (by rw [fixedSym_output, if_pos hc])]
      · rw [if_neg hc, allowedSyms_length_of_none T x SU.length _ pos
          (by rw [fixedSym_output, if_neg hc])]

/-- **The symbol start branch agrees with the fixed symbol.** -/
theorem symStartU_length_eq (x SU tapeU lastU posU : List Bool) (tape : TapeSlot k)
    (pos : Fin (T + 2)) (htape : tapeU.length = tape.index.val) (hlast : lastU.length = k + 1)
    (hpos : posU.length = pos.val) :
    (symStartU x SU tapeU lastU posU).length = symStart T x SU.length tape pos := by
  cases tape with
  | input =>
      have ht0 : tapeU.length = ([] : List Bool).length := by
        rw [htape]
        rfl
      rw [symStartU, ifEqLen_pos ht0, symStartInput_length, hpos,
        symStart_of_some T x SU.length _ pos (fixedSym_input x SU.length pos.val)]
  | work i =>
      have hne : tapeU.length ≠ ([] : List Bool).length := by
        rw [htape]
        simp [TapeSlot.index]
      have hne2 : tapeU.length ≠ lastU.length := by
        rw [htape, hlast]
        have := i.isLt
        simp only [TapeSlot.index]
        omega
      rw [symStartU, ifEqLen_neg hne, ifEqLen_neg hne2, symStartBeyond_length, hpos]
      by_cases hc : SU.length < pos.val
      · rw [if_pos hc, symStart_of_some T x SU.length _ pos
          (by rw [fixedSym_work, if_pos hc])]
        rfl
      · rw [if_neg hc, symStart_of_none T x SU.length _ pos
          (by rw [fixedSym_work, if_neg hc])]
  | output =>
      have hne : tapeU.length ≠ ([] : List Bool).length := by
        rw [htape]
        simp [TapeSlot.index]
      have hlen1 : (SU ++ [false]).length = SU.length + 1 := by
        rw [List.length_append]
        rfl
      rw [symStartU, ifEqLen_neg hne, ifEqLen_pos (by rw [htape, hlast]; rfl),
        symStartBeyond_length, hlen1, hpos]
      by_cases hc : SU.length + 1 < pos.val
      · rw [if_pos hc, symStart_of_some T x SU.length _ pos
          (by rw [fixedSym_output, if_pos hc])]
        rfl
      · rw [if_neg hc, symStart_of_none T x SU.length _ pos
          (by rw [fixedSym_output, if_neg hc])]

/-- **A cell group's one-hot clause, encoded.** -/
theorem validEnc_cell_zero (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU : List Bool)
    (S p : ℕ) (hsq : sqU.length = 1 + Fintype.card tm.Q * Fintype.card tm.Q)
    (htb : tbU.length = tapeBlockSize T) (hhs : hsU.length = 1 + (T + 1) * (T + 1))
    (hhd : hdU.length = (k + 2) * (T + 1)) (hhor2 : hor2U.length = T + 2)
    (hSU : SU.length = S) (hlast : lastU.length = k + 1)
    (hq : qU.length = Fintype.card tm.Q)
    (h₁ : sqU.length ≤ p) (h₂ : p < sqU.length + (k + 2) * tapeBlockSize T)
    (hoffge : hsU.length ≤ (p - sqU.length) % tapeBlockSize T)
    (hcell : ((p - sqU.length) % tapeBlockSize T - hsU.length) % (1 + 4 * 4) = 0)
    (hb : ∀ j, j < (symCountU SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU
        (divFn2 (pair cellSizeU
          ((offInTape sqU tbU (List.replicate p true)).drop hsU.length)))).length →
      (cellWireU offU qU hdU (tapeOfIdx sqU tbU (List.replicate p true))
        (divFn2 (pair cellSizeU
          ((offInTape sqU tbU (List.replicate p true)).drop hsU.length))) hor2U
        (symStartU x SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU
          (divFn2 (pair cellSizeU
            ((offInTape sqU tbU (List.replicate p true)).drop hsU.length))))).length + j
        ≤ w.length) :
    ((cfgValidC tm T x S offU.length)[p]?).map DataEncode.bitstringEncode
      = some (validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
          (List.replicate p true)) := by
  have htbpos : 0 < tapeBlockSize T := tapeBlockSize_pos T
  have hcomm : (k + 2) * tapeBlockSize T = tapeBlockSize T * (k + 2) := Nat.mul_comm _ _
  have hi : (p - sqU.length) / tapeBlockSize T < k + 2 := Nat.div_lt_of_lt_mul (by omega)
  have hlenrep : (List.replicate p true).length = p := List.length_replicate
  have htape : (tapeOfIdx sqU tbU (List.replicate p true)).length
      = ((tapeSlotEquiv k).symm ⟨(p - sqU.length) / tapeBlockSize T, hi⟩).index.val := by
    rw [tapeOfIdx_length _ _ _ (by omega), hlenrep, htb, tapeSlotEquiv_symm_index]
  have hr : (offInTape sqU tbU (List.replicate p true)).length
      = (p - sqU.length) % tapeBlockSize T := by
    rw [offInTape_length _ _ _ (by omega), hlenrep, htb]
  have htbeq : tapeBlockSize T = 1 + (T + 1) * (T + 1) + (T + 2) * (1 + 4 * 4) := rfl
  have hrlt : (p - sqU.length) % tapeBlockSize T
      < 1 + (T + 1) * (T + 1) + (T + 2) * (1 + 4 * 4) := by
    rw [← htbeq]; exact Nat.mod_lt _ htbpos
  have hdrop : ((offInTape sqU tbU (List.replicate p true)).drop hsU.length).length
      = (p - sqU.length) % tapeBlockSize T - hsU.length := by
    rw [List.length_drop, hr]
  have hposlt : ((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4) < T + 2 :=
    Nat.div_lt_of_lt_mul (by omega)
  have hpos : (divFn2 (pair cellSizeU
      ((offInTape sqU tbU (List.replicate p true)).drop hsU.length))).length
      = ((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4) := by
    rw [divFn2_eq (by rw [cellSizeU_length]; omega), List.length_replicate, hdrop,
      cellSizeU_length]
  have hnil : modFn2 (pair cellSizeU
      ((offInTape sqU tbU (List.replicate p true)).drop hsU.length)) = [] := by
    rw [modFn2_eq (by rw [cellSizeU_length]; omega), hdrop, cellSizeU_length, hcell,
      List.replicate_zero]
  have hbound : (p - sqU.length) % tapeBlockSize T - hsU.length
      < (List.finRange (T + 2)).length * (1 + 4 * 4) := by
    rw [List.length_finRange]
    omega
  rw [cfgValidC_getElem?_tape tm T x S offU.length p (by omega) (by omega), ← hsq,
    tapeList_getElem? _ hi, Option.bind_some,
    List.getElem?_append_right (by rw [headGroupC_length, ← hhs]; omega),
    headGroupC_length, ← hhs,
    getElem?_flatMap_const (1 + 4 * 4) (by omega) _
      (fun pos => cellGroupC_length tm T x S offU.length _ pos) _ _ hbound,
    finRange_getElem? _ _ hposlt, Option.bind_some, hcell,
    cellGroupC, oneHotClauses_getElem?_head, Option.map_some,
    validEnc_cell_eq w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
      (List.replicate p true) (by rw [hlenrep]; omega) (by rw [hr]; omega), hnil,
    cellGroupEnc_zero_eq tm T w offU qU hdU (tapeOfIdx sqU tbU (List.replicate p true))
      (divFn2 (pair cellSizeU
        ((offInTape sqU tbU (List.replicate p true)).drop hsU.length))) hor2U
      (symStartU x SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU
        (divFn2 (pair cellSizeU
          ((offInTape sqU tbU (List.replicate p true)).drop hsU.length))))
      (symCountU SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU
        (divFn2 (pair cellSizeU
          ((offInTape sqU tbU (List.replicate p true)).drop hsU.length))))
      x S _ ⟨((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4), hposlt⟩
      hq hhd htape hpos hhor2
      (by
        rw [symStartU_length_eq (T := T) x SU _ lastU _ _
          ⟨((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4), hposlt⟩
          htape hlast hpos, hSU])
      (by
        rw [symCountU_length_eq (T := T) (x := x) SU _ lastU _ _
          ⟨((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4), hposlt⟩
          htape hlast hpos, hSU])
      hb]

/-! ## The chain clause of a level -/

/-- The `i`-th literal of a chain clause, encoded. -/
noncomputable def chainLitEnc (w yU y'U e₁U e₂U wU iU : List Bool) : List Bool :=
  ifEqLen iU [] (litEnc w [] yU)
    (ifLtLen (dropOne iU) wU (litEnc w [] (e₁U ++ dropOne iU))
      (ifLtLen ((dropOne iU).drop wU.length) wU
        (litEnc w [] (e₂U ++ (dropOne iU).drop wU.length))
        (litEnc w [true] y'U)))

theorem chainLitEnc_eq (w yU y'U e₁U e₂U wU iU : List Bool) :
    chainLitEnc w yU y'U e₁U e₂U wU iU
      = DataEncode.bitstringEncode
          (if iU.length = 0 then ((false, min yU.length w.length) : CLit)
            else if iU.length - 1 < wU.length then
              (false, min (e₁U.length + (iU.length - 1)) w.length)
            else if iU.length - 1 - wU.length < wU.length then
              (false, min (e₂U.length + (iU.length - 1 - wU.length)) w.length)
            else (true, min y'U.length w.length)) := by
  have hd : (dropOne iU).length = iU.length - 1 := by rw [dropOne, List.length_drop]
  have hd2 : ((dropOne iU).drop wU.length).length = iU.length - 1 - wU.length := by
    rw [List.length_drop, hd]
  have he₁ : (e₁U ++ dropOne iU).length = e₁U.length + (iU.length - 1) := by
    rw [List.length_append, hd]
  have he₂ : (e₂U ++ (dropOne iU).drop wU.length).length
      = e₂U.length + (iU.length - 1 - wU.length) := by
    rw [List.length_append, hd2]
  rw [chainLitEnc]
  by_cases c0 : iU.length = 0
  · rw [ifEqLen_pos (by rw [c0]; rfl), if_pos c0, litEnc_neg' w yU]
  · rw [ifEqLen_neg (by simpa using c0), if_neg c0]
    by_cases c1 : iU.length - 1 < wU.length
    · rw [ifLtLen_pos (by rw [hd]; exact c1), if_pos c1,
        litEnc_neg' w (e₁U ++ dropOne iU), he₁]
    · rw [ifLtLen_neg (by rw [hd]; exact c1), if_neg c1]
      by_cases c2 : iU.length - 1 - wU.length < wU.length
      · rw [ifLtLen_pos (by rw [hd2]; exact c2), if_pos c2,
          litEnc_neg' w (e₂U ++ (dropOne iU).drop wU.length), he₂]
      · rw [ifLtLen_neg (by rw [hd2]; exact c2), if_neg c2,
          litEnc_pos' (by simp) w y'U]

theorem chainLitEnc_mem_FP {w yU y'U e₁U e₂U wU iU : List Bool → List Bool} (hw : w ∈ FP)
    (hy : yU ∈ FP) (hy' : y'U ∈ FP) (he₁ : e₁U ∈ FP) (he₂ : e₂U ∈ FP) (hwU : wU ∈ FP)
    (hi : iU ∈ FP) :
    (fun z => chainLitEnc (w z) (yU z) (y'U z) (e₁U z) (e₂U z) (wU z) (iU z)) ∈ FP := by
  have hdrop : (fun z => dropOne (iU z)) ∈ FP := dropOneFn_mem_FP hi
  have hdrop2 : (fun z => (dropOne (iU z)).drop (wU z).length) ∈ FP :=
    dropLenFn_mem_FP hwU hdrop
  exact ifEqLen_mem_FP hi (constFn_mem_FP []) (litEnc_mem_FP hw (constFn_mem_FP []) hy)
    (ifLtLen_mem_FP hdrop hwU
      (litEnc_mem_FP hw (constFn_mem_FP []) (Cobham.appendFn_mem_FP he₁ hdrop))
      (ifLtLen_mem_FP hdrop2 hwU
        (litEnc_mem_FP hw (constFn_mem_FP []) (Cobham.appendFn_mem_FP he₂ hdrop2))
        (litEnc_mem_FP hw (constFn_mem_FP [true]) hy')))

/-- A whole chain clause, encoded. -/
noncomputable def chainEnc (w yU y'U e₁U e₂U wU : List Bool) : List Bool :=
  DataEncode.bitstringEncode
    ((List.range (2 * wU.length + 2)).map fun i =>
      if i = 0 then ((false, min yU.length w.length) : CLit)
      else if i - 1 < wU.length then (false, min (e₁U.length + (i - 1)) w.length)
      else if i - 1 - wU.length < wU.length then
        (false, min (e₂U.length + (i - 1 - wU.length)) w.length)
      else (true, min y'U.length w.length))

/-- **A chain clause, encoded.** -/
theorem chainEnc_eq (w yU y'U e₁U e₂U wU : List Bool) (L : FlatLayout) (j : ℕ)
    (hW : wU.length = L.W) (hy : yU.length = L.yAt j)
    (hy' : y'U.length = L.yAt (j + 1))
    (hyle : yU.length ≤ w.length) (hy'le : y'U.length ≤ w.length)
    (he₁ : e₁U.length + wU.length ≤ w.length)
    (he₂ : e₂U.length + wU.length ≤ w.length) :
    chainEnc w yU y'U e₁U e₂U wU
      = DataEncode.bitstringEncode (L.chainClause j e₁U.length e₂U.length) := by
  have he₁' : e₁U.length + L.W ≤ w.length := by rw [← hW]; exact he₁
  have he₂' : e₂U.length + L.W ≤ w.length := by rw [← hW]; exact he₂
  rw [chainEnc, L.chainClause_eq_map, hW]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  by_cases c0 : i = 0
  · rw [if_pos c0, if_pos c0, Nat.min_eq_left hyle, hy]
  · rw [if_neg c0, if_neg c0]
    by_cases c1 : i - 1 < L.W
    · rw [if_pos c1, if_pos c1, Nat.min_eq_left (by omega)]
    · rw [if_neg c1, if_neg c1]
      by_cases c2 : i - 1 - L.W < L.W
      · rw [if_pos c2, if_pos c2, Nat.min_eq_left (by omega)]
      · rw [if_neg c2, if_neg c2, Nat.min_eq_left hy'le, hy']

theorem chainEnc_mem_FP {w yU y'U e₁U e₂U wU : List Bool → List Bool} (hw : w ∈ FP)
    (hy : yU ∈ FP) (hy' : y'U ∈ FP) (he₁ : e₁U ∈ FP) (he₂ : e₂U ∈ FP) (hwU : wU ∈ FP)
    :
    (fun z => chainEnc (w z) (yU z) (y'U z) (e₁U z) (e₂U z) (wU z)) ∈ FP := by
  have hproj : ∀ {f : List Bool → List Bool}, f ∈ FP → (fun y => f (pairFst y)) ∈ FP :=
    fun hf => mem_FP_of_eq (mem_FP_comp pairFst_mem_FP hf) fun _ => rfl
  refine emit_list_mem_FP (E := fun y => chainLitEnc (w (pairFst y)) (yU (pairFst y))
      (y'U (pairFst y)) (e₁U (pairFst y)) (e₂U (pairFst y)) (wU (pairFst y)) (pairSnd y))
    (chainLitEnc_mem_FP (hproj hw) (hproj hy) (hproj hy') (hproj he₁) (hproj he₂)
      (hproj hwU) Cobham.sndBlock_mem_FP) ?_ ?_
  · refine mem_FP_of_eq (divC_mem_FP (Cobham.appendFn_mem_FP (mulC_mem_FP hwU 2)
      (constFn_mem_FP [false, false])) 1) fun z => ?_
    rw [divC_eq (by norm_num), List.length_map, List.length_range, List.length_append,
      length_mulC, Nat.div_one]
    congr 1
    simp only [List.length_cons, List.length_nil]
    omega
  · intro z i hi
    rw [List.length_map, List.length_range] at hi
    show chainLitEnc (w (pairFst (pair z (List.replicate i true))))
      (yU (pairFst (pair z (List.replicate i true))))
      (y'U (pairFst (pair z (List.replicate i true))))
      (e₁U (pairFst (pair z (List.replicate i true))))
      (e₂U (pairFst (pair z (List.replicate i true))))
      (wU (pairFst (pair z (List.replicate i true))))
      (pairSnd (pair z (List.replicate i true))) = _
    rw [pairFst_pair, pairSnd_pair, chainLitEnc_eq, List.length_replicate]
    congr 1
    rw [List.getElem_map, List.getElem_range]

/-! ## Block equality -/

/-- The `t`-th clause of a block-equality family, encoded. -/
noncomputable def eqClauseEnc (w uU vU tU : List Bool) : List Bool :=
  ifEqLen (modC 2 tU) []
    (clause2 w [] (uU ++ divC 2 tU) [true] (vU ++ divC 2 tU))
    (clause2 w [true] (uU ++ divC 2 tU) [] (vU ++ divC 2 tU))

theorem eqClauseEnc_eq (w uU vU tU : List Bool)
    (h₁ : uU.length + tU.length / 2 ≤ w.length)
    (h₂ : vU.length + tU.length / 2 ≤ w.length) :
    eqClauseEnc w uU vU tU
      = DataEncode.bitstringEncode
          (if tU.length % 2 = 0 then
              [(false, uU.length + tU.length / 2), (true, vU.length + tU.length / 2)]
            else [(true, uU.length + tU.length / 2),
              (false, vU.length + tU.length / 2)]) := by
  have hd : (divC 2 tU).length = tU.length / 2 := by
    rw [divC_eq (by norm_num), List.length_replicate]
  have hm : (modC 2 tU).length = tU.length % 2 := by
    rw [modC_eq (by norm_num), List.length_replicate]
  have hu : (uU ++ divC 2 tU).length = uU.length + tU.length / 2 := by
    rw [List.length_append, hd]
  have hv : (vU ++ divC 2 tU).length = vU.length + tU.length / 2 := by
    rw [List.length_append, hd]
  rw [eqClauseEnc]
  by_cases c0 : tU.length % 2 = 0
  · rw [ifEqLen_pos (by rw [hm, c0]; rfl), if_pos c0,
      clause2_eq false true (litEnc_neg (by rw [hu]; exact h₁))
        (litEnc_pos (by simp) (by rw [hv]; exact h₂)), hu, hv]
  · rw [ifEqLen_neg (by rw [hm]; simpa using c0), if_neg c0,
      clause2_eq true false (litEnc_pos (by simp) (by rw [hu]; exact h₁))
        (litEnc_neg (by rw [hv]; exact h₂)), hu, hv]

/-- **An equality clause matches the family it indexes.** -/
theorem eqClauseEnc_replicate_eq (w uU vU : List Bool) (W t : ℕ) (ht : t < W * 2)
    (h₁ : uU.length + t / 2 ≤ w.length) (h₂ : vU.length + t / 2 ≤ w.length) :
    ((QBF.eqClauses W uU.length vU.length)[t]?).map DataEncode.bitstringEncode
      = some (eqClauseEnc w uU vU (List.replicate t true)) := by
  rw [eqClauses_getElem?_eq W uU.length vU.length t ht,
    eqClauseEnc_eq w uU vU (List.replicate t true) (by rwa [List.length_replicate])
      (by rwa [List.length_replicate]), List.length_replicate, Option.map_some]

theorem eqClauseEnc_mem_FP {w uU vU tU : List Bool → List Bool} (hw : w ∈ FP) (hu : uU ∈ FP)
    (hv : vU ∈ FP) (ht : tU ∈ FP) :
    (fun z => eqClauseEnc (w z) (uU z) (vU z) (tU z)) ∈ FP := by
  have hd : (fun z => divC 2 (tU z)) ∈ FP := divC_mem_FP ht 2
  have hm : (fun z => modC 2 (tU z)) ∈ FP := modC_mem_FP ht 2
  have hU := Cobham.appendFn_mem_FP hu hd
  have hV := Cobham.appendFn_mem_FP hv hd
  exact ifEqLen_mem_FP hm (constFn_mem_FP [])
    (clause2_mem_FP hw (constFn_mem_FP []) hU (constFn_mem_FP [true]) hV)
    (clause2_mem_FP hw (constFn_mem_FP [true]) hU (constFn_mem_FP []) hV)

/-! ## The frame clauses -/

/-- One frame clause, encoded: a tautology on the diagonal, otherwise the two clauses tying a
cell to its old value. -/
noncomputable def frameEnc (w headU cuU cvU posU pU rU : List Bool) : List Bool :=
  ifEqLen posU pU
    (clause2 w [] headU [true] headU)
    (ifEqLen rU [] (clause3 w [] headU [] cuU [true] cvU)
      (clause3 w [] headU [true] cuU [] cvU))

theorem frameEnc_diag (w headU cuU cvU posU pU rU : List Bool)
    (heq : posU.length = pU.length) (h : headU.length ≤ w.length) :
    frameEnc w headU cuU cvU posU pU rU
      = DataEncode.bitstringEncode
          [(false, headU.length), (true, headU.length)] := by
  rw [frameEnc, ifEqLen_pos heq,
    clause2_eq false true (litEnc_neg h) (litEnc_pos (by simp) h)]

theorem frameEnc_off (w headU cuU cvU posU pU rU : List Bool)
    (hne : posU.length ≠ pU.length) (h₀ : headU.length ≤ w.length)
    (h₁ : cuU.length ≤ w.length) (h₂ : cvU.length ≤ w.length) :
    frameEnc w headU cuU cvU posU pU rU
      = DataEncode.bitstringEncode
          (if rU.length = 0 then
              [(false, headU.length), (false, cuU.length), (true, cvU.length)]
            else [(false, headU.length), (true, cuU.length), (false, cvU.length)]) := by
  rw [frameEnc, ifEqLen_neg hne]
  by_cases hr : rU.length = 0
  · rw [ifEqLen_pos (by rw [hr]; rfl), if_pos hr,
      clause3_eq false false true (litEnc_neg h₀) (litEnc_neg h₁)
        (litEnc_pos (by simp) h₂)]
  · rw [ifEqLen_neg (by simpa using hr), if_neg hr,
      clause3_eq false true false (litEnc_neg h₀) (litEnc_pos (by simp) h₁)
        (litEnc_neg h₂)]

theorem frameEnc_mem_FP {w headU cuU cvU posU pU rU : List Bool → List Bool} (hw : w ∈ FP)
    (hh : headU ∈ FP) (hcu : cuU ∈ FP) (hcv : cvU ∈ FP) (hpos : posU ∈ FP) (hp : pU ∈ FP)
    (hr : rU ∈ FP) :
    (fun z => frameEnc (w z) (headU z) (cuU z) (cvU z) (posU z) (pU z) (rU z)) ∈ FP :=
  ifEqLen_mem_FP hpos hp
    (clause2_mem_FP hw (constFn_mem_FP []) hh (constFn_mem_FP [true]) hh)
    (ifEqLen_mem_FP hr (constFn_mem_FP [])
      (clause3_mem_FP hw (constFn_mem_FP []) hh (constFn_mem_FP []) hcu
        (constFn_mem_FP [true]) hcv)
      (clause3_mem_FP hw (constFn_mem_FP []) hh (constFn_mem_FP [true]) hcu
        (constFn_mem_FP []) hcv))

/-! ## The literals of a view clause -/

/-- The case list of a machine: every local transition case, in the enumeration the view list
uses. -/
noncomputable def caseList (tm : NTM k) : List (TransitionCase tm) :=
  (Finset.univ : Finset (TransitionCase tm)).toList

theorem caseList_length : (caseList tm).length = Fintype.card (TransitionCase tm) := by
  rw [caseList, Finset.length_toList, Finset.card_univ]

theorem mem_caseList (c : TransitionCase tm) : c ∈ caseList tm :=
  Finset.mem_toList.mpr (Finset.mem_univ c)

/-- The `j`-th literal of a view clause, encoded: the negated choice bit, the negated state
literal, then the negated head and cell literals of each tape, then the forced atom. -/
noncomputable def viewLitEnc (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU
    jU : List Bool) : List Bool :=
  ifEqLen jU [] (litEnc w (tableU (caseList tm) (fun c => if c.choice then 0 else 1) caseU) sU)
    (ifEqLen jU [false]
      (litEnc w [] (uU ++ tableU (caseList tm) (fun c => stateIndex tm c.state) caseU))
      (ifLtLen (dropOne (dropOne jU)) (mulC 2 tapesU)
        (ifEqLen (modC 2 (dropOne (dropOne jU))) []
          (litEnc w [] (headWireU uU qU (divC 2 (dropOne (dropOne jU)))
            (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) horU))
          (litEnc w [] (cellWireU uU qU hdU (divC 2 (dropOne (dropOne jU)))
            (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) hor2U
            (tableU2 (caseList tm) (tapeList k) (fun c t => (symbolIndex (c.read t)).val)
              caseU (divC 2 (dropOne (dropOne jU)))))))
        (litEnc w bU (vU ++ forcedU))))

theorem viewLitEnc_mem_FP
    {w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU : List Bool → List Bool}
    (hw : w ∈ FP) (hu : uU ∈ FP) (hv : vU ∈ FP) (hs : sU ∈ FP) (hq : qU ∈ FP)
    (hhd : hdU ∈ FP) (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP) (hcase : caseU ∈ FP)
    (hview : viewU ∈ FP) (hforced : forcedU ∈ FP) (hb : bU ∈ FP) (htapes : tapesU ∈ FP)
    (hj : jU ∈ FP)
    {C : ℕ} (hC : ∀ z, (caseU z).length ≤ C)
    {E : ℕ} (hE : ∀ z, (divC 2 (dropOne (dropOne (jU z)))).length ≤ E)
    {K : ℕ} (hK : ∀ z, (pair (caseU z) (divC 2 (dropOne (dropOne (jU z))))).length ≤ K)
    {width : List Bool → List Bool} (hwd : width ∈ FP)
    (hbound : ∀ z, (horU z).length ^ E + 2 * (horU z).length + 4 ≤ (width z).length) :
    (fun z => viewLitEnc tm (w z) (uU z) (vU z) (sU z) (qU z) (hdU z) (horU z) (hor2U z)
      (caseU z) (viewU z) (forcedU z) (bU z) (tapesU z) (jU z)) ∈ FP := by
  have hd2 : (fun z => dropOne (dropOne (jU z))) ∈ FP := dropOneFn_mem_FP (dropOneFn_mem_FP hj)
  have hi : (fun z => divC 2 (dropOne (dropOne (jU z)))) ∈ FP := divC_mem_FP hd2 2
  have hr : (fun z => modC 2 (dropOne (dropOne (jU z)))) ∈ FP := modC_mem_FP hd2 2
  have hdig : (fun z => headDigitU (horU z) (divC 2 (dropOne (dropOne (jU z)))) (viewU z))
      ∈ FP := headDigitU_mem_FP hhor hi hview E hE hwd hbound
  have hch : (fun z => tableU (caseList tm) (fun c => if c.choice then 0 else 1)
      (caseU z)) ∈ FP := tableU_mem_FP _ _ hcase hC
  have hst : (fun z => tableU (caseList tm) (fun c => stateIndex tm c.state) (caseU z)) ∈ FP :=
    tableU_mem_FP _ _ hcase hC
  have hrd : (fun z => tableU2 (caseList tm) (tapeList k)
      (fun c t => (symbolIndex (c.read t)).val) (caseU z)
      (divC 2 (dropOne (dropOne (jU z))))) ∈ FP := tableU2_mem_FP _ _ _ hcase hi hK
  exact ifEqLen_mem_FP hj (constFn_mem_FP []) (litEnc_mem_FP hw hch hs)
    (ifEqLen_mem_FP hj (constFn_mem_FP [false])
      (litEnc_mem_FP hw (constFn_mem_FP []) (Cobham.appendFn_mem_FP hu hst))
      (ifLtLen_mem_FP hd2 (mulC_mem_FP htapes 2)
        (ifEqLen_mem_FP hr (constFn_mem_FP [])
          (litEnc_mem_FP hw (constFn_mem_FP [])
            (headWireU_mem_FP hu hq hi hdig hhor))
          (litEnc_mem_FP hw (constFn_mem_FP [])
            (cellWireU_mem_FP hu hq hhd hi hdig hhor2 hrd)))
        (litEnc_mem_FP hw hb (Cobham.appendFn_mem_FP hv hforced))))

/-! ## Indexing a view clause -/

theorem negLits_getElem? (L : List CLit) (i : ℕ) :
    (negLits L)[i]? = (L[i]?).map fun l => (!l.1, l.2) := by
  rw [negLits, List.getElem?_map]

theorem viewLits_length (u : ℕ) (V : StepView tm T) :
    (viewLits tm T u V).length = 2 * (k + 2) + 1 := by
  rw [viewLits, List.length_cons, List.length_flatMap,
    sum_map_const 2 (fun t => ([((true, configWire tm T u (ConfigAtom.head t (V.2 t))) : CLit),
      (true, configWire tm T u
        (ConfigAtom.cell t (headCellPosition (V.2 t)) (V.1.read t)))]).length)
      (tapeList k) (fun t _ => rfl), tapeList_length]
  omega

theorem viewLits_getElem?_zero (u : ℕ) (V : StepView tm T) :
    (viewLits tm T u V)[0]? = some (true, configWire tm T u (.state V.1.state)) := rfl

theorem viewLits_getElem?_succ (u : ℕ) (V : StepView tm T) (i : ℕ) (hi : i < 2 * (k + 2)) :
    (viewLits tm T u V)[i + 1]?
      = ((tapeList k)[i / 2]?).map fun t =>
          if i % 2 = 0 then ((true, configWire tm T u (.head t (V.2 t))) : CLit)
          else (true, configWire tm T u
            (.cell t (headCellPosition (V.2 t)) (V.1.read t))) := by
  rw [viewLits, List.getElem?_cons_succ,
    getElem?_flatMap_const 2 (by omega) _ (fun t => rfl) (tapeList k) i
      (by rw [tapeList_length]; omega)]
  rcases Nat.lt_or_ge (i / 2) (tapeList k).length with hlt | hge
  · rw [List.getElem?_eq_getElem hlt]
    have h2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases h2 with h | h <;> rw [h] <;> rfl
  · rw [List.getElem?_eq_none hge]
    rfl

theorem viewCondLits_getElem?_zero (u s : ℕ) (V : StepView tm T) :
    (viewCondLits tm T u s V)[0]? = some (V.1.choice, s) := rfl

theorem viewCondLits_getElem?_succ (u s : ℕ) (V : StepView tm T) (i : ℕ) :
    (viewCondLits tm T u s V)[i + 1]? = (viewLits tm T u V)[i]? := rfl

theorem negLits_viewCondLits_length (u s : ℕ) (V : StepView tm T) :
    (negLits (viewCondLits tm T u s V)).length = 2 * (k + 2) + 2 := by
  rw [negLits, List.length_map, viewCondLits, List.length_cons, viewLits_length]

theorem forceAtom_length (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T) (b : Bool) :
    (forceAtom tm T u v s V a b).length = 2 * (k + 2) + 3 := by
  rw [forceAtom, List.length_append, negLits_viewCondLits_length]
  simp

theorem forceAtom_getElem?_cond (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T)
    (b : Bool) (i : ℕ) (hi : i < 2 * (k + 2) + 2) :
    (forceAtom tm T u v s V a b)[i]?
      = ((viewCondLits tm T u s V)[i]?).map fun l => (!l.1, l.2) := by
  rw [forceAtom, List.getElem?_append_left (by
      rw [negLits_viewCondLits_length]; omega), negLits_getElem?]

theorem forceAtom_getElem?_last (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T)
    (b : Bool) : (forceAtom tm T u v s V a b)[2 * (k + 2) + 2]?
      = some (b, configWire tm T v a) := by
  rw [forceAtom, List.getElem?_append_right (by
      rw [negLits_viewCondLits_length]), negLits_viewCondLits_length]
  simp

theorem forceAtom_getElem?_zero (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T)
    (b : Bool) : (forceAtom tm T u v s V a b)[0]? = some (!V.1.choice, s) := by
  rw [forceAtom_getElem?_cond tm T u v s V a b 0 (by omega), viewCondLits_getElem?_zero]
  rfl

theorem forceAtom_getElem?_one (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T)
    (b : Bool) : (forceAtom tm T u v s V a b)[1]?
      = some (false, configWire tm T u (.state V.1.state)) := by
  rw [forceAtom_getElem?_cond tm T u v s V a b 1 (by omega), viewCondLits_getElem?_succ,
    viewLits_getElem?_zero]
  rfl

theorem forceAtom_getElem?_tape (u v s : ℕ) (V : StepView tm T) (a : ConfigAtom tm T)
    (b : Bool) (i : ℕ) (hi : i < 2 * (k + 2)) :
    (forceAtom tm T u v s V a b)[i + 2]?
      = ((tapeList k)[i / 2]?).map fun t =>
          if i % 2 = 0 then ((false, configWire tm T u (.head t (V.2 t))) : CLit)
          else (false, configWire tm T u
            (.cell t (headCellPosition (V.2 t)) (V.1.read t))) := by
  rw [forceAtom_getElem?_cond tm T u v s V a b (i + 2) (by omega),
    show i + 2 = (i + 1) + 1 from rfl, viewCondLits_getElem?_succ,
    viewLits_getElem?_succ tm T u V i hi, Option.map_map]
  congr 1
  funext t
  have h2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
  rcases h2 with h | h <;> rw [h] <;> rfl

/-! ## The view literal emitter is correct on the first two literals -/

theorem viewLitEnc_zero_eq (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU
    : List Bool) (c : TransitionCase tm)
    (hlt : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hlt = c)
    (hs : sU.length ≤ w.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU []
      = DataEncode.bitstringEncode ((!c.choice, sU.length) : Bool × ℕ) := by
  have htab : (tableU (caseList tm) (fun c => if c.choice then 0 else 1) caseU).length
      = if c.choice then 0 else 1 := by
    rw [tableU_length _ _ _ hlt, hc]
  rw [viewLitEnc, ifEqLen_pos rfl]
  cases hch : c.choice
  · have hne : tableU (caseList tm) (fun c => if c.choice then 0 else 1) caseU ≠ [] := by
      intro hnil
      rw [hnil, List.length_nil, hch] at htab
      simp at htab
    rw [litEnc_pos hne hs]
    rfl
  · have hnil : tableU (caseList tm) (fun c => if c.choice then 0 else 1) caseU = [] := by
      refine List.eq_nil_of_length_eq_zero ?_
      rw [htab, hch]
      rfl
    rw [hnil, litEnc_neg hs]
    rfl

theorem viewLitEnc_one_eq (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
    : List Bool) (c : TransitionCase tm)
    (hlt : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hlt = c) (hj : jU.length = 1)
    (hu : uU.length + stateIndex tm c.state ≤ w.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      = DataEncode.bitstringEncode
          ((false, uU.length + stateIndex tm c.state) : Bool × ℕ) := by
  have htab : (tableU (caseList tm) (fun c => stateIndex tm c.state) caseU).length
      = stateIndex tm c.state := by
    rw [tableU_length _ _ _ hlt, hc]
  have hlen : (uU ++ tableU (caseList tm) (fun c => stateIndex tm c.state) caseU).length
      = uU.length + stateIndex tm c.state := by
    rw [List.length_append, htab]
  rw [viewLitEnc, ifEqLen_neg (by rw [hj]; simp), ifEqLen_pos (by rw [hj]; rfl),
    litEnc_neg (by rw [hlen]; exact hu), hlen]

/-- **The view literal dispatch reaches the forced atom.** -/
theorem viewLitEnc_last_eq (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
    : List Bool) (hj0 : jU.length ≠ 0) (hj1 : jU.length ≠ 1)
    (hge : 2 * tapesU.length ≤ jU.length - 2) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      = litEnc w bU (vU ++ forcedU) := by
  have hd2 : (dropOne (dropOne jU)).length = jU.length - 2 := by
    rw [dropOne, dropOne, List.length_drop, List.length_drop]
    omega
  rw [viewLitEnc, ifEqLen_neg (by simpa using hj0), ifEqLen_neg (by simpa using hj1),
    ifLtLen_neg (by rw [hd2, length_mulC]; omega)]

/-- **The view literal dispatch reaches a tape's literal.** -/
theorem viewLitEnc_tape_eq (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
    : List Bool) (hj0 : jU.length ≠ 0) (hj1 : jU.length ≠ 1)
    (hlt : jU.length - 2 < 2 * tapesU.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      = ifEqLen (modC 2 (dropOne (dropOne jU))) []
          (litEnc w [] (headWireU uU qU (divC 2 (dropOne (dropOne jU)))
            (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) horU))
          (litEnc w [] (cellWireU uU qU hdU (divC 2 (dropOne (dropOne jU)))
            (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) hor2U
            (tableU2 (caseList tm) (tapeList k) (fun c t => (symbolIndex (c.read t)).val)
              caseU (divC 2 (dropOne (dropOne jU)))))) := by
  have hd2 : (dropOne (dropOne jU)).length = jU.length - 2 := by
    rw [dropOne, dropOne, List.length_drop, List.length_drop]
    omega
  rw [viewLitEnc, ifEqLen_neg (by simpa using hj0), ifEqLen_neg (by simpa using hj1),
    ifLtLen_pos (by rw [hd2, length_mulC]; omega)]

/-- The tape equivalence is the tape index. -/
theorem tapeSlotEquiv_apply (tape : TapeSlot k) : tapeSlotEquiv k tape = tape.index := rfl

/-- **The emitted head wire of a view is the right one.** -/
theorem headWireU_view_eq (uU qU tapeU horU viewU : List Bool)
    (i : Fin ((T + 1) ^ (k + 2))) (tape : TapeSlot k) (off : ℕ)
    (hoff : uU.length = off) (hq : qU.length = Fintype.card tm.Q)
    (htape : tapeU.length = tape.index.val) (hhor : horU.length = T + 1)
    (hview : viewU.length = i.val) :
    (headWireU uU qU tapeU (headDigitU horU tapeU viewU) horU).length
      = configWire tm T off (.head tape (headTupleOf k T i tape)) := by
  refine headWireU_eq tm T off tape (headTupleOf k T i tape) hoff hq htape ?_ hhor
  exact headDigitU_eq_headTupleOf horU tapeU viewU i tape hhor
    (by rw [htape, tapeSlotEquiv_apply]) hview

/-- **The emitted cell wire of a view is the right one.** -/
theorem cellWireU_view_eq (uU qU hdU tapeU hor2U horU viewU symU : List Bool)
    (i : Fin ((T + 1) ^ (k + 2))) (tape : TapeSlot k) (off : ℕ) (sym : Γ)
    (hoff : uU.length = off) (hq : qU.length = Fintype.card tm.Q)
    (hhd : hdU.length = (k + 2) * (T + 1)) (htape : tapeU.length = tape.index.val)
    (hhor : horU.length = T + 1) (hhor2 : hor2U.length = T + 2)
    (hview : viewU.length = i.val) (hsym : symU.length = (symbolIndex sym).val)
    (pos : Fin (T + 2))
    (hpos : pos.val = (headTupleOf k T i tape).val) :
    (cellWireU uU qU hdU tapeU (headDigitU horU tapeU viewU) hor2U symU).length
      = configWire tm T off (.cell tape pos sym) := by
  refine cellWireU_eq tm T off tape pos sym hoff hq hhd htape ?_ hhor2 hsym
  rw [hpos]
  exact headDigitU_eq_headTupleOf horU tapeU viewU i tape hhor
    (by rw [htape, tapeSlotEquiv_apply]) hview

/-- **A view clause's head literal, encoded.** -/
theorem viewLitEnc_tape_head_eq (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU
    jU : List Bool) (i : Fin ((T + 1) ^ (k + 2))) (tape : TapeSlot k)
    (hj0 : jU.length ≠ 0) (hj1 : jU.length ≠ 1)
    (hlt : jU.length - 2 < 2 * tapesU.length) (heven : (jU.length - 2) % 2 = 0)
    (htape : (jU.length - 2) / 2 = tape.index.val)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (hview : viewU.length = i.val)
    (hb : configWire tm T uU.length (.head tape (headTupleOf k T i tape)) ≤ w.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      = DataEncode.bitstringEncode
          ((false, configWire tm T uU.length
            (.head tape (headTupleOf k T i tape))) : Bool × ℕ) := by
  have hd2 : (dropOne (dropOne jU)).length = jU.length - 2 := by
    rw [dropOne, dropOne, List.length_drop, List.length_drop]
    omega
  have hmod : (modC 2 (dropOne (dropOne jU))).length = 0 := by
    rw [modC_eq (by norm_num), List.length_replicate, hd2, heven]
  have hdiv : (divC 2 (dropOne (dropOne jU))).length = tape.index.val := by
    rw [divC_eq (by norm_num), List.length_replicate, hd2, htape]
  have hw : (headWireU uU qU (divC 2 (dropOne (dropOne jU)))
      (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) horU).length
      = configWire tm T uU.length (.head tape (headTupleOf k T i tape)) :=
    headWireU_view_eq tm T uU qU _ horU viewU i tape uU.length rfl hq hdiv hhor hview
  rw [viewLitEnc_tape_eq tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      hj0 hj1 hlt,
    ifEqLen_pos (by rw [hmod, List.length_nil]), litEnc_neg (by rw [hw]; exact hb), hw]

/-- **A view clause's cell literal, encoded.** -/
theorem viewLitEnc_tape_cell_eq (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU
    jU : List Bool) (i : Fin ((T + 1) ^ (k + 2))) (tape : TapeSlot k)
    (c : TransitionCase tm) (pos : Fin (T + 2))
    (hj0 : jU.length ≠ 0) (hj1 : jU.length ≠ 1)
    (hlt : jU.length - 2 < 2 * tapesU.length) (hodd : (jU.length - 2) % 2 = 1)
    (htape : (jU.length - 2) / 2 = tape.index.val)
    (hq : qU.length = Fintype.card tm.Q) (hhd : hdU.length = (k + 2) * (T + 1))
    (hhor : horU.length = T + 1) (hhor2 : hor2U.length = T + 2)
    (hview : viewU.length = i.val)
    (hcase : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hcase = c)
    (hpos : pos.val = (headTupleOf k T i tape).val)
    (hb : configWire tm T uU.length (.cell tape pos (c.read tape)) ≤ w.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      = DataEncode.bitstringEncode
          ((false, configWire tm T uU.length (.cell tape pos (c.read tape))) : Bool × ℕ) := by
  have hd2 : (dropOne (dropOne jU)).length = jU.length - 2 := by
    rw [dropOne, dropOne, List.length_drop, List.length_drop]
    omega
  have hmod : (modC 2 (dropOne (dropOne jU))).length = 1 := by
    rw [modC_eq (by norm_num), List.length_replicate, hd2, hodd]
  have hdiv : (divC 2 (dropOne (dropOne jU))).length = tape.index.val := by
    rw [divC_eq (by norm_num), List.length_replicate, hd2, htape]
  have hidx : (divC 2 (dropOne (dropOne jU))).length < k + 2 := by
    rw [hdiv]; exact tape.index.isLt
  have hgt : (tapeList k)[(divC 2 (dropOne (dropOne jU))).length]'(by
      rw [tapeList_length]; exact hidx) = tape := by
    have h1 := tapeList_getElem? (k := k) _ hidx
    rw [List.getElem?_eq_getElem (by rw [tapeList_length]; exact hidx)] at h1
    rw [Option.some.inj h1, Equiv.symm_apply_eq]
    exact Fin.ext (by simpa [tapeSlotEquiv_apply] using hdiv)
  have hsym : (tableU2 (caseList tm) (tapeList k)
      (fun c t => (symbolIndex (c.read t)).val) caseU
      (divC 2 (dropOne (dropOne jU)))).length = (symbolIndex (c.read tape)).val := by
    rw [tableU2_length _ _ _ _ _ hcase (by rw [tapeList_length]; exact hidx), hc, hgt]
  have hw : (cellWireU uU qU hdU (divC 2 (dropOne (dropOne jU)))
      (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) hor2U
      (tableU2 (caseList tm) (tapeList k) (fun c t => (symbolIndex (c.read t)).val)
        caseU (divC 2 (dropOne (dropOne jU))))).length
      = configWire tm T uU.length (.cell tape pos (c.read tape)) :=
    cellWireU_view_eq tm T uU qU hdU _ hor2U horU viewU _ i tape uU.length (c.read tape)
      rfl hq hhd hdiv hhor hhor2 hview hsym pos hpos
  rw [viewLitEnc_tape_eq tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      hj0 hj1 hlt,
    ifEqLen_neg (by rw [hmod, List.length_nil]; omega),
    litEnc_neg (by rw [hw]; exact hb), hw]

/-! ## One level of the matrix -/

/-- One clause of a level, encoded: the guarded validity clauses of the midpoint, the four
equality-bit blocks, then the two chain clauses. -/
noncomputable def levelEnc (w qU sqU tbU hdU horU hor2U x SU lastU hsU
    vcU eU yU y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU pU : List Bool) :
    List Bool :=
  ifLtLen pU vcU
    (consLitEnc w [] yU (validEnc w midU qU sqU tbU hdU horU hor2U x SU lastU hsU pU))
    (ifLtLen (pU.drop vcU.length) eU
      (eqAuxEnc w eUAU uBlkU leftU (pU.drop vcU.length))
      (ifLtLen ((pU.drop vcU.length).drop eU.length) eU
        (eqAuxEnc w eVMU vBlkU midU ((pU.drop vcU.length).drop eU.length))
        (ifLtLen (((pU.drop vcU.length).drop eU.length).drop eU.length) eU
          (eqAuxEnc w eUMU uBlkU midU
            (((pU.drop vcU.length).drop eU.length).drop eU.length))
          (ifLtLen ((((pU.drop vcU.length).drop eU.length).drop eU.length).drop eU.length) eU
            (eqAuxEnc w eVBU vBlkU rightU
              ((((pU.drop vcU.length).drop eU.length).drop eU.length).drop eU.length))
            (ifEqLen ((((pU.drop vcU.length).drop eU.length).drop eU.length).drop eU.length)
                eU
              (chainEnc w yU y'U eUAU eVMU wU)
              (chainEnc w yU y'U eUMU eVBU wU))))))

theorem levelEnc_valid_eq (w qU sqU tbU hdU horU hor2U x SU lastU hsU
    vcU eU yU y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU : List Bool)
    (p : ℕ) (hp : p < vcU.length) :
    levelEnc w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU uBlkU vBlkU
        leftU rightU eUAU eVMU eUMU eVBU (List.replicate p true)
      = consLitEnc w [] yU (validEnc w midU qU sqU tbU hdU horU hor2U x SU lastU hsU
          (List.replicate p true)) := by
  rw [levelEnc, ifLtLen_pos (by rw [List.length_replicate]; exact hp)]

theorem levelEnc_eqUA_eq (w qU sqU tbU hdU horU hor2U x SU lastU hsU
    vcU eU yU y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU : List Bool)
    (p : ℕ) (h₁ : vcU.length ≤ p) (h₂ : p < vcU.length + eU.length) :
    levelEnc w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU uBlkU vBlkU
        leftU rightU eUAU eVMU eUMU eVBU (List.replicate p true)
      = eqAuxEnc w eUAU uBlkU leftU (List.replicate (p - vcU.length) true) := by
  rw [levelEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_pos (by rw [List.length_drop, List.length_replicate]; omega),
    List.drop_replicate]

theorem levelEnc_eqVM_eq (w qU sqU tbU hdU horU hor2U x SU lastU hsU
    vcU eU yU y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU : List Bool)
    (p : ℕ) (h₁ : vcU.length + eU.length ≤ p)
    (h₂ : p < vcU.length + eU.length + eU.length) :
    levelEnc w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU uBlkU vBlkU
        leftU rightU eUAU eVMU eUMU eVBU (List.replicate p true)
      = eqAuxEnc w eVMU vBlkU midU
        (List.replicate (p - vcU.length - eU.length) true) := by
  rw [levelEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate]; omega),
    ifLtLen_pos (by rw [List.length_drop, List.length_drop, List.length_replicate]; omega),
    List.drop_replicate, List.drop_replicate]

theorem levelEnc_eqUM_eq (w qU sqU tbU hdU horU hor2U x SU lastU hsU
    vcU eU yU y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU : List Bool)
    (p : ℕ) (h₁ : vcU.length + eU.length + eU.length ≤ p)
    (h₂ : p < vcU.length + eU.length + eU.length + eU.length) :
    levelEnc w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU uBlkU vBlkU
        leftU rightU eUAU eVMU eUMU eVBU (List.replicate p true)
      = eqAuxEnc w eUMU uBlkU midU
        (List.replicate (p - vcU.length - eU.length - eU.length) true) := by
  rw [levelEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_drop, List.length_replicate]; omega),
    ifLtLen_pos (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate]
      omega),
    List.drop_replicate, List.drop_replicate, List.drop_replicate]

theorem levelEnc_eqVB_eq (w qU sqU tbU hdU horU hor2U x SU lastU hsU
    vcU eU yU y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU : List Bool)
    (p : ℕ) (h₁ : vcU.length + eU.length + eU.length + eU.length ≤ p)
    (h₂ : p < vcU.length + eU.length + eU.length + eU.length + eU.length) :
    levelEnc w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU uBlkU vBlkU
        leftU rightU eUAU eVMU eUMU eVBU (List.replicate p true)
      = eqAuxEnc w eVBU vBlkU rightU
        (List.replicate (p - vcU.length - eU.length - eU.length - eU.length) true) := by
  rw [levelEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_drop, List.length_replicate]; omega),
    ifLtLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate]
      omega),
    ifLtLen_pos (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_drop,
        List.length_replicate]
      omega),
    List.drop_replicate, List.drop_replicate, List.drop_replicate, List.drop_replicate]

theorem levelEnc_chain₁_eq (w qU sqU tbU hdU horU hor2U x SU lastU hsU
    vcU eU yU y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU : List Bool)
    (p : ℕ) (hp : p = vcU.length + eU.length + eU.length + eU.length + eU.length) :
    levelEnc w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU uBlkU vBlkU
        leftU rightU eUAU eVMU eUMU eVBU (List.replicate p true)
      = chainEnc w yU y'U eUAU eVMU wU := by
  rw [levelEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_drop, List.length_replicate]; omega),
    ifLtLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate]
      omega),
    ifLtLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_drop,
        List.length_replicate]
      omega),
    ifEqLen_pos (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_drop,
        List.length_replicate]
      omega)]

theorem levelEnc_chain₂_eq (w qU sqU tbU hdU horU hor2U x SU lastU hsU
    vcU eU yU y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU : List Bool)
    (p : ℕ) (hp : p = vcU.length + eU.length + eU.length + eU.length + eU.length + 1) :
    levelEnc w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU uBlkU vBlkU
        leftU rightU eUAU eVMU eUMU eVBU (List.replicate p true)
      = chainEnc w yU y'U eUMU eVBU wU := by
  rw [levelEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_drop, List.length_replicate]; omega),
    ifLtLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate]
      omega),
    ifLtLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_drop,
        List.length_replicate]
      omega),
    ifEqLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_drop,
        List.length_replicate]
      omega)]

/-- **A level's clause, encoded**, given that the validity family is encoded. -/
theorem levelEnc_eq (w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU
    uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU : List Bool)
    (L : FlatLayout) (validC : ℕ → List (List CLit)) (j : ℕ)
    (hVC : ∀ off, (validC off).length = vcU.length)
    (heU : eU.length = L.W * 4) (hwU : wU.length = L.W)
    (hy : yU.length = L.yAt j) (hy' : y'U.length = L.yAt (j + 1))
    (heUA : eUAU.length = L.eUA j) (heVM : eVMU.length = L.eVM j)
    (heUM : eUMU.length = L.eUM j) (heVB : eVBU.length = L.eVB j)
    (huBlk : uBlkU.length = L.uBlk j) (hvBlk : vBlkU.length = L.vBlk j)
    (hmid : midU.length = L.mid j) (hleft : leftU.length = L.leftOf j)
    (hright : rightU.length = L.rightOf j)
    (byle : yU.length ≤ w.length) (by'le : y'U.length ≤ w.length)
    (bUA : eUAU.length + wU.length ≤ w.length) (bVM : eVMU.length + wU.length ≤ w.length)
    (bUM : eUMU.length + wU.length ≤ w.length) (bVB : eVBU.length + wU.length ≤ w.length)
    (bu : uBlkU.length + wU.length ≤ w.length) (bv : vBlkU.length + wU.length ≤ w.length)
    (bmid : midU.length + wU.length ≤ w.length) (bl : leftU.length + wU.length ≤ w.length)
    (br : rightU.length + wU.length ≤ w.length)
    (hvalid : ∀ q, q < vcU.length → ((validC (L.mid j))[q]?).map DataEncode.bitstringEncode
      = some (validEnc w midU qU sqU tbU hdU horU hor2U x SU lastU hsU
          (List.replicate q true)))
    (p : ℕ) (hp : p < vcU.length + eU.length + eU.length + eU.length + eU.length + 2) :
    ((L.levelClauses validC j)[p]?).map DataEncode.bitstringEncode
      = some (levelEnc w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU
          uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU (List.replicate p true)) := by
  have hquot : ∀ q : ℕ, q < eU.length → q / 4 < L.W := by
    intro q hq
    rw [heU] at hq
    omega
  by_cases c0 : p < vcU.length
  · rw [L.levelClauses_getElem?_valid validC vcU.length hVC (p := p) c0,
      levelEnc_valid_eq w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU
        uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU p c0]
    have hv := hvalid p c0
    rcases hc : (validC (L.mid j))[p]? with _ | c
    · rw [hc] at hv; exact absurd hv (by simp)
    · rw [hc] at hv
      rw [Option.map_some, Option.map_some]
      have hcv : DataEncode.bitstringEncode c
          = validEnc w midU qU sqU tbU hdU horU hor2U x SU lastU hsU
            (List.replicate p true) := Option.some.inj hv
      rw [← hcv, consLitEnc_eq false c (by rw [litEnc_neg', Nat.min_eq_left byle]), hy]
  · by_cases c1 : p < vcU.length + eU.length
    · rw [L.levelClauses_getElem?_eqUA validC vcU.length hVC (p := p) (by omega)
        (by omega),
        levelEnc_eqUA_eq w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU
          uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU p (by omega) c1, ← heUA, ← huBlk,
        ← hleft]
      exact eqAuxEnc_replicate_eq w eUAU uBlkU leftU L.W (p - vcU.length) (by omega)
        (by have := hquot (p - vcU.length) (by omega); omega)
        (by have := hquot (p - vcU.length) (by omega); omega)
        (by have := hquot (p - vcU.length) (by omega); omega)
    · by_cases c2 : p < vcU.length + eU.length + eU.length
      · rw [L.levelClauses_getElem?_eqVM validC vcU.length hVC (p := p) (by omega)
        (by omega),
          levelEnc_eqVM_eq w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU
            uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU p (by omega) c2, ← heVM, ← hvBlk,
          ← hmid]
        have hidx : p - vcU.length - L.W * 4 = p - vcU.length - eU.length := by
          rw [heU]
        rw [hidx]
        exact eqAuxEnc_replicate_eq w eVMU vBlkU midU L.W (p - vcU.length - eU.length)
          (by omega)
          (by have := hquot (p - vcU.length - eU.length) (by omega); omega)
          (by have := hquot (p - vcU.length - eU.length) (by omega); omega)
          (by have := hquot (p - vcU.length - eU.length) (by omega); omega)
      · by_cases c3 : p < vcU.length + eU.length + eU.length + eU.length
        · rw [L.levelClauses_getElem?_eqUM validC vcU.length hVC (p := p) (by omega)
        (by omega),
            levelEnc_eqUM_eq w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU
              midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU p (by omega) c3, ← heUM,
            ← huBlk, ← hmid]
          have hidx : p - vcU.length - 2 * (L.W * 4)
              = p - vcU.length - eU.length - eU.length := by rw [heU]; omega
          rw [hidx]
          exact eqAuxEnc_replicate_eq w eUMU uBlkU midU L.W
            (p - vcU.length - eU.length - eU.length) (by omega)
            (by have := hquot (p - vcU.length - eU.length - eU.length) (by omega); omega)
            (by have := hquot (p - vcU.length - eU.length - eU.length) (by omega); omega)
            (by have := hquot (p - vcU.length - eU.length - eU.length) (by omega); omega)
        · by_cases c4 : p < vcU.length + eU.length + eU.length + eU.length + eU.length
          · rw [L.levelClauses_getElem?_eqVB validC vcU.length hVC (p := p) (by omega)
        (by omega),
              levelEnc_eqVB_eq w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU
                midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU p (by omega) c4, ← heVB,
              ← hvBlk, ← hright]
            have hidx : p - vcU.length - 3 * (L.W * 4)
                = p - vcU.length - eU.length - eU.length - eU.length := by rw [heU]; omega
            rw [hidx]
            exact eqAuxEnc_replicate_eq w eVBU vBlkU rightU L.W
              (p - vcU.length - eU.length - eU.length - eU.length) (by omega)
              (by have := hquot (p - vcU.length - eU.length - eU.length - eU.length)
                    (by omega); omega)
              (by have := hquot (p - vcU.length - eU.length - eU.length - eU.length)
                    (by omega); omega)
              (by have := hquot (p - vcU.length - eU.length - eU.length - eU.length)
                    (by omega); omega)
          · rw [L.levelClauses_getElem?_chain validC vcU.length hVC p (by omega)]
            have hidx : p - vcU.length - 4 * (L.W * 4)
                = p - (vcU.length + eU.length + eU.length + eU.length + eU.length) := by
              rw [heU]; omega
            rw [hidx]
            by_cases c5 : p = vcU.length + eU.length + eU.length + eU.length + eU.length
            · rw [levelEnc_chain₁_eq w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU
                  y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU p c5,
                chainEnc_eq w yU y'U eUAU eVMU wU L j hwU hy hy' byle by'le bUA bVM,
                heUA, heVM]
              have : p - (vcU.length + eU.length + eU.length + eU.length + eU.length) = 0 := by
                omega
              rw [this]
              rfl
            · have c6 : p = vcU.length + eU.length + eU.length + eU.length + eU.length + 1 := by
                omega
              rw [levelEnc_chain₂_eq w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU
                  y'U wU midU uBlkU vBlkU leftU rightU eUAU eVMU eUMU eVBU p c6,
                chainEnc_eq w yU y'U eUMU eVBU wU L j hwU hy hy' byle by'le bUM bVB,
                heUM, heVB]
              have : p - (vcU.length + eU.length + eU.length + eU.length + eU.length) = 1 := by
                omega
              rw [this]
              rfl

theorem levelEnc_mem_FP
    {w qU sqU tbU hdU horU hor2U x SU lastU hsU vcU eU yU y'U wU midU uBlkU vBlkU leftU
      rightU eUAU eVMU eUMU eVBU pU : List Bool → List Bool}
    (hw : w ∈ FP) (hq : qU ∈ FP) (hsq : sqU ∈ FP) (htb : tbU ∈ FP) (hhd : hdU ∈ FP)
    (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP) (hx : x ∈ FP) (hS : SU ∈ FP) (hl : lastU ∈ FP)
    (hhs : hsU ∈ FP) (hvc : vcU ∈ FP) (he : eU ∈ FP) (hy : yU ∈ FP) (hy' : y'U ∈ FP)
    (hwU : wU ∈ FP) (hmid : midU ∈ FP) (hu : uBlkU ∈ FP) (hv : vBlkU ∈ FP)
    (hleft : leftU ∈ FP) (hright : rightU ∈ FP) (heUA : eUAU ∈ FP) (heVM : eVMU ∈ FP)
    (heUM : eUMU ∈ FP) (heVB : eVBU ∈ FP) (hp : pU ∈ FP)
    :
    (fun z => levelEnc (w z) (qU z) (sqU z) (tbU z) (hdU z) (horU z) (hor2U z) (x z) (SU z)
      (lastU z) (hsU z) (vcU z) (eU z) (yU z) (y'U z) (wU z) (midU z) (uBlkU z) (vBlkU z)
      (leftU z) (rightU z) (eUAU z) (eVMU z) (eUMU z) (eVBU z) (pU z)) ∈ FP := by
  have d1 : (fun z => (pU z).drop (vcU z).length) ∈ FP := dropLenFn_mem_FP hvc hp
  have d2 : (fun z => ((pU z).drop (vcU z).length).drop (eU z).length) ∈ FP :=
    dropLenFn_mem_FP he d1
  have d3 : (fun z => (((pU z).drop (vcU z).length).drop (eU z).length).drop (eU z).length)
      ∈ FP := dropLenFn_mem_FP he d2
  have d4 : (fun z => ((((pU z).drop (vcU z).length).drop (eU z).length).drop
      (eU z).length).drop (eU z).length) ∈ FP := dropLenFn_mem_FP he d3
  exact ifLtLen_mem_FP hp hvc
    (consLitEnc_mem_FP hw (constFn_mem_FP []) hy
      (validEnc_mem_FP hw hmid hq hsq htb hhd hhor hhor2 hx hS hl hhs hp))
    (ifLtLen_mem_FP d1 he (eqAuxEnc_mem_FP hw heUA hu hleft d1)
      (ifLtLen_mem_FP d2 he (eqAuxEnc_mem_FP hw heVM hv hmid d2)
        (ifLtLen_mem_FP d3 he (eqAuxEnc_mem_FP hw heUM hu hmid d3)
          (ifLtLen_mem_FP d4 he (eqAuxEnc_mem_FP hw heVB hv hright d4)
            (ifEqLen_mem_FP d4 he
              (chainEnc_mem_FP hw hy hy' heUA heVM hwU)
              (chainEnc_mem_FP hw hy hy' heUM heVB hwU))))))

/-! ## The size of one view's clauses -/

theorem stepClausesView_length (u v s : ℕ) (V : StepView tm T) :
    (stepClausesView tm T u v s V).length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4) := by
  rw [stepClausesView, List.length_append, List.length_append, List.length_map,
    stateList_length, List.length_flatMap, List.length_flatMap,
    sum_map_const (T + 1) _ _ (fun t _ => by rw [List.length_map, List.length_finRange]),
    sum_map_const 4 _ _ (fun t _ => by rw [List.length_map, symbolList_length]),
    tapeList_length]

/-! ## Which atom a view clause forces -/

theorem tapeList_getElem?_index (tape : TapeSlot k) :
    (tapeList k)[tape.index.val]? = some tape := by
  rw [tapeList_getElem? _ tape.index.isLt]
  congr 1
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp [tapeSlotEquiv_apply])

/-- **A view's index decodes to its transition case and its head tuple.** -/
theorem viewList_getElem? (v : ℕ) (hv : v < (caseList tm).length * (T + 1) ^ (k + 2)) :
    (viewList tm T)[v]?
      = ((caseList tm)[v / (T + 1) ^ (k + 2)]?).map fun tc =>
          (tc, headTupleOf k T ⟨v % (T + 1) ^ (k + 2),
            Nat.mod_lt _ (by positivity)⟩) := by
  have hpow : 0 < (T + 1) ^ (k + 2) := by positivity
  rw [viewList, ← caseList,
    getElem?_flatMap_const ((T + 1) ^ (k + 2)) hpow _
      (fun tc => by rw [List.length_map, List.length_finRange]) (caseList tm) v hv]
  rcases hc : (caseList tm)[v / (T + 1) ^ (k + 2)]? with _ | tc
  · rfl
  · rw [Option.bind_some, Option.map_some, List.getElem?_map,
      finRange_getElem? _ _ (Nat.mod_lt _ hpow), Option.map_some]

theorem stepClausesView_getElem?_state (u v s : ℕ) (V : StepView tm T) (i : ℕ)
    (hi : i < Fintype.card tm.Q) :
    (stepClausesView tm T u v s V)[i]?
      = ((stateList tm)[i]?).map fun q =>
          forceAtom tm T u v s V (.state q) (decide (newStateV tm T V = q)) := by
  rw [stepClausesView, List.getElem?_append_left (by
      rw [List.length_map, stateList_length]
      exact hi), List.getElem?_map]

theorem stepClausesView_getElem?_head (u v s : ℕ) (V : StepView tm T) (i : ℕ)
    (h₁ : Fintype.card tm.Q ≤ i) (h₂ : i < Fintype.card tm.Q + (k + 2) * (T + 1)) :
    (stepClausesView tm T u v s V)[i]?
      = ((tapeList k)[(i - Fintype.card tm.Q) / (T + 1)]?).bind fun t =>
          (((List.finRange (T + 1)).map fun p =>
            forceAtom tm T u v s V (.head t p)
              (decide (newHeadV tm T V t = p.val)))[(i - Fintype.card tm.Q) % (T + 1)]?) := by
  have hq : ((stateList tm).map fun q =>
      forceAtom tm T u v s V (.state q) (decide (newStateV tm T V = q))).length
      = Fintype.card tm.Q := by
    rw [List.length_map, stateList_length]
  rw [stepClausesView, List.getElem?_append_right (by rw [hq]; exact h₁), hq,
    List.getElem?_append_left (by
      rw [List.length_flatMap,
        sum_map_const (T + 1) _ _ (fun t _ => by
          rw [List.length_map, List.length_finRange]), tapeList_length]
      omega),
    getElem?_flatMap_const (T + 1) (by omega) _
      (fun t => by rw [List.length_map, List.length_finRange]) (tapeList k)
      (i - Fintype.card tm.Q) (by rw [tapeList_length]; omega)]

theorem stepClausesView_getElem?_cell (u v s : ℕ) (V : StepView tm T) (i : ℕ)
    (h₁ : Fintype.card tm.Q + (k + 2) * (T + 1) ≤ i)
    (h₂ : i < Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4)) :
    (stepClausesView tm T u v s V)[i]?
      = ((tapeList k)[(i - Fintype.card tm.Q - (k + 2) * (T + 1)) / 4]?).bind fun t =>
          ((symbolList.map fun sym =>
            forceAtom tm T u v s V (.cell t (headCellPosition (V.2 t)) sym)
              (decide (newSymV tm T V t = sym)))[(i - Fintype.card tm.Q
                - (k + 2) * (T + 1)) % 4]?) := by
  have hq : ((stateList tm).map fun q =>
      forceAtom tm T u v s V (.state q) (decide (newStateV tm T V = q))).length
      = Fintype.card tm.Q := by
    rw [List.length_map, stateList_length]
  have hh : (((tapeList k).flatMap fun t => (List.finRange (T + 1)).map fun p =>
      forceAtom tm T u v s V (.head t p)
        (decide (newHeadV tm T V t = p.val))).length) = (k + 2) * (T + 1) := by
    rw [List.length_flatMap,
      sum_map_const (T + 1) _ _ (fun t _ => by
        rw [List.length_map, List.length_finRange]), tapeList_length]
  rw [stepClausesView, List.getElem?_append_right (by rw [hq]; omega), hq,
    List.getElem?_append_right (by rw [hh]; omega), hh,
    getElem?_flatMap_const 4 (by omega) _
      (fun t => by rw [List.length_map, symbolList_length])
      (tapeList k) (i - Fintype.card tm.Q - (k + 2) * (T + 1))
      (by rw [tapeList_length]; omega)]

/-! ## Splitting the step clauses -/

theorem viewList_length :
    (viewList tm T).length
      = Fintype.card (TransitionCase tm) * (T + 1) ^ (k + 2) := by
  rw [viewList, List.length_flatMap,
    sum_map_const ((T + 1) ^ (k + 2)) _ _ (fun tc _ => by
      rw [List.length_map, List.length_finRange]),
    Finset.length_toList, Finset.card_univ]

theorem stepClauses_getElem?_view (u v s i : ℕ)
    (hpos : 0 < Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hi : i < (viewList tm T).length
      * (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))) :
    (stepClauses tm T u v s)[i]?
      = ((viewList tm T)[i / (Fintype.card tm.Q
            + ((k + 2) * (T + 1) + (k + 2) * 4))]?).bind fun V =>
          (stepClausesView tm T u v s V)[i % (Fintype.card tm.Q
            + ((k + 2) * (T + 1) + (k + 2) * 4))]? := by
  rw [stepClauses, List.getElem?_append_left (by
      rw [List.length_flatMap,
        sum_map_const (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4)) _ _
          (fun V _ => stepClausesView_length tm T u v s V)]
      exact hi),
    getElem?_flatMap_const (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4)) hpos _
      (fun V => stepClausesView_length tm T u v s V) (viewList tm T) i hi]

theorem stepClauses_getElem?_frame (u v s i : ℕ)
    (hge : (viewList tm T).length
      * (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4)) ≤ i) :
    (stepClauses tm T u v s)[i]?
      = (frameClauses tm T u v)[i - (viewList tm T).length
          * (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))]? := by
  have hlen : ((viewList tm T).flatMap fun V => stepClausesView tm T u v s V).length
      = (viewList tm T).length
        * (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4)) := by
    rw [List.length_flatMap,
      sum_map_const (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4)) _ _
        (fun V _ => stepClausesView_length tm T u v s V)]
  rw [stepClauses, List.getElem?_append_right (by rw [hlen]; exact hge), hlen]

/-! ## Indexing the frame clauses -/

theorem framePairOr_length (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1)) (pos : Fin (T + 2))
    (sym : Γ) : (framePairOr tm T u v t p pos sym).length = 2 := by
  rw [framePairOr]
  split <;> rfl

theorem frameSym_length (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1)) (pos : Fin (T + 2)) :
    (symbolList.flatMap fun sym =>
        framePairOr tm T u v t p pos sym).length = 4 * 2 := by
  rw [List.length_flatMap,
    sum_map_const 2 _ _ (fun sym _ => framePairOr_length tm T u v t p pos sym),
    symbolList_length]

theorem framePos_length (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1)) :
    ((List.finRange (T + 2)).flatMap fun pos =>
        symbolList.flatMap fun sym =>
          framePairOr tm T u v t p pos sym).length = (T + 2) * (4 * 2) := by
  rw [List.length_flatMap,
    sum_map_const (4 * 2) _ _ (fun pos _ => frameSym_length tm T u v t p pos),
    List.length_finRange]

theorem frameP_length (u v : ℕ) (t : TapeSlot k) :
    ((List.finRange (T + 1)).flatMap fun p =>
        (List.finRange (T + 2)).flatMap fun pos =>
          symbolList.flatMap fun sym =>
            framePairOr tm T u v t p pos sym).length
      = (T + 1) * ((T + 2) * (4 * 2)) := by
  rw [List.length_flatMap,
    sum_map_const ((T + 2) * (4 * 2)) _ _ (fun p _ => framePos_length tm T u v t p),
    List.length_finRange]

theorem frameClauses_length (u v : ℕ) :
    (frameClauses tm T u v).length = (k + 2) * ((T + 1) * ((T + 2) * (4 * 2))) := by
  rw [frameClauses, List.length_flatMap,
    sum_map_const ((T + 1) * ((T + 2) * (4 * 2))) _ _ (fun t _ => frameP_length tm T u v t),
    tapeList_length]

/-- **Indexing the frame clauses**: the tape, then the head position, the cell position and the
symbol. -/
theorem frameClauses_getElem?_tape (u v i : ℕ)
    (hi : i < (k + 2) * ((T + 1) * ((T + 2) * (4 * 2)))) :
    (frameClauses tm T u v)[i]?
      = ((tapeList k)[i / ((T + 1) * ((T + 2) * (4 * 2)))]?).bind fun t =>
          ((List.finRange (T + 1)).flatMap fun p =>
            (List.finRange (T + 2)).flatMap fun pos =>
              symbolList.flatMap fun sym =>
                framePairOr tm T u v t p pos sym)[i % ((T + 1) * ((T + 2) * (4 * 2)))]? := by
  rw [frameClauses,
    getElem?_flatMap_const ((T + 1) * ((T + 2) * (4 * 2))) (by positivity) _
      (fun t => frameP_length tm T u v t) (tapeList k) i (by rw [tapeList_length]; exact hi)]

theorem frameP_getElem?_head (u v : ℕ) (t : TapeSlot k) (j : ℕ)
    (hj : j < (T + 1) * ((T + 2) * (4 * 2))) :
    ((List.finRange (T + 1)).flatMap fun p =>
        (List.finRange (T + 2)).flatMap fun pos =>
          symbolList.flatMap fun sym =>
            framePairOr tm T u v t p pos sym)[j]?
      = ((List.finRange (T + 1))[j / ((T + 2) * (4 * 2))]?).bind fun p =>
          ((List.finRange (T + 2)).flatMap fun pos =>
            symbolList.flatMap fun sym =>
              framePairOr tm T u v t p pos sym)[j % ((T + 2) * (4 * 2))]? := by
  rw [getElem?_flatMap_const ((T + 2) * (4 * 2)) (by positivity) _
    (fun p => framePos_length tm T u v t p) (List.finRange (T + 1)) j
    (by rw [List.length_finRange]; exact hj)]

theorem framePos_getElem?_cell (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1)) (j : ℕ)
    (hj : j < (T + 2) * (4 * 2)) :
    ((List.finRange (T + 2)).flatMap fun pos =>
        symbolList.flatMap fun sym =>
          framePairOr tm T u v t p pos sym)[j]?
      = ((List.finRange (T + 2))[j / (4 * 2)]?).bind fun pos =>
          (symbolList.flatMap fun sym =>
            framePairOr tm T u v t p pos sym)[j % (4 * 2)]? := by
  rw [getElem?_flatMap_const (4 * 2) (by omega) _
    (fun pos => frameSym_length tm T u v t p pos) (List.finRange (T + 2)) j
    (by rw [List.length_finRange]; exact hj)]

theorem frameSym_getElem?_sym (u v : ℕ) (t : TapeSlot k) (p : Fin (T + 1))
    (pos : Fin (T + 2)) (j : ℕ) (hj : j < 4 * 2) :
    (symbolList.flatMap fun sym =>
        framePairOr tm T u v t p pos sym)[j]?
      = (symbolList[j / 2]?).bind fun sym =>
          (framePairOr tm T u v t p pos sym)[j % 2]? := by
  rw [getElem?_flatMap_const 2 (by omega) _
    (fun sym => framePairOr_length tm T u v t p pos sym)
    symbolList j
    (by rw [symbolList_length]; exact hj)]

/-! ## Indexing the base clauses -/

theorem stepClauses_length (u v s : ℕ) :
    (stepClauses tm T u v s).length
      = (viewList tm T).length
          * (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
        + (k + 2) * ((T + 1) * ((T + 2) * (4 * 2))) := by
  rw [stepClauses, List.length_append, List.length_flatMap,
    sum_map_const (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4)) _ _
      (fun V _ => stepClausesView_length tm T u v s V), frameClauses_length]

theorem cfgBaseC_getElem?_eq (u v s p : ℕ) (hp : p < configWidth tm T * 2) :
    (cfgBaseC tm T u v s)[p]?
      = ((QBF.eqClauses (configWidth tm T) u v)[p]?).map fun c => ((false, s + 1) : CLit) :: c := by
  rw [cfgBaseC, QBF.orCNF, List.getElem?_append_left (by
      rw [QBF.disjLit_length, eqClauses_length]
      exact hp), QBF.disjLit_getElem?]

theorem cfgBaseC_getElem?_step (u v s p : ℕ) (hge : configWidth tm T * 2 ≤ p) :
    (cfgBaseC tm T u v s)[p]?
      = ((stepClauses tm T u v s)[p - configWidth tm T * 2]?).map fun c =>
          ((true, s + 1) : CLit) :: c := by
  rw [cfgBaseC, QBF.orCNF, List.getElem?_append_right (by
      rw [QBF.disjLit_length, eqClauses_length]
      exact hge), QBF.disjLit_length, eqClauses_length, QBF.disjLit_getElem?]

/-! ## Decoding a frame clause index -/

/-- The tape a frame index names. -/
noncomputable def frTape (blkTU pU : List Bool) : List Bool := divFn2 (pair blkTU pU)

/-- What is left of a frame index after the tape. -/
noncomputable def frRest (blkTU pU : List Bool) : List Bool := modFn2 (pair blkTU pU)

/-- The head position a frame index names. -/
noncomputable def frHead (blkTU blkPU pU : List Bool) : List Bool :=
  divFn2 (pair blkPU (frRest blkTU pU))

/-- What is left after the head position. -/
noncomputable def frRest2 (blkTU blkPU pU : List Bool) : List Bool :=
  modFn2 (pair blkPU (frRest blkTU pU))

/-- The cell position a frame index names. -/
noncomputable def frPos (blkTU blkPU blkPosU pU : List Bool) : List Bool :=
  divFn2 (pair blkPosU (frRest2 blkTU blkPU pU))

/-- What is left after the cell position. -/
noncomputable def frRest3 (blkTU blkPU blkPosU pU : List Bool) : List Bool :=
  modFn2 (pair blkPosU (frRest2 blkTU blkPU pU))

/-- The symbol a frame index names. -/
noncomputable def frSym (blkTU blkPU blkPosU pU : List Bool) : List Bool :=
  divC 2 (frRest3 blkTU blkPU blkPosU pU)

/-- Which of a pair's two frame clauses the index names. -/
noncomputable def frSel (blkTU blkPU blkPosU pU : List Bool) : List Bool :=
  modC 2 (frRest3 blkTU blkPU blkPosU pU)

theorem frTape_length (blkTU pU : List Bool) (hb : 0 < blkTU.length) :
    (frTape blkTU pU).length = pU.length / blkTU.length := by
  rw [frTape, divFn2_eq hb, List.length_replicate]

theorem frRest_length (blkTU pU : List Bool) (hb : 0 < blkTU.length) :
    (frRest blkTU pU).length = pU.length % blkTU.length := by
  rw [frRest, modFn2_eq hb, List.length_replicate]

theorem frHead_length (blkTU blkPU pU : List Bool) (hb : 0 < blkTU.length)
    (hp : 0 < blkPU.length) :
    (frHead blkTU blkPU pU).length = pU.length % blkTU.length / blkPU.length := by
  rw [frHead, divFn2_eq hp, List.length_replicate, frRest_length _ _ hb]

theorem frRest2_length (blkTU blkPU pU : List Bool) (hb : 0 < blkTU.length)
    (hp : 0 < blkPU.length) :
    (frRest2 blkTU blkPU pU).length = pU.length % blkTU.length % blkPU.length := by
  rw [frRest2, modFn2_eq hp, List.length_replicate, frRest_length _ _ hb]

theorem frPos_length (blkTU blkPU blkPosU pU : List Bool) (hb : 0 < blkTU.length)
    (hp : 0 < blkPU.length) (hpos : 0 < blkPosU.length) :
    (frPos blkTU blkPU blkPosU pU).length
      = pU.length % blkTU.length % blkPU.length / blkPosU.length := by
  rw [frPos, divFn2_eq hpos, List.length_replicate, frRest2_length _ _ _ hb hp]

theorem frRest3_length (blkTU blkPU blkPosU pU : List Bool) (hb : 0 < blkTU.length)
    (hp : 0 < blkPU.length) (hpos : 0 < blkPosU.length) :
    (frRest3 blkTU blkPU blkPosU pU).length
      = pU.length % blkTU.length % blkPU.length % blkPosU.length := by
  rw [frRest3, modFn2_eq hpos, List.length_replicate, frRest2_length _ _ _ hb hp]

theorem frSym_length' (blkTU blkPU blkPosU pU : List Bool) (hb : 0 < blkTU.length)
    (hp : 0 < blkPU.length) (hpos : 0 < blkPosU.length) :
    (frSym blkTU blkPU blkPosU pU).length
      = pU.length % blkTU.length % blkPU.length % blkPosU.length / 2 := by
  rw [frSym, divC_eq (by norm_num), List.length_replicate,
    frRest3_length _ _ _ _ hb hp hpos]

theorem frSel_length (blkTU blkPU blkPosU pU : List Bool) (hb : 0 < blkTU.length)
    (hp : 0 < blkPU.length) (hpos : 0 < blkPosU.length) :
    (frSel blkTU blkPU blkPosU pU).length
      = pU.length % blkTU.length % blkPU.length % blkPosU.length % 2 := by
  rw [frSel, modC_eq (by norm_num), List.length_replicate,
    frRest3_length _ _ _ _ hb hp hpos]

theorem frTape_mem_FP {blkTU pU : List Bool → List Bool} (hb : blkTU ∈ FP) (hp : pU ∈ FP) :
    (fun z => frTape (blkTU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hb hp) divFn2_mem_FP) fun _ => rfl

theorem frRest_mem_FP {blkTU pU : List Bool → List Bool} (hb : blkTU ∈ FP) (hp : pU ∈ FP) :
    (fun z => frRest (blkTU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hb hp) modFn2_mem_FP) fun _ => rfl

theorem frHead_mem_FP {blkTU blkPU pU : List Bool → List Bool} (hb : blkTU ∈ FP)
    (hbp : blkPU ∈ FP) (hp : pU ∈ FP) :
    (fun z => frHead (blkTU z) (blkPU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hbp (frRest_mem_FP hb hp))
    divFn2_mem_FP) fun _ => rfl

theorem frRest2_mem_FP {blkTU blkPU pU : List Bool → List Bool} (hb : blkTU ∈ FP)
    (hbp : blkPU ∈ FP) (hp : pU ∈ FP) :
    (fun z => frRest2 (blkTU z) (blkPU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hbp (frRest_mem_FP hb hp))
    modFn2_mem_FP) fun _ => rfl

theorem frPos_mem_FP {blkTU blkPU blkPosU pU : List Bool → List Bool} (hb : blkTU ∈ FP)
    (hbp : blkPU ∈ FP) (hbs : blkPosU ∈ FP) (hp : pU ∈ FP) :
    (fun z => frPos (blkTU z) (blkPU z) (blkPosU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hbs (frRest2_mem_FP hb hbp hp))
    divFn2_mem_FP) fun _ => rfl

theorem frRest3_mem_FP {blkTU blkPU blkPosU pU : List Bool → List Bool} (hb : blkTU ∈ FP)
    (hbp : blkPU ∈ FP) (hbs : blkPosU ∈ FP) (hp : pU ∈ FP) :
    (fun z => frRest3 (blkTU z) (blkPU z) (blkPosU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hbs (frRest2_mem_FP hb hbp hp))
    modFn2_mem_FP) fun _ => rfl

theorem frSym_mem_FP {blkTU blkPU blkPosU pU : List Bool → List Bool} (hb : blkTU ∈ FP)
    (hbp : blkPU ∈ FP) (hbs : blkPosU ∈ FP) (hp : pU ∈ FP) :
    (fun z => frSym (blkTU z) (blkPU z) (blkPosU z) (pU z)) ∈ FP :=
  divC_mem_FP (frRest3_mem_FP hb hbp hbs hp) 2

theorem frSel_mem_FP {blkTU blkPU blkPosU pU : List Bool → List Bool} (hb : blkTU ∈ FP)
    (hbp : blkPU ∈ FP) (hbs : blkPosU ∈ FP) (hp : pU ∈ FP) :
    (fun z => frSel (blkTU z) (blkPU z) (blkPosU z) (pU z)) ∈ FP :=
  modC_mem_FP (frRest3_mem_FP hb hbp hbs hp) 2

/-- One frame clause, encoded from its index. -/
noncomputable def frameIdxEnc (w uU vU qU hdU horU hor2U blkTU blkPU blkPosU pU : List Bool) :
    List Bool :=
  frameEnc w
    (headWireU uU qU (frTape blkTU pU) (frHead blkTU blkPU pU) horU)
    (cellWireU uU qU hdU (frTape blkTU pU) (frPos blkTU blkPU blkPosU pU) hor2U
      (frSym blkTU blkPU blkPosU pU))
    (cellWireU vU qU hdU (frTape blkTU pU) (frPos blkTU blkPU blkPosU pU) hor2U
      (frSym blkTU blkPU blkPosU pU))
    (frPos blkTU blkPU blkPosU pU) (frHead blkTU blkPU pU)
    (frSel blkTU blkPU blkPosU pU)

theorem symbolList_getElem? (m : ℕ) (hm : m < 4) :
    symbolList[m]? = some (symbolList[m]'(by rw [symbolList_length]; exact hm)) :=
  List.getElem?_eq_getElem (by rw [symbolList_length]; exact hm)

/-- **A frame clause, encoded.** -/
theorem frameIdxEnc_value (w uU vU qU hdU horU hor2U blkTU blkPU blkPosU : List Bool)
    (hq : qU.length = Fintype.card tm.Q) (hhd : hdU.length = (k + 2) * (T + 1))
    (hhor : horU.length = T + 1) (hhor2 : hor2U.length = T + 2)
    (hblkT : blkTU.length = (T + 1) * ((T + 2) * (4 * 2)))
    (hblkP : blkPU.length = (T + 2) * (4 * 2)) (hblkPos : blkPosU.length = 4 * 2)
    (i : ℕ) (hi : i < (k + 2) * ((T + 1) * ((T + 2) * (4 * 2))))
    (h₀ : (headWireU uU qU (frTape blkTU (List.replicate i true))
      (frHead blkTU blkPU (List.replicate i true)) horU).length ≤ w.length)
    (h₁ : (cellWireU uU qU hdU (frTape blkTU (List.replicate i true))
      (frPos blkTU blkPU blkPosU (List.replicate i true)) hor2U
      (frSym blkTU blkPU blkPosU (List.replicate i true))).length ≤ w.length)
    (h₂ : (cellWireU vU qU hdU (frTape blkTU (List.replicate i true))
      (frPos blkTU blkPU blkPosU (List.replicate i true)) hor2U
      (frSym blkTU blkPU blkPosU (List.replicate i true))).length ≤ w.length) :
    ((frameClauses tm T uU.length vU.length)[i]?).map DataEncode.bitstringEncode
      = some (frameIdxEnc w uU vU qU hdU horU hor2U blkTU blkPU blkPosU
          (List.replicate i true)) := by
  have hTpos : 0 < (T + 1) * ((T + 2) * (4 * 2)) := by positivity
  have hPpos : 0 < (T + 2) * (4 * 2) := by positivity
  have hlenrep : (List.replicate i true).length = i := List.length_replicate
  have hcomm : (k + 2) * ((T + 1) * ((T + 2) * (4 * 2)))
      = (T + 1) * ((T + 2) * (4 * 2)) * (k + 2) := Nat.mul_comm _ _
  have hit : i / ((T + 1) * ((T + 2) * (4 * 2))) < k + 2 :=
    Nat.div_lt_of_lt_mul (by omega)
  have hj : i % ((T + 1) * ((T + 2) * (4 * 2))) < (T + 1) * ((T + 2) * (4 * 2)) :=
    Nat.mod_lt _ hTpos
  have hip : i % ((T + 1) * ((T + 2) * (4 * 2))) / ((T + 2) * (4 * 2)) < T + 1 :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm ((T + 2) * (4 * 2)) (T + 1)]; exact hj)
  have hj2 : i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) < (T + 2) * (4 * 2) :=
    Nat.mod_lt _ hPpos
  have hipos : i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) / (4 * 2) < T + 2 :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (4 * 2) (T + 2)]; exact hj2)
  have hj3 : i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2) < 4 * 2 :=
    Nat.mod_lt _ (by omega)
  have hisym : i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2) / 2 < 4 := by
    omega
  have htape : (frTape blkTU (List.replicate i true)).length
      = ((tapeSlotEquiv k).symm ⟨i / ((T + 1) * ((T + 2) * (4 * 2))), hit⟩).index.val := by
    rw [frTape_length _ _ (by omega), hlenrep, hblkT, tapeSlotEquiv_symm_index]
  have hhead : (frHead blkTU blkPU (List.replicate i true)).length
      = i % ((T + 1) * ((T + 2) * (4 * 2))) / ((T + 2) * (4 * 2)) := by
    rw [frHead_length _ _ _ (by omega) (by omega), hlenrep, hblkT, hblkP]
  have hposv : (frPos blkTU blkPU blkPosU (List.replicate i true)).length
      = i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) / (4 * 2) := by
    rw [frPos_length _ _ _ _ (by omega) (by omega) (by omega), hlenrep, hblkT, hblkP,
      hblkPos]
  have hsymv : (frSym blkTU blkPU blkPosU (List.replicate i true)).length
      = i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2) / 2 := by
    rw [frSym_length' _ _ _ _ (by omega) (by omega) (by omega), hlenrep, hblkT, hblkP,
      hblkPos]
  have hselv : (frSel blkTU blkPU blkPosU (List.replicate i true)).length
      = i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2) % 2 := by
    rw [frSel_length _ _ _ _ (by omega) (by omega) (by omega), hlenrep, hblkT, hblkP,
      hblkPos]
  rw [frameClauses_getElem?_tape tm T uU.length vU.length i hi, tapeList_getElem? _ hit,
    Option.bind_some,
    frameP_getElem?_head tm T uU.length vU.length _ _ hj, finRange_getElem? _ _ hip,
    Option.bind_some,
    framePos_getElem?_cell tm T uU.length vU.length _ _ _ hj2,
    finRange_getElem? _ _ hipos, Option.bind_some,
    frameSym_getElem?_sym tm T uU.length vU.length _ _ _ _ hj3,
    symbolList_getElem? _ hisym, Option.bind_some, framePairOr, frameIdxEnc, frameEnc]
  have hwire : (headWireU uU qU (frTape blkTU (List.replicate i true))
      (frHead blkTU blkPU (List.replicate i true)) horU).length
      = configWire tm T uU.length (.head
          ((tapeSlotEquiv k).symm ⟨i / ((T + 1) * ((T + 2) * (4 * 2))), hit⟩)
          ⟨i % ((T + 1) * ((T + 2) * (4 * 2))) / ((T + 2) * (4 * 2)), hip⟩) :=
    headWireU_eq tm T uU.length _ _ rfl hq htape hhead hhor
  have hcellu : (cellWireU uU qU hdU (frTape blkTU (List.replicate i true))
      (frPos blkTU blkPU blkPosU (List.replicate i true)) hor2U
      (frSym blkTU blkPU blkPosU (List.replicate i true))).length
      = configWire tm T uU.length (.cell
          ((tapeSlotEquiv k).symm ⟨i / ((T + 1) * ((T + 2) * (4 * 2))), hit⟩)
          ⟨i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) / (4 * 2), hipos⟩
          (symbolList[i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2)
            / 2]'(by rw [symbolList_length]; exact hisym))) :=
    cellWireU_eq tm T uU.length _ _ _ rfl hq hhd htape hposv hhor2
      (by rw [hsymv, symbolIndex_symbolList _ hisym])
  have hcellv : (cellWireU vU qU hdU (frTape blkTU (List.replicate i true))
      (frPos blkTU blkPU blkPosU (List.replicate i true)) hor2U
      (frSym blkTU blkPU blkPosU (List.replicate i true))).length
      = configWire tm T vU.length (.cell
          ((tapeSlotEquiv k).symm ⟨i / ((T + 1) * ((T + 2) * (4 * 2))), hit⟩)
          ⟨i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) / (4 * 2), hipos⟩
          (symbolList[i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2)
            / 2]'(by rw [symbolList_length]; exact hisym))) :=
    cellWireU_eq tm T vU.length _ _ _ rfl hq hhd htape hposv hhor2
      (by rw [hsymv, symbolIndex_symbolList _ hisym])
  by_cases hdiag : i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) / (4 * 2)
      = i % ((T + 1) * ((T + 2) * (4 * 2))) / ((T + 2) * (4 * 2))
  · rw [if_pos hdiag, ifEqLen_pos (by rw [hposv, hhead]; exact hdiag),
      clause2_eq false true (litEnc_neg h₀) (litEnc_pos (by simp) h₀), hwire]
    have hsel : i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2) % 2 = 0 ∨
        i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2) % 2 = 1 := by
      omega
    rcases hsel with h | h <;> rw [h] <;> rfl
  · rw [if_neg hdiag, ifEqLen_neg (by rw [hposv, hhead]; exact hdiag), framePair]
    by_cases hsel : i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2) % 2
        = 0
    · rw [hsel, ifEqLen_pos (by rw [hselv, hsel]; rfl),
        clause3_eq false false true (litEnc_neg h₀) (litEnc_neg h₁)
          (litEnc_pos (by simp) h₂), hwire, hcellu, hcellv]
      rfl
    · have h1 : i % ((T + 1) * ((T + 2) * (4 * 2))) % ((T + 2) * (4 * 2)) % (4 * 2) % 2
          = 1 := by omega
      rw [h1, ifEqLen_neg (by rw [hselv, h1]; simp),
        clause3_eq false true false (litEnc_neg h₀) (litEnc_pos (by simp) h₁)
          (litEnc_neg h₂), hwire, hcellu, hcellv]
      rfl

theorem frameIdxEnc_mem_FP
    {w uU vU qU hdU horU hor2U blkTU blkPU blkPosU pU : List Bool → List Bool} (hw : w ∈ FP)
    (hu : uU ∈ FP) (hv : vU ∈ FP) (hq : qU ∈ FP) (hhd : hdU ∈ FP) (hhor : horU ∈ FP)
    (hhor2 : hor2U ∈ FP) (hb : blkTU ∈ FP) (hbp : blkPU ∈ FP) (hbs : blkPosU ∈ FP)
    (hp : pU ∈ FP) :
    (fun z => frameIdxEnc (w z) (uU z) (vU z) (qU z) (hdU z) (horU z) (hor2U z) (blkTU z)
      (blkPU z) (blkPosU z) (pU z)) ∈ FP := by
  have htape := frTape_mem_FP hb hp
  have hhead := frHead_mem_FP hb hbp hp
  have hpos := frPos_mem_FP hb hbp hbs hp
  have hsym := frSym_mem_FP hb hbp hbs hp
  have hsel := frSel_mem_FP hb hbp hbs hp
  exact frameEnc_mem_FP hw (headWireU_mem_FP hu hq htape hhead hhor)
    (cellWireU_mem_FP hu hq hhd htape hpos hhor2 hsym)
    (cellWireU_mem_FP hv hq hhd htape hpos hhor2 hsym) hpos hhead hsel

/-! ## Decoding which atom a view clause forces -/

/-- What is left of an atom index after the state segment. -/
noncomputable def atRest (qU aU : List Bool) : List Bool := aU.drop qU.length

/-- The tape of a head atom. -/
noncomputable def atHeadTape (qU horU aU : List Bool) : List Bool :=
  divFn2 (pair horU (atRest qU aU))

/-- The position of a head atom. -/
noncomputable def atHeadPos (qU horU aU : List Bool) : List Bool :=
  modFn2 (pair horU (atRest qU aU))

/-- What is left of an atom index after the head segment. -/
noncomputable def atRest2 (qU horU tapesU aU : List Bool) : List Bool :=
  (atRest qU aU).drop (mulLen tapesU horU).length

/-- The tape of a cell atom. -/
noncomputable def atCellTape (qU horU tapesU aU : List Bool) : List Bool :=
  divC 4 (atRest2 qU horU tapesU aU)

/-- The symbol of a cell atom. -/
noncomputable def atCellSym (qU horU tapesU aU : List Bool) : List Bool :=
  modC 4 (atRest2 qU horU tapesU aU)

/-- The wire of the atom a view clause forces. -/
noncomputable def atomWireU (vU qU hdU horU hor2U tapesU viewU aU : List Bool) : List Bool :=
  ifLtLen aU qU (vU ++ aU)
    (ifLtLen (atRest qU aU) (mulLen tapesU horU)
      (headWireU vU qU (atHeadTape qU horU aU) (atHeadPos qU horU aU) horU)
      (cellWireU vU qU hdU (atCellTape qU horU tapesU aU)
        (headDigitU horU (atCellTape qU horU tapesU aU) viewU) hor2U
        (atCellSym qU horU tapesU aU)))

/-! ## What a forced atom's index decodes to -/

theorem atomWireU_state_eq (qU hdU horU hor2U tapesU viewU aU : List Bool) (q : tm.Q)
    (hq : qU.length = Fintype.card tm.Q) (ha : aU.length = stateIndex tm q) :
    (atomWireU [] qU hdU horU hor2U tapesU viewU aU).length
      = configIndex tm T (ConfigAtom.state q) := by
  rw [atomWireU, ifLtLen_pos (by rw [ha, hq]; exact (Fintype.equivFin tm.Q q).isLt),
    List.length_append, List.length_nil, Nat.zero_add, ha, configIndex_state]

theorem atomWireU_head_eq (qU hdU horU hor2U tapesU viewU aU : List Bool)
    (tape : TapeSlot k) (p : Fin (T + 1))
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (htapes : tapesU.length = k + 2)
    (ha : aU.length = Fintype.card tm.Q + (tape.index.val * (T + 1) + p.val)) :
    (atomWireU [] qU hdU horU hor2U tapesU viewU aU).length
      = configIndex tm T (ConfigAtom.head tape p) := by
  have hrest : (atRest qU aU).length = tape.index.val * (T + 1) + p.val := by
    rw [atRest, List.length_drop, ha, hq]
    omega
  have hblk : tape.index.val * (T + 1) + p.val < (k + 2) * (T + 1) := by
    have h1 : (tape.index.val + 1) * (T + 1) ≤ (k + 2) * (T + 1) :=
      Nat.mul_le_mul_right _ tape.index.isLt
    have h2 : (tape.index.val + 1) * (T + 1) = tape.index.val * (T + 1) + (T + 1) := by ring
    have := p.isLt
    omega
  have htp : (atHeadTape qU horU aU).length = tape.index.val := by
    rw [atHeadTape, divFn2_eq (by rw [hhor]; omega), List.length_replicate, hrest, hhor]
    have h2 : tape.index.val * (T + 1) + p.val = (T + 1) * tape.index.val + p.val := by ring
    rw [h2, Nat.mul_add_div (by omega), Nat.div_eq_of_lt p.isLt]
    omega
  have hpp : (atHeadPos qU horU aU).length = p.val := by
    rw [atHeadPos, modFn2_eq (by rw [hhor]; omega), List.length_replicate, hrest, hhor]
    have h2 : tape.index.val * (T + 1) + p.val = (T + 1) * tape.index.val + p.val := by ring
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
  rw [atomWireU, ifLtLen_neg (by rw [ha, hq]; omega),
    ifLtLen_pos (by rw [hrest, length_mulLen, htapes, hhor]; exact hblk),
    headWireU_eq tm T 0 tape p rfl hq htp hpp hhor, configWire, Nat.zero_add]

theorem atomWireU_cell_eq (qU hdU horU hor2U tapesU viewU aU : List Bool)
    (tape : TapeSlot k) (sym : Γ) (i : Fin ((T + 1) ^ (k + 2)))
    (hq : qU.length = Fintype.card tm.Q) (hhd : hdU.length = (k + 2) * (T + 1))
    (hhor : horU.length = T + 1) (hhor2 : hor2U.length = T + 2)
    (htapes : tapesU.length = k + 2) (hview : viewU.length = i.val)
    (ha : aU.length = Fintype.card tm.Q + (k + 2) * (T + 1)
      + (tape.index.val * 4 + (symbolIndex sym).val)) :
    (atomWireU [] qU hdU horU hor2U tapesU viewU aU).length
      = configIndex tm T
        (ConfigAtom.cell tape (headCellPosition (headTupleOf k T i tape)) sym) := by
  have hrest : (atRest qU aU).length
      = (k + 2) * (T + 1) + (tape.index.val * 4 + (symbolIndex sym).val) := by
    rw [atRest, List.length_drop, ha, hq]
    omega
  have hrest2 : (atRest2 qU horU tapesU aU).length
      = tape.index.val * 4 + (symbolIndex sym).val := by
    rw [atRest2, List.length_drop, hrest, length_mulLen, htapes, hhor]
    omega
  have htp : (atCellTape qU horU tapesU aU).length = tape.index.val := by
    rw [atCellTape, divC_eq (by norm_num), List.length_replicate, hrest2]
    have h2 : tape.index.val * 4 + (symbolIndex sym).val
        = 4 * tape.index.val + (symbolIndex sym).val := by ring
    rw [h2, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt (symbolIndex sym).isLt]
    omega
  have hsy : (atCellSym qU horU tapesU aU).length = (symbolIndex sym).val := by
    rw [atCellSym, modC_eq (by norm_num), List.length_replicate, hrest2]
    have h2 : tape.index.val * 4 + (symbolIndex sym).val
        = 4 * tape.index.val + (symbolIndex sym).val := by ring
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (symbolIndex sym).isLt]
  rw [atomWireU, ifLtLen_neg (by rw [ha, hq]; omega),
    ifLtLen_neg (by rw [hrest, length_mulLen, htapes, hhor]; omega),
    cellWireU_view_eq tm T [] qU hdU _ hor2U horU viewU _ i tape 0 sym rfl hq hhd htp hhor
      hhor2 hview hsy (headCellPosition (headTupleOf k T i tape)) rfl,
    configWire, Nat.zero_add]

theorem atRest_mem_FP {qU aU : List Bool → List Bool} (hq : qU ∈ FP) (ha : aU ∈ FP) :
    (fun z => atRest (qU z) (aU z)) ∈ FP := dropLenFn_mem_FP hq ha

theorem atHeadTape_mem_FP {qU horU aU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (ha : aU ∈ FP) :
    (fun z => atHeadTape (qU z) (horU z) (aU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hhor (atRest_mem_FP hq ha))
    divFn2_mem_FP) fun _ => rfl

theorem atHeadPos_mem_FP {qU horU aU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (ha : aU ∈ FP) :
    (fun z => atHeadPos (qU z) (horU z) (aU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hhor (atRest_mem_FP hq ha))
    modFn2_mem_FP) fun _ => rfl

theorem atRest2_mem_FP {qU horU tapesU aU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (ht : tapesU ∈ FP) (ha : aU ∈ FP) :
    (fun z => atRest2 (qU z) (horU z) (tapesU z) (aU z)) ∈ FP :=
  dropLenFn_mem_FP (mulLen_mem_FP ht hhor) (atRest_mem_FP hq ha)

theorem atCellTape_mem_FP {qU horU tapesU aU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (ht : tapesU ∈ FP) (ha : aU ∈ FP) :
    (fun z => atCellTape (qU z) (horU z) (tapesU z) (aU z)) ∈ FP :=
  divC_mem_FP (atRest2_mem_FP hq hhor ht ha) 4

theorem atCellSym_mem_FP {qU horU tapesU aU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (ht : tapesU ∈ FP) (ha : aU ∈ FP) :
    (fun z => atCellSym (qU z) (horU z) (tapesU z) (aU z)) ∈ FP :=
  modC_mem_FP (atRest2_mem_FP hq hhor ht ha) 4

theorem atomWireU_mem_FP {vU qU hdU horU hor2U tapesU viewU aU : List Bool → List Bool}
    (hv : vU ∈ FP) (hq : qU ∈ FP) (hhd : hdU ∈ FP) (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP)
    (ht : tapesU ∈ FP) (hview : viewU ∈ FP) (ha : aU ∈ FP)
    {E : ℕ} (hE : ∀ z, (atCellTape (qU z) (horU z) (tapesU z) (aU z)).length ≤ E)
    {width : List Bool → List Bool} (hwd : width ∈ FP)
    (hbound : ∀ z, (horU z).length ^ E + 2 * (horU z).length + 4 ≤ (width z).length) :
    (fun z => atomWireU (vU z) (qU z) (hdU z) (horU z) (hor2U z) (tapesU z) (viewU z)
      (aU z)) ∈ FP := by
  have hct := atCellTape_mem_FP hq hhor ht ha
  exact ifLtLen_mem_FP ha hq (Cobham.appendFn_mem_FP hv ha)
    (ifLtLen_mem_FP (atRest_mem_FP hq ha) (mulLen_mem_FP ht hhor)
      (headWireU_mem_FP hv hq (atHeadTape_mem_FP hq hhor ha)
        (atHeadPos_mem_FP hq hhor ha) hhor)
      (cellWireU_mem_FP hv hq hhd hct
        (headDigitU_mem_FP hhor hct hview E hE hwd hbound) hhor2
        (atCellSym_mem_FP hq hhor ht ha)))

/-! ## The value a view forces on an atom -/

/-- The state a transition case moves to. -/
noncomputable def newStateOfCase (c : TransitionCase tm) : tm.Q :=
  if c.state = tm.qhalt then c.state
  else (tm.δ c.choice c.state c.inputRead c.workRead c.outputRead).1

theorem newStateV_eq_ofCase (V : StepView tm T) :
    newStateV tm T V = newStateOfCase tm V.1 := rfl

/-- Whether the state atom an index names is the one the view forces. -/
noncomputable def stateForcedU (caseU aU : List Bool) : List Bool :=
  ifEqLen (tableU (caseList tm) (fun c => stateIndex tm (newStateOfCase tm c)) caseU) aU
    [false] []

theorem stateForcedU_eq (caseU aU : List Bool) (c : TransitionCase tm)
    (hlt : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hlt = c) :
    (stateForcedU tm caseU aU ≠ []) ↔ stateIndex tm (newStateOfCase tm c) = aU.length := by
  have htab : (tableU (caseList tm) (fun c => stateIndex tm (newStateOfCase tm c)) caseU).length
      = stateIndex tm (newStateOfCase tm c) := by
    rw [tableU_length _ _ _ hlt, hc]
  rw [stateForcedU]
  by_cases h : stateIndex tm (newStateOfCase tm c) = aU.length
  · rw [ifEqLen_pos (by rw [htab, h]), h]
    simp
  · rw [ifEqLen_neg (by rw [htab]; exact h)]
    simp [h]

theorem stateForcedU_mem_FP {caseU aU : List Bool → List Bool} (hcase : caseU ∈ FP)
    (ha : aU ∈ FP) {C : ℕ} (hC : ∀ z, (caseU z).length ≤ C) :
    (fun z => stateForcedU tm (caseU z) (aU z)) ∈ FP :=
  ifEqLen_mem_FP (tableU_mem_FP _ _ hcase hC) ha (constFn_mem_FP _) (constFn_mem_FP _)

/-- The symbol a transition case writes on a tape whose head sits at cell zero. -/
noncomputable def newSymOfCaseZero (c : TransitionCase tm) : TapeSlot k → Γ
  | .input => if c.state = tm.qhalt then c.read .input else c.inputRead
  | .work i => if c.state = tm.qhalt then c.read (.work i) else c.workRead i
  | .output => if c.state = tm.qhalt then c.read .output else c.outputRead

/-- The symbol a transition case writes on a tape whose head is past cell zero. -/
noncomputable def newSymOfCaseAway (c : TransitionCase tm) : TapeSlot k → Γ
  | .input => if c.state = tm.qhalt then c.read .input else c.inputRead
  | .work i =>
      if c.state = tm.qhalt then c.read (.work i)
      else ((tm.δ c.choice c.state c.inputRead c.workRead c.outputRead).2.1 i : Γ)
  | .output =>
      if c.state = tm.qhalt then c.read .output
      else ((tm.δ c.choice c.state c.inputRead c.workRead c.outputRead).2.2.1 : Γ)

theorem newSymV_eq_ofCase (V : StepView tm T) (t : TapeSlot k) :
    newSymV tm T V t
      = if (V.2 t).val = 0 then newSymOfCaseZero tm V.1 t else newSymOfCaseAway tm V.1 t := by
  rw [newSymV]
  cases t with
  | input =>
      rw [newSymOfCaseZero, newSymOfCaseAway]
      split <;> simp [viewWrite]
  | work i =>
      rw [newSymOfCaseZero, newSymOfCaseAway]
      by_cases hh : (V.2 (TapeSlot.work i)).val = 0 <;>
        by_cases hq : V.1.state = tm.qhalt <;>
        simp [hh, hq, viewWrite, viewDelta]
  | output =>
      rw [newSymOfCaseZero, newSymOfCaseAway]
      by_cases hh : (V.2 (TapeSlot.output : TapeSlot k)).val = 0 <;>
        by_cases hq : V.1.state = tm.qhalt <;>
        simp [hh, hq, viewWrite, viewDelta]

/-- Whether the cell atom an index names holds the symbol the view writes. -/
noncomputable def cellForcedU (caseU tapeU digitU symU : List Bool) : List Bool :=
  ifEqLen digitU []
    (ifEqLen (tableU2 (caseList tm) (tapeList k)
      (fun c t => (symbolIndex (newSymOfCaseZero tm c t)).val) caseU tapeU) symU [false] [])
    (ifEqLen (tableU2 (caseList tm) (tapeList k)
      (fun c t => (symbolIndex (newSymOfCaseAway tm c t)).val) caseU tapeU) symU [false] [])

theorem cellForcedU_eq (caseU tapeU digitU symU : List Bool) (c : TransitionCase tm)
    (t : TapeSlot k) (hclt : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hclt = c)
    (htlt : tapeU.length < (tapeList k).length)
    (ht : (tapeList k)[tapeU.length]'htlt = t) :
    (cellForcedU tm caseU tapeU digitU symU ≠ [])
      ↔ (symbolIndex (if digitU.length = 0 then newSymOfCaseZero tm c t
          else newSymOfCaseAway tm c t)).val = symU.length := by
  have h0 : (tableU2 (caseList tm) (tapeList k)
      (fun c t => (symbolIndex (newSymOfCaseZero tm c t)).val) caseU tapeU).length
      = (symbolIndex (newSymOfCaseZero tm c t)).val := by
    rw [tableU2_length _ _ _ _ _ hclt htlt, hc, ht]
  have h1 : (tableU2 (caseList tm) (tapeList k)
      (fun c t => (symbolIndex (newSymOfCaseAway tm c t)).val) caseU tapeU).length
      = (symbolIndex (newSymOfCaseAway tm c t)).val := by
    rw [tableU2_length _ _ _ _ _ hclt htlt, hc, ht]
  rw [cellForcedU]
  by_cases hd : digitU.length = 0
  · rw [ifEqLen_pos (by rw [hd]; rfl), if_pos hd]
    by_cases he : (symbolIndex (newSymOfCaseZero tm c t)).val = symU.length
    · rw [ifEqLen_pos (by rw [h0, he])]
      simp [he]
    · rw [ifEqLen_neg (by rw [h0]; exact he)]
      simp [he]
  · rw [ifEqLen_neg (by simpa using hd), if_neg hd]
    by_cases he : (symbolIndex (newSymOfCaseAway tm c t)).val = symU.length
    · rw [ifEqLen_pos (by rw [h1, he])]
      simp [he]
    · rw [ifEqLen_neg (by rw [h1]; exact he)]
      simp [he]

theorem cellForcedU_mem_FP {caseU tapeU digitU symU : List Bool → List Bool}
    (hcase : caseU ∈ FP) (htape : tapeU ∈ FP) (hd : digitU ∈ FP) (hsym : symU ∈ FP)
    {K : ℕ} (hK : ∀ z, (pair (caseU z) (tapeU z)).length ≤ K) :
    (fun z => cellForcedU tm (caseU z) (tapeU z) (digitU z) (symU z)) ∈ FP :=
  ifEqLen_mem_FP hd (constFn_mem_FP [])
    (ifEqLen_mem_FP (tableU2_mem_FP _ _ _ hcase htape hK) hsym
      (constFn_mem_FP _) (constFn_mem_FP _))
    (ifEqLen_mem_FP (tableU2_mem_FP _ _ _ hcase htape hK) hsym
      (constFn_mem_FP _) (constFn_mem_FP _))

/-- The direction a transition case moves a tape's head. -/
noncomputable def dirOfCase (c : TransitionCase tm) : TapeSlot k → Dir3
  | .input => (tm.δ c.choice c.state c.inputRead c.workRead c.outputRead).2.2.2.1
  | .work i => (tm.δ c.choice c.state c.inputRead c.workRead c.outputRead).2.2.2.2.1 i
  | .output => (tm.δ c.choice c.state c.inputRead c.workRead c.outputRead).2.2.2.2.2

theorem viewDir_eq_ofCase (V : StepView tm T) (t : TapeSlot k) :
    viewDir tm T V t = dirOfCase tm V.1 t := by
  cases t <;> rfl

/-- Where a transition case sends a head that sits at `p`. A halted case stays put. -/
noncomputable def newHeadOfCase (c : TransitionCase tm) (t : TapeSlot k) (p : ℕ) : ℕ :=
  if c.state = tm.qhalt then p else movedHeadPosition p (dirOfCase tm c t)

theorem newHeadV_eq_ofCase (V : StepView tm T) (t : TapeSlot k) :
    newHeadV tm T V t = newHeadOfCase tm V.1 t (V.2 t).val := by
  rw [newHeadV, newHeadOfCase, viewDir_eq_ofCase]

/-- The direction code of a case on a tape: `0` left, `1` stay, `2` right. -/
noncomputable def dirCodeOfCase (c : TransitionCase tm) (t : TapeSlot k) : ℕ :=
  if c.state = tm.qhalt then 1
  else
    match dirOfCase tm c t with
    | .left => 0
    | .stay => 1
    | .right => 2

theorem newHeadOfCase_eq_code (c : TransitionCase tm) (t : TapeSlot k) (p : ℕ) :
    newHeadOfCase tm c t p
      = if dirCodeOfCase tm c t = 0 then p - 1
        else if dirCodeOfCase tm c t = 1 then p else p + 1 := by
  rw [newHeadOfCase, dirCodeOfCase]
  by_cases hq : c.state = tm.qhalt
  · rw [if_pos hq, if_pos hq]
    simp
  · rw [if_neg hq, if_neg hq]
    cases hd : dirOfCase tm c t <;> simp [movedHeadPosition]

/-- Where a head goes, in unary, given the direction code. -/
noncomputable def movedU (codeU digitU : List Bool) : List Bool :=
  ifEqLen codeU [] (dropOne digitU)
    (ifEqLen codeU [false] digitU (digitU ++ [false]))

theorem movedU_length (codeU digitU : List Bool) :
    (movedU codeU digitU).length
      = if codeU.length = 0 then digitU.length - 1
        else if codeU.length = 1 then digitU.length else digitU.length + 1 := by
  rw [movedU]
  by_cases h0 : codeU.length = 0
  · rw [ifEqLen_pos (by rw [h0]; rfl), if_pos h0, dropOne, List.length_drop]
  · rw [ifEqLen_neg (by simpa using h0), if_neg h0]
    by_cases h1 : codeU.length = 1
    · rw [ifEqLen_pos (by rw [h1]; rfl), if_pos h1]
    · rw [ifEqLen_neg (by simpa using h1), if_neg h1, List.length_append]
      rfl

theorem movedU_mem_FP {codeU digitU : List Bool → List Bool} (hc : codeU ∈ FP)
    (hd : digitU ∈ FP) : (fun z => movedU (codeU z) (digitU z)) ∈ FP :=
  ifEqLen_mem_FP hc (constFn_mem_FP []) (dropOneFn_mem_FP hd)
    (ifEqLen_mem_FP hc (constFn_mem_FP [false]) hd
      (Cobham.appendFn_mem_FP hd (constFn_mem_FP [false])))

/-- The bit a transition case forces on a head atom. -/
noncomputable def headForcedU (caseU tapeU digitU posU : List Bool) : List Bool :=
  ifEqLen (movedU (tableU2 (caseList tm) (tapeList k) (fun c t => dirCodeOfCase tm c t)
    caseU tapeU) digitU) posU [false] []

/-- **Whether the head atom an index names is where the view sends the head.** -/
theorem headForcedU_eq (caseU tapeU digitU posU : List Bool) (c : TransitionCase tm)
    (t : TapeSlot k) (hclt : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hclt = c)
    (htlt : tapeU.length < (tapeList k).length)
    (ht : (tapeList k)[tapeU.length]'htlt = t) :
    (headForcedU tm caseU tapeU digitU posU ≠ [])
      ↔ newHeadOfCase tm c t digitU.length = posU.length := by
  have hcode : (tableU2 (caseList tm) (tapeList k) (fun c t => dirCodeOfCase tm c t)
      caseU tapeU).length = dirCodeOfCase tm c t := by
    rw [tableU2_length _ _ _ _ _ hclt htlt, hc, ht]
  have hmv : (movedU (tableU2 (caseList tm) (tapeList k) (fun c t => dirCodeOfCase tm c t)
      caseU tapeU) digitU).length = newHeadOfCase tm c t digitU.length := by
    rw [movedU_length, hcode, newHeadOfCase_eq_code]
  rw [headForcedU]
  by_cases h : newHeadOfCase tm c t digitU.length = posU.length
  · rw [ifEqLen_pos (by rw [hmv]; exact h)]
    simp [h]
  · rw [ifEqLen_neg (by rw [hmv]; exact h)]
    simp [h]

theorem headForcedU_mem_FP {caseU tapeU digitU posU : List Bool → List Bool}
    (hcase : caseU ∈ FP) (htape : tapeU ∈ FP) (hd : digitU ∈ FP) (hpos : posU ∈ FP)
    {K : ℕ} (hK : ∀ z, (pair (caseU z) (tapeU z)).length ≤ K) :
    (fun z => headForcedU tm (caseU z) (tapeU z) (digitU z) (posU z)) ∈ FP :=
  ifEqLen_mem_FP (movedU_mem_FP (tableU2_mem_FP _ _ _ hcase htape hK) hd) hpos
    (constFn_mem_FP _) (constFn_mem_FP _)

/-- The value a view forces on the atom an index names, as a flag. -/
noncomputable def atomForcedU (caseU qU horU tapesU viewU aU : List Bool) : List Bool :=
  ifLtLen aU qU (stateForcedU tm caseU aU)
    (ifLtLen (atRest qU aU) (mulLen tapesU horU)
      (headForcedU tm caseU (atHeadTape qU horU aU)
        (headDigitU horU (atHeadTape qU horU aU) viewU) (atHeadPos qU horU aU))
      (cellForcedU tm caseU (atCellTape qU horU tapesU aU)
        (headDigitU horU (atCellTape qU horU tapesU aU) viewU)
        (atCellSym qU horU tapesU aU)))

private theorem symbolIndex_val_inj {a b : Γ}
    (h : (symbolIndex a).val = (symbolIndex b).val) : a = b := by
  cases a <;> cases b <;> simp_all [symbolIndex]

theorem stateIndex_inj {q q' : tm.Q} (h : stateIndex tm q = stateIndex tm q') : q = q' :=
  (Fintype.equivFin tm.Q).injective (Fin.ext h)

/-- **The bit forced on a state atom.** -/
theorem atomForcedU_state_eq (caseU qU horU tapesU viewU aU : List Bool)
    (c : TransitionCase tm) (q : tm.Q)
    (hclt : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hclt = c)
    (hq : qU.length = Fintype.card tm.Q) (ha : aU.length = stateIndex tm q) :
    (atomForcedU tm caseU qU horU tapesU viewU aU ≠ [])
      ↔ newStateOfCase tm c = q := by
  rw [atomForcedU, ifLtLen_pos (by rw [ha, hq]; exact (Fintype.equivFin tm.Q q).isLt),
    stateForcedU_eq tm caseU aU c hclt hc, ha]
  constructor
  · exact fun h => stateIndex_inj tm h
  · exact fun h => by rw [h]

/-- **The bit forced on a head atom.** -/
theorem atomForcedU_head_eq (caseU qU horU tapesU viewU aU : List Bool)
    (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (tape : TapeSlot k)
    (p : Fin (T + 1)) (hclt : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hclt = c)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (htapes : tapesU.length = k + 2) (hview : viewU.length = i.val)
    (ha : aU.length = Fintype.card tm.Q + (tape.index.val * (T + 1) + p.val)) :
    (atomForcedU tm caseU qU horU tapesU viewU aU ≠ [])
      ↔ newHeadV tm T (c, headTupleOf k T i) tape = p.val := by
  have hrest : (atRest qU aU).length = tape.index.val * (T + 1) + p.val := by
    rw [atRest, List.length_drop, ha, hq]
    omega
  have hblk : tape.index.val * (T + 1) + p.val < (k + 2) * (T + 1) := by
    have h1 : (tape.index.val + 1) * (T + 1) ≤ (k + 2) * (T + 1) :=
      Nat.mul_le_mul_right _ tape.index.isLt
    have h2 : (tape.index.val + 1) * (T + 1) = tape.index.val * (T + 1) + (T + 1) := by ring
    have := p.isLt
    omega
  have htp : (atHeadTape qU horU aU).length = tape.index.val := by
    rw [atHeadTape, divFn2_eq (by rw [hhor]; omega), List.length_replicate, hrest, hhor]
    have h2 : tape.index.val * (T + 1) + p.val = (T + 1) * tape.index.val + p.val := by ring
    rw [h2, Nat.mul_add_div (by omega), Nat.div_eq_of_lt p.isLt]
    omega
  have hpp : (atHeadPos qU horU aU).length = p.val := by
    rw [atHeadPos, modFn2_eq (by rw [hhor]; omega), List.length_replicate, hrest, hhor]
    have h2 : tape.index.val * (T + 1) + p.val = (T + 1) * tape.index.val + p.val := by ring
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
  have hdig : (headDigitU horU (atHeadTape qU horU aU) viewU).length
      = (headTupleOf k T i tape).val :=
    headDigitU_eq_headTupleOf horU _ viewU i tape hhor
      (by rw [htp, tapeSlotEquiv_apply]) hview
  have hsomeH : (tapeList k)[(atHeadTape qU horU aU).length]? = some tape := by
    rw [htp, tapeList_getElem? _ tape.index.isLt]
    congr 1
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simp [tapeSlotEquiv_apply])
  rw [atomForcedU, ifLtLen_neg (by rw [ha, hq]; omega),
    ifLtLen_pos (by rw [hrest, length_mulLen, htapes, hhor]; exact hblk),
    headForcedU_eq tm caseU _ _ _ c tape hclt hc
      (by rw [htp, tapeList_length]; exact tape.index.isLt)
      (by
        have h := hsomeH
        rw [List.getElem?_eq_getElem
          (by rw [htp, tapeList_length]; exact tape.index.isLt)] at h
        exact Option.some.inj h),
    hdig, hpp, newHeadV_eq_ofCase]

/-- **The bit forced on a cell atom.** -/
theorem atomForcedU_cell_eq (caseU qU horU tapesU viewU aU : List Bool)
    (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (tape : TapeSlot k) (sym : Γ)
    (hclt : caseU.length < (caseList tm).length)
    (hc : (caseList tm)[caseU.length]'hclt = c)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (htapes : tapesU.length = k + 2) (hview : viewU.length = i.val)
    (ha : aU.length = Fintype.card tm.Q + (k + 2) * (T + 1)
      + (tape.index.val * 4 + (symbolIndex sym).val)) :
    (atomForcedU tm caseU qU horU tapesU viewU aU ≠ [])
      ↔ newSymV tm T (c, headTupleOf k T i) tape = sym := by
  have hrest : (atRest qU aU).length
      = (k + 2) * (T + 1) + (tape.index.val * 4 + (symbolIndex sym).val) := by
    rw [atRest, List.length_drop, ha, hq]
    omega
  have hrest2 : (atRest2 qU horU tapesU aU).length
      = tape.index.val * 4 + (symbolIndex sym).val := by
    rw [atRest2, List.length_drop, hrest, length_mulLen, htapes, hhor]
    omega
  have htp : (atCellTape qU horU tapesU aU).length = tape.index.val := by
    rw [atCellTape, divC_eq (by norm_num), List.length_replicate, hrest2]
    have h2 : tape.index.val * 4 + (symbolIndex sym).val
        = 4 * tape.index.val + (symbolIndex sym).val := by ring
    rw [h2, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt (symbolIndex sym).isLt]
    omega
  have hsy : (atCellSym qU horU tapesU aU).length = (symbolIndex sym).val := by
    rw [atCellSym, modC_eq (by norm_num), List.length_replicate, hrest2]
    have h2 : tape.index.val * 4 + (symbolIndex sym).val
        = 4 * tape.index.val + (symbolIndex sym).val := by ring
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (symbolIndex sym).isLt]
  have hdig : (headDigitU horU (atCellTape qU horU tapesU aU) viewU).length
      = (headTupleOf k T i tape).val :=
    headDigitU_eq_headTupleOf horU _ viewU i tape hhor
      (by rw [htp, tapeSlotEquiv_apply]) hview
  have hsomeC : (tapeList k)[(atCellTape qU horU tapesU aU).length]? = some tape := by
    rw [htp, tapeList_getElem? _ tape.index.isLt]
    congr 1
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by simp [tapeSlotEquiv_apply])
  rw [atomForcedU, ifLtLen_neg (by rw [ha, hq]; omega),
    ifLtLen_neg (by rw [hrest, length_mulLen, htapes, hhor]; omega),
    cellForcedU_eq tm caseU _ _ _ c tape hclt hc
      (by rw [htp, tapeList_length]; exact tape.index.isLt)
      (by
        have h := hsomeC
        rw [List.getElem?_eq_getElem
          (by rw [htp, tapeList_length]; exact tape.index.isLt)] at h
        exact Option.some.inj h),
    hdig, hsy, newSymV_eq_ofCase]
  constructor
  · exact fun h => symbolIndex_val_inj h
  · exact fun h => by rw [h]

theorem atomForcedU_mem_FP {caseU qU horU tapesU viewU aU : List Bool → List Bool}
    (hcase : caseU ∈ FP) (hq : qU ∈ FP) (hhor : horU ∈ FP) (ht : tapesU ∈ FP)
    (hview : viewU ∈ FP) (ha : aU ∈ FP)
    {C : ℕ} (hC : ∀ z, (caseU z).length ≤ C)
    {K₁ : ℕ} (hK₁ : ∀ z, (pair (caseU z) (atHeadTape (qU z) (horU z) (aU z))).length ≤ K₁)
    {K₂ : ℕ} (hK₂ : ∀ z,
      (pair (caseU z) (atCellTape (qU z) (horU z) (tapesU z) (aU z))).length ≤ K₂)
    {E : ℕ} (hE₁ : ∀ z, (atHeadTape (qU z) (horU z) (aU z)).length ≤ E)
    (hE₂ : ∀ z, (atCellTape (qU z) (horU z) (tapesU z) (aU z)).length ≤ E)
    {width : List Bool → List Bool} (hwd : width ∈ FP)
    (hbound : ∀ z, (horU z).length ^ E + 2 * (horU z).length + 4 ≤ (width z).length) :
    (fun z => atomForcedU tm (caseU z) (qU z) (horU z) (tapesU z) (viewU z) (aU z)) ∈ FP := by
  have hht := atHeadTape_mem_FP hq hhor ha
  have hct := atCellTape_mem_FP hq hhor ht ha
  exact ifLtLen_mem_FP ha hq (stateForcedU_mem_FP tm hcase ha hC)
    (ifLtLen_mem_FP (atRest_mem_FP hq ha) (mulLen_mem_FP ht hhor)
      (headForcedU_mem_FP tm hcase hht
        (headDigitU_mem_FP hhor hht hview E hE₁ hwd hbound)
        (atHeadPos_mem_FP hq hhor ha) hK₁)
      (cellForcedU_mem_FP tm hcase hct
        (headDigitU_mem_FP hhor hct hview E hE₂ hwd hbound)
        (atCellSym_mem_FP hq hhor ht ha) hK₂))

/-! ## The step clauses of a base family -/

/-- One step clause, encoded from its index: a view's clause (supplied already encoded), or a
frame clause. -/
noncomputable def stepIdxEnc (viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU
    blkPosU pU : List Bool) : List Bool :=
  ifLtLen pU (mulLen viewsU scvU) viewEnc
    (frameIdxEnc w uU vU qU hdU horU hor2U blkTU blkPU blkPosU
      (pU.drop (mulLen viewsU scvU).length))

theorem stepIdxEnc_view_eq (viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU
    blkPosU pU : List Bool) (hlt : pU.length < (mulLen viewsU scvU).length) :
    stepIdxEnc viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU blkPosU pU
      = viewEnc := by
  rw [stepIdxEnc, ifLtLen_pos hlt]

theorem stepIdxEnc_frame_eq (viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU
    blkPosU pU : List Bool) (hge : (mulLen viewsU scvU).length ≤ pU.length) :
    stepIdxEnc viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU blkPosU pU
      = frameIdxEnc w uU vU qU hdU horU hor2U blkTU blkPU blkPosU
          (pU.drop (mulLen viewsU scvU).length) := by
  rw [stepIdxEnc, ifLtLen_neg (by omega)]

theorem stepIdxEnc_mem_FP
    {viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU blkPosU pU
      : List Bool → List Bool}
    (hve : viewEnc ∈ FP) (hw : w ∈ FP) (hu : uU ∈ FP) (hv : vU ∈ FP) (hq : qU ∈ FP)
    (hhd : hdU ∈ FP) (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP) (hviews : viewsU ∈ FP)
    (hscv : scvU ∈ FP) (hb : blkTU ∈ FP) (hbp : blkPU ∈ FP) (hbs : blkPosU ∈ FP)
    (hp : pU ∈ FP) :
    (fun z => stepIdxEnc (viewEnc z) (w z) (uU z) (vU z) (qU z) (hdU z) (horU z) (hor2U z)
      (viewsU z) (scvU z) (blkTU z) (blkPU z) (blkPosU z) (pU z)) ∈ FP :=
  ifLtLen_mem_FP hp (mulLen_mem_FP hviews hscv) hve
    (frameIdxEnc_mem_FP hw hu hv hq hhd hhor hhor2 hb hbp hbs
      (dropLenFn_mem_FP (mulLen_mem_FP hviews hscv) hp))

/-- **A step clause in the view region, encoded.** -/
theorem stepIdxEnc_view_value (viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU
    blkPosU : List Bool) (u v s p : ℕ) (V : StepView tm T)
    (hviews : viewsU.length = (viewList tm T).length)
    (hscv : scvU.length = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hpos : 0 < scvU.length) (hp : p < viewsU.length * scvU.length)
    (hV : (viewList tm T)[p / scvU.length]? = some V)
    (hval : ((stepClausesView tm T u v s V)[p % scvU.length]?).map
      DataEncode.bitstringEncode = some viewEnc) :
    ((stepClauses tm T u v s)[p]?).map DataEncode.bitstringEncode
      = some (stepIdxEnc viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU blkPosU
          (List.replicate p true)) := by
  rw [stepIdxEnc_view_eq viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU blkPosU
      (List.replicate p true)
      (by rw [List.length_replicate, length_mulLen]; exact hp),
    stepClauses_getElem?_view tm T u v s p (by omega) (by rw [← hscv, ← hviews]; exact hp),
    ← hscv, hV, Option.bind_some, hval]

/-- **A step clause in the frame region, encoded.** -/
theorem stepIdxEnc_frame_value (viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU
    blkPosU : List Bool) (u v p : ℕ)
    (hviews : viewsU.length = (viewList tm T).length)
    (hscv : scvU.length = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hp : viewsU.length * scvU.length ≤ p) (s : ℕ)
    (hframe : ((frameClauses tm T u v)[p - viewsU.length * scvU.length]?).map
        DataEncode.bitstringEncode
      = some (frameIdxEnc w uU vU qU hdU horU hor2U blkTU blkPU blkPosU
          (List.replicate (p - viewsU.length * scvU.length) true))) :
    ((stepClauses tm T u v s)[p]?).map DataEncode.bitstringEncode
      = some (stepIdxEnc viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU blkPosU
          (List.replicate p true)) := by
  rw [stepIdxEnc_frame_eq viewEnc w uU vU qU hdU horU hor2U viewsU scvU blkTU blkPU blkPosU
      (List.replicate p true)
      (by rw [List.length_replicate, length_mulLen]; exact hp),
    length_mulLen, List.drop_replicate,
    stepClauses_getElem?_frame tm T u v s p (by rw [← hscv, ← hviews]; exact hp),
    ← hscv, ← hviews]
  exact hframe

/-! ## The base family -/

/-- One base clause, encoded from its index: block equality guarded by the selector being
false, or a step clause (supplied already encoded) guarded by it being true. -/
noncomputable def baseEnc (stepEnc w uU vU s1U w2U pU : List Bool) : List Bool :=
  ifLtLen pU w2U
    (consLitEnc w [] s1U (eqClauseEnc w uU vU pU))
    (consLitEnc w [true] s1U stepEnc)

theorem baseEnc_eq_eq (stepEnc w uU vU s1U w2U pU : List Bool)
    (hlt : pU.length < w2U.length) :
    baseEnc stepEnc w uU vU s1U w2U pU
      = consLitEnc w [] s1U (eqClauseEnc w uU vU pU) := by
  rw [baseEnc, ifLtLen_pos hlt]

theorem baseEnc_step_eq (stepEnc w uU vU s1U w2U pU : List Bool)
    (hge : w2U.length ≤ pU.length) :
    baseEnc stepEnc w uU vU s1U w2U pU = consLitEnc w [true] s1U stepEnc := by
  rw [baseEnc, ifLtLen_neg (by omega)]

theorem baseEnc_mem_FP {stepEnc w uU vU s1U w2U pU : List Bool → List Bool}
    (hse : stepEnc ∈ FP) (hw : w ∈ FP) (hu : uU ∈ FP) (hv : vU ∈ FP) (hs1 : s1U ∈ FP)
    (hw2 : w2U ∈ FP) (hp : pU ∈ FP) :
    (fun z => baseEnc (stepEnc z) (w z) (uU z) (vU z) (s1U z) (w2U z) (pU z)) ∈ FP :=
  ifLtLen_mem_FP hp hw2
    (consLitEnc_mem_FP hw (constFn_mem_FP []) hs1 (eqClauseEnc_mem_FP hw hu hv hp))
    (consLitEnc_mem_FP hw (constFn_mem_FP [true]) hs1 hse)

/-! ## The outer dispatch -/

/-- The offset of a block inside level `j`: the first level's start, plus `j` whole levels,
plus the block's offset inside a level. -/
noncomputable def levOffU (baseOffU levSizeU jU cOffU : List Bool) : List Bool :=
  baseOffU ++ (mulLen levSizeU jU ++ cOffU)

@[simp] theorem levOffU_length (baseOffU levSizeU jU cOffU : List Bool) :
    (levOffU baseOffU levSizeU jU cOffU).length
      = baseOffU.length + (levSizeU.length * jU.length + cOffU.length) := by
  rw [levOffU, List.length_append, List.length_append, length_mulLen]

theorem levOffU_mem_FP {baseOffU levSizeU jU cOffU : List Bool → List Bool}
    (hb : baseOffU ∈ FP) (hl : levSizeU ∈ FP) (hj : jU ∈ FP) (hc : cOffU ∈ FP) :
    (fun z => levOffU (baseOffU z) (levSizeU z) (jU z) (cOffU z)) ∈ FP :=
  Cobham.appendFn_mem_FP hb (Cobham.appendFn_mem_FP (mulLen_mem_FP hl hj) hc)

/-- The level a matrix index falls in. -/
noncomputable def levOfIdx (gcU lcU pU : List Bool) : List Bool :=
  divFn2 (pair lcU (pU.drop gcU.length))

/-- Where inside its level a matrix index falls. -/
noncomputable def offInLevel (gcU lcU pU : List Bool) : List Bool :=
  modFn2 (pair lcU (pU.drop gcU.length))

theorem levOfIdx_mem_FP {gcU lcU pU : List Bool → List Bool} (hg : gcU ∈ FP)
    (hl : lcU ∈ FP) (hp : pU ∈ FP) :
    (fun z => levOfIdx (gcU z) (lcU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hl (dropLenFn_mem_FP hg hp))
    divFn2_mem_FP) fun _ => rfl

theorem offInLevel_mem_FP {gcU lcU pU : List Bool → List Bool} (hg : gcU ∈ FP)
    (hl : lcU ∈ FP) (hp : pU ∈ FP) :
    (fun z => offInLevel (gcU z) (lcU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hl (dropLenFn_mem_FP hg hp))
    modFn2_mem_FP) fun _ => rfl

/-- One clause of the whole matrix, encoded: a guard, a level clause, or a base clause. The
guard and base clauses are supplied already encoded. -/
noncomputable def matrixEnc (guardEnc baseClauseEnc levelClauseEnc w gcU lcU nU yLastU
    pU : List Bool) : List Bool :=
  ifLtLen pU gcU guardEnc
    (ifLtLen (pU.drop gcU.length) (mulLen lcU nU) levelClauseEnc
      (consLitEnc w [] yLastU baseClauseEnc))

theorem matrixEnc_mem_FP
    {guardEnc baseClauseEnc levelClauseEnc w gcU lcU nU yLastU pU : List Bool → List Bool}
    (hg : guardEnc ∈ FP) (hbc : baseClauseEnc ∈ FP) (hlc : levelClauseEnc ∈ FP)
    (hw : w ∈ FP) (hgc : gcU ∈ FP) (hlcU : lcU ∈ FP) (hn : nU ∈ FP) (hy : yLastU ∈ FP)
    (hp : pU ∈ FP) :
    (fun z => matrixEnc (guardEnc z) (baseClauseEnc z) (levelClauseEnc z) (w z) (gcU z)
      (lcU z) (nU z) (yLastU z) (pU z)) ∈ FP :=
  ifLtLen_mem_FP hp hgc hg
    (ifLtLen_mem_FP (dropLenFn_mem_FP hgc hp) (mulLen_mem_FP hlcU hn) hlc
      (consLitEnc_mem_FP hw (constFn_mem_FP []) hy hbc))

theorem matrixEnc_guard_eq (guardEnc baseClauseEnc levelClauseEnc w gcU lcU nU yLastU
    : List Bool) (p : ℕ) (hp : p < gcU.length) :
    matrixEnc guardEnc baseClauseEnc levelClauseEnc w gcU lcU nU yLastU
        (List.replicate p true) = guardEnc := by
  rw [matrixEnc, ifLtLen_pos (by rw [List.length_replicate]; exact hp)]

theorem matrixEnc_level_eq (guardEnc baseClauseEnc levelClauseEnc w gcU lcU nU yLastU
    : List Bool) (p : ℕ) (h₁ : gcU.length ≤ p)
    (h₂ : p < gcU.length + lcU.length * nU.length) :
    matrixEnc guardEnc baseClauseEnc levelClauseEnc w gcU lcU nU yLastU
        (List.replicate p true) = levelClauseEnc := by
  rw [matrixEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_pos (by rw [List.length_drop, List.length_replicate, length_mulLen]; omega)]

theorem matrixEnc_base_eq (guardEnc baseClauseEnc levelClauseEnc w gcU lcU nU yLastU
    : List Bool) (p : ℕ) (hp : gcU.length + lcU.length * nU.length ≤ p) :
    matrixEnc guardEnc baseClauseEnc levelClauseEnc w gcU lcU nU yLastU
        (List.replicate p true) = consLitEnc w [] yLastU baseClauseEnc := by
  rw [matrixEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate, length_mulLen]; omega)]

/-! ## Decoding a block's wire index -/

/-- What is left of a wire index after the state segment. -/
noncomputable def wiRest (qU pU : List Bool) : List Bool := pU.drop qU.length

/-- The tape of a head wire. -/
noncomputable def wiHeadTape (qU horU pU : List Bool) : List Bool :=
  divFn2 (pair horU (wiRest qU pU))

/-- The position of a head wire. -/
noncomputable def wiHeadPos (qU horU pU : List Bool) : List Bool :=
  modFn2 (pair horU (wiRest qU pU))

/-- What is left of a wire index after the head segment. -/
noncomputable def wiRest2 (qU horU tapesU pU : List Bool) : List Bool :=
  (wiRest qU pU).drop (mulLen tapesU horU).length

/-- The symbol of a cell wire. -/
noncomputable def wiCellSym (qU horU tapesU pU : List Bool) : List Bool :=
  modC 4 (wiRest2 qU horU tapesU pU)

/-- The tape-and-position part of a cell wire. -/
noncomputable def wiCellRest (qU horU tapesU pU : List Bool) : List Bool :=
  divC 4 (wiRest2 qU horU tapesU pU)

/-- The tape of a cell wire. -/
noncomputable def wiCellTape (qU horU hor2U tapesU pU : List Bool) : List Bool :=
  divFn2 (pair hor2U (wiCellRest qU horU tapesU pU))

/-- The position of a cell wire. -/
noncomputable def wiCellPos (qU horU hor2U tapesU pU : List Bool) : List Bool :=
  modFn2 (pair hor2U (wiCellRest qU horU tapesU pU))

theorem wiRest_mem_FP {qU pU : List Bool → List Bool} (hq : qU ∈ FP) (hp : pU ∈ FP) :
    (fun z => wiRest (qU z) (pU z)) ∈ FP := dropLenFn_mem_FP hq hp

theorem wiHeadTape_mem_FP {qU horU pU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (hp : pU ∈ FP) :
    (fun z => wiHeadTape (qU z) (horU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hhor (wiRest_mem_FP hq hp))
    divFn2_mem_FP) fun _ => rfl

theorem wiHeadPos_mem_FP {qU horU pU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (hp : pU ∈ FP) :
    (fun z => wiHeadPos (qU z) (horU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hhor (wiRest_mem_FP hq hp))
    modFn2_mem_FP) fun _ => rfl

theorem wiRest2_mem_FP {qU horU tapesU pU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (ht : tapesU ∈ FP) (hp : pU ∈ FP) :
    (fun z => wiRest2 (qU z) (horU z) (tapesU z) (pU z)) ∈ FP :=
  dropLenFn_mem_FP (mulLen_mem_FP ht hhor) (wiRest_mem_FP hq hp)

theorem wiCellSym_mem_FP {qU horU tapesU pU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (ht : tapesU ∈ FP) (hp : pU ∈ FP) :
    (fun z => wiCellSym (qU z) (horU z) (tapesU z) (pU z)) ∈ FP :=
  modC_mem_FP (wiRest2_mem_FP hq hhor ht hp) 4

theorem wiCellRest_mem_FP {qU horU tapesU pU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (ht : tapesU ∈ FP) (hp : pU ∈ FP) :
    (fun z => wiCellRest (qU z) (horU z) (tapesU z) (pU z)) ∈ FP :=
  divC_mem_FP (wiRest2_mem_FP hq hhor ht hp) 4

theorem wiCellTape_mem_FP {qU horU hor2U tapesU pU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP) (ht : tapesU ∈ FP) (hp : pU ∈ FP) :
    (fun z => wiCellTape (qU z) (horU z) (hor2U z) (tapesU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hhor2 (wiCellRest_mem_FP hq hhor ht hp))
    divFn2_mem_FP) fun _ => rfl

theorem wiCellPos_mem_FP {qU horU hor2U tapesU pU : List Bool → List Bool} (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP) (ht : tapesU ∈ FP) (hp : pU ∈ FP) :
    (fun z => wiCellPos (qU z) (horU z) (hor2U z) (tapesU z) (pU z)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hhor2 (wiCellRest_mem_FP hq hhor ht hp))
    modFn2_mem_FP) fun _ => rfl

/-! ## The initial block -/

/-- The index of the symbol the initial configuration holds at a cell. -/
noncomputable def initSymIdxU (x tapeU posU : List Bool) : List Bool :=
  ifEqLen tapeU [] (symStartInput x posU)
    (ifEqLen posU [] [false, false, false] [false, false])

theorem initSymIdxU_mem_FP {x tapeU posU : List Bool → List Bool} (hx : x ∈ FP)
    (ht : tapeU ∈ FP) (hp : posU ∈ FP) :
    (fun z => initSymIdxU (x z) (tapeU z) (posU z)) ∈ FP :=
  ifEqLen_mem_FP ht (constFn_mem_FP []) (symStartInput_mem_FP hx hp)
    (ifEqLen_mem_FP hp (constFn_mem_FP []) (constFn_mem_FP _) (constFn_mem_FP _))

/-- Whether the initial block holds a `1` on a wire. -/
noncomputable def initBitU (qU horU hor2U tapesU qstartU x pU : List Bool) : List Bool :=
  ifLtLen pU qU
    (ifEqLen pU qstartU [false] [])
    (ifLtLen (wiRest qU pU) (mulLen tapesU horU)
      (ifEqLen (wiHeadPos qU horU pU) [] [false] [])
      (ifEqLen (initSymIdxU x (wiCellTape qU horU hor2U tapesU pU)
          (wiCellPos qU horU hor2U tapesU pU)) (wiCellSym qU horU tapesU pU)
        [false] []))

theorem initBitU_mem_FP {qU horU hor2U tapesU qstartU x pU : List Bool → List Bool}
    (hq : qU ∈ FP) (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP) (ht : tapesU ∈ FP)
    (hqs : qstartU ∈ FP) (hx : x ∈ FP) (hp : pU ∈ FP) :
    (fun z => initBitU (qU z) (horU z) (hor2U z) (tapesU z) (qstartU z) (x z) (pU z))
      ∈ FP :=
  ifLtLen_mem_FP hp hq
    (ifEqLen_mem_FP hp hqs (constFn_mem_FP _) (constFn_mem_FP _))
    (ifLtLen_mem_FP (wiRest_mem_FP hq hp) (mulLen_mem_FP ht hhor)
      (ifEqLen_mem_FP (wiHeadPos_mem_FP hq hhor hp) (constFn_mem_FP [])
        (constFn_mem_FP _) (constFn_mem_FP _))
      (ifEqLen_mem_FP
        (initSymIdxU_mem_FP hx (wiCellTape_mem_FP hq hhor hhor2 ht hp)
          (wiCellPos_mem_FP hq hhor hhor2 ht hp))
        (wiCellSym_mem_FP hq hhor ht hp) (constFn_mem_FP _) (constFn_mem_FP _)))

/-! ## The lengths a wire index decodes to -/

theorem wiRest_length (qU pU : List Bool) :
    (wiRest qU pU).length = pU.length - qU.length := by
  rw [wiRest, List.length_drop]

theorem wiHeadTape_length (qU horU pU : List Bool) (hhor : 0 < horU.length) :
    (wiHeadTape qU horU pU).length = (pU.length - qU.length) / horU.length := by
  rw [wiHeadTape, divFn2_eq hhor, List.length_replicate, wiRest_length]

theorem wiHeadPos_length (qU horU pU : List Bool) (hhor : 0 < horU.length) :
    (wiHeadPos qU horU pU).length = (pU.length - qU.length) % horU.length := by
  rw [wiHeadPos, modFn2_eq hhor, List.length_replicate, wiRest_length]

theorem wiRest2_length (qU horU tapesU pU : List Bool) :
    (wiRest2 qU horU tapesU pU).length
      = pU.length - qU.length - tapesU.length * horU.length := by
  rw [wiRest2, List.length_drop, wiRest_length, length_mulLen]

theorem wiCellSym_length (qU horU tapesU pU : List Bool) :
    (wiCellSym qU horU tapesU pU).length
      = (pU.length - qU.length - tapesU.length * horU.length) % 4 := by
  rw [wiCellSym, modC_eq (by norm_num), List.length_replicate, wiRest2_length]

theorem wiCellRest_length (qU horU tapesU pU : List Bool) :
    (wiCellRest qU horU tapesU pU).length
      = (pU.length - qU.length - tapesU.length * horU.length) / 4 := by
  rw [wiCellRest, divC_eq (by norm_num), List.length_replicate, wiRest2_length]

theorem wiCellTape_length (qU horU hor2U tapesU pU : List Bool) (hhor2 : 0 < hor2U.length) :
    (wiCellTape qU horU hor2U tapesU pU).length
      = (pU.length - qU.length - tapesU.length * horU.length) / 4 / hor2U.length := by
  rw [wiCellTape, divFn2_eq hhor2, List.length_replicate, wiCellRest_length]

theorem wiCellPos_length (qU horU hor2U tapesU pU : List Bool) (hhor2 : 0 < hor2U.length) :
    (wiCellPos qU horU hor2U tapesU pU).length
      = (pU.length - qU.length - tapesU.length * horU.length) / 4 % hor2U.length := by
  rw [wiCellPos, modFn2_eq hhor2, List.length_replicate, wiCellRest_length]

/-! ## What the initial-block bit says -/

theorem initBitU_state_length (qU horU hor2U tapesU qstartU x : List Bool) (q : tm.Q)
    (hq : qU.length = Fintype.card tm.Q)
    (hqstart : qstartU.length = stateIndex tm tm.qstart) :
    (initBitU qU horU hor2U tapesU qstartU x
        (List.replicate (configIndex tm T (ConfigAtom.state q)) true)).length
      = if ConfigAtom.value (Cfg.init tm.qstart x) (ConfigAtom.state q : ConfigAtom tm T)
        then 1 else 0 := by
  have hlen : (List.replicate (configIndex tm T (ConfigAtom.state q)) true).length
      = stateIndex tm q := by rw [List.length_replicate, configIndex_state]
  have hlt : (List.replicate (configIndex tm T (ConfigAtom.state q)) true).length
      < qU.length := by
    rw [hlen, hq, stateIndex]
    exact (Fintype.equivFin tm.Q q).isLt
  rw [initBitU, ifLtLen_pos hlt, ConfigAtom.value]
  by_cases h : tm.qstart = q
  · rw [ifEqLen_pos (by rw [hlen, hqstart, h]), if_pos (by simp [h])]
    rfl
  · rw [ifEqLen_neg (by
      rw [hlen, hqstart]
      intro hcontra
      exact h ((Fintype.equivFin tm.Q).injective (Fin.ext hcontra.symm))),
      if_neg (by simp [h])]
    rfl

theorem get_init_head (t : TapeSlot k) (qs : tm.Q) (x : List Bool) :
    (t.get (Cfg.init qs x)).head = 0 := by
  cases t <;> rfl

theorem get_init_cells (t : TapeSlot k) (qs : tm.Q) (x : List Bool) (n : ℕ) :
    (t.get (Cfg.init qs x)).cells n
      = if t.index.val = 0 then (Tape.init (x.map Γ.ofBool)).cells n
        else (Tape.init []).cells n := by
  cases t with
  | input => rfl
  | work i => rw [if_neg (by simp [TapeSlot.index])]; rfl
  | output => rw [if_neg (by simp [TapeSlot.index])]; rfl

theorem initBitU_head_length (qU horU hor2U tapesU qstartU x : List Bool)
    (t : TapeSlot k) (p : Fin (T + 1))
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (htapes : tapesU.length = k + 2) :
    (initBitU qU horU hor2U tapesU qstartU x
        (List.replicate (configIndex tm T (ConfigAtom.head t p)) true)).length
      = if ConfigAtom.value (Cfg.init tm.qstart x) (ConfigAtom.head t p : ConfigAtom tm T)
        then 1 else 0 := by
  set pU := List.replicate (configIndex tm T (ConfigAtom.head t p)) true with hpU
  have hlen : pU.length = Fintype.card tm.Q + t.index.val * (T + 1) + p.val := by
    rw [hpU, List.length_replicate, configIndex_head]
  have hnlt : ¬ pU.length < qU.length := by rw [hlen, hq]; omega
  have hblk : t.index.val * (T + 1) + p.val < (k + 2) * (T + 1) := by
    have h1 : (t.index.val + 1) * (T + 1) ≤ (k + 2) * (T + 1) :=
      Nat.mul_le_mul_right _ t.index.isLt
    have h2 : (t.index.val + 1) * (T + 1) = t.index.val * (T + 1) + (T + 1) := by ring
    have := p.isLt
    omega
  have hrest : (wiRest qU pU).length < (mulLen tapesU horU).length := by
    rw [wiRest_length, length_mulLen, hlen, hq, htapes, hhor]
    omega
  have hpos : (wiHeadPos qU horU pU).length = p.val := by
    rw [wiHeadPos_length _ _ _ (by rw [hhor]; omega), hlen, hq, hhor]
    have h1 : Fintype.card tm.Q + t.index.val * (T + 1) + p.val - Fintype.card tm.Q
        = (T + 1) * t.index.val + p.val := by rw [Nat.mul_comm]; omega
    rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]
  rw [initBitU, ifLtLen_neg (by omega), ifLtLen_pos hrest, ConfigAtom.value,
    get_init_head]
  by_cases h : p.val = 0
  · rw [ifEqLen_pos (by rw [hpos, h]; rfl), if_pos (by simp [h])]
    rfl
  · rw [ifEqLen_neg (by rw [hpos]; simpa using h), if_neg (by simp [Ne.symm h])]
    rfl

theorem initBitU_cell_length (qU horU hor2U tapesU qstartU x : List Bool)
    (t : TapeSlot k) (pos : Fin (T + 2)) (sym : Γ)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (hhor2 : hor2U.length = T + 2) (htapes : tapesU.length = k + 2) :
    (initBitU qU horU hor2U tapesU qstartU x
        (List.replicate (configIndex tm T (ConfigAtom.cell t pos sym)) true)).length
      = if ConfigAtom.value (Cfg.init tm.qstart x)
          (ConfigAtom.cell t pos sym : ConfigAtom tm T) then 1 else 0 := by
  set pU := List.replicate (configIndex tm T (ConfigAtom.cell t pos sym)) true with hpU
  set A : ℕ := (t.index.val * (T + 2) + pos.val) * 4 + (symbolIndex sym).val with hA
  have hlen : pU.length = Fintype.card tm.Q + (k + 2) * (T + 1) + A := by
    rw [hpU, List.length_replicate, configIndex_cell, hA]
    omega
  have hnlt : ¬ pU.length < qU.length := by rw [hlen, hq]; omega
  have hrest : ¬ (wiRest qU pU).length < (mulLen tapesU horU).length := by
    rw [wiRest_length, length_mulLen, hlen, hq, htapes, hhor]
    omega
  have hdrop : pU.length - qU.length - tapesU.length * horU.length = A := by
    rw [hlen, hq, htapes, hhor]; omega
  have hsym : (wiCellSym qU horU tapesU pU).length = (symbolIndex sym).val := by
    rw [wiCellSym_length, hdrop, hA]
    have h4 : (t.index.val * (T + 2) + pos.val) * 4 + (symbolIndex sym).val
        = 4 * (t.index.val * (T + 2) + pos.val) + (symbolIndex sym).val := by ring
    rw [h4, Nat.mul_add_mod, Nat.mod_eq_of_lt (symbolIndex sym).isLt]
  have hrestv : (pU.length - qU.length - tapesU.length * horU.length) / 4
      = t.index.val * (T + 2) + pos.val := by
    rw [hdrop, hA]
    have h4 : (t.index.val * (T + 2) + pos.val) * 4 + (symbolIndex sym).val
        = 4 * (t.index.val * (T + 2) + pos.val) + (symbolIndex sym).val := by ring
    rw [h4, Nat.mul_add_div (by norm_num),
      Nat.div_eq_of_lt (symbolIndex sym).isLt]
    omega
  have htape : (wiCellTape qU horU hor2U tapesU pU).length = t.index.val := by
    rw [wiCellTape_length _ _ _ _ _ (by rw [hhor2]; omega), hrestv, hhor2]
    have h2 : t.index.val * (T + 2) + pos.val = (T + 2) * t.index.val + pos.val := by ring
    rw [h2, Nat.mul_add_div (by omega), Nat.div_eq_of_lt pos.isLt]
    omega
  have hposv : (wiCellPos qU horU hor2U tapesU pU).length = pos.val := by
    rw [wiCellPos_length _ _ _ _ _ (by rw [hhor2]; omega), hrestv, hhor2]
    have h2 : t.index.val * (T + 2) + pos.val = (T + 2) * t.index.val + pos.val := by ring
    rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt pos.isLt]
  rw [initBitU, ifLtLen_neg (by omega), ifLtLen_neg (by omega), ConfigAtom.value,
    get_init_cells]
  have hkey : (initSymIdxU x (wiCellTape qU horU hor2U tapesU pU)
      (wiCellPos qU horU hor2U tapesU pU)).length
      = (symbolIndex (if t.index.val = 0 then (Tape.init (x.map Γ.ofBool)).cells pos.val
          else (Tape.init []).cells pos.val)).val := by
    rw [initSymIdxU]
    by_cases ht : t.index.val = 0
    · rw [ifEqLen_pos (by rw [htape, ht]; rfl), if_pos ht, symStartInput_length, hposv]
    · rw [ifEqLen_neg (by rw [htape]; simpa using ht), if_neg ht]
      by_cases hp : pos.val = 0
      · rw [ifEqLen_pos (by rw [hposv, hp]; rfl), hp, Tape.init_cells_zero]
        rfl
      · rw [ifEqLen_neg (by rw [hposv]; simpa using hp)]
        have : (Tape.init ([] : List Γ)).cells pos.val = Γ.blank := by
          rw [Tape.init]
          simp [hp]
        rw [this]
        rfl
  by_cases hb : (if t.index.val = 0 then (Tape.init (x.map Γ.ofBool)).cells pos.val
      else (Tape.init []).cells pos.val) = sym
  · rw [ifEqLen_pos (by rw [hkey, hsym, hb]), if_pos (by simpa using hb)]
    rfl
  · rw [ifEqLen_neg (by
      rw [hkey, hsym]
      intro hcontra
      exact hb (symbolIndex_val_inj hcontra)), if_neg (by simpa using hb)]
    rfl

/-- **The initial block's bit at any wire index.** -/
theorem initBitU_length (qU horU hor2U tapesU qstartU x : List Bool)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (hhor2 : hor2U.length = T + 2) (htapes : tapesU.length = k + 2)
    (hqstart : qstartU.length = stateIndex tm tm.qstart) (atom : ConfigAtom tm T) :
    (initBitU qU horU hor2U tapesU qstartU x
        (List.replicate (configIndex tm T atom) true)).length
      = if ConfigAtom.value (Cfg.init tm.qstart x) atom then 1 else 0 := by
  cases atom with
  | state q => exact initBitU_state_length tm T qU horU hor2U tapesU qstartU x q hq hqstart
  | head t p => exact initBitU_head_length tm T qU horU hor2U tapesU qstartU x t p hq hhor htapes
  | cell t pos sym =>
      exact initBitU_cell_length tm T qU horU hor2U tapesU qstartU x t pos sym hq hhor hhor2
        htapes

/-- The same, indexed by the raw wire number. -/
theorem initBitU_length_of_lt (qU horU hor2U tapesU qstartU x : List Bool)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (hhor2 : hor2U.length = T + 2) (htapes : tapesU.length = k + 2)
    (hqstart : qstartU.length = stateIndex tm tm.qstart)
    (p : ℕ) (hp : p < configWidth tm T) :
    (initBitU qU horU hor2U tapesU qstartU x (List.replicate p true)).length
      = if ConfigAtom.value (Cfg.init tm.qstart x)
          ((configAtomEquiv tm T).symm ⟨p, hp⟩) then 1 else 0 := by
  have hidx : configIndex tm T ((configAtomEquiv tm T).symm ⟨p, hp⟩) = p := by
    rw [← configAtomEquiv_apply_val, Equiv.apply_symm_apply]
  have h := initBitU_length tm T qU horU hor2U tapesU qstartU x hq hhor hhor2 htapes hqstart
    ((configAtomEquiv tm T).symm ⟨p, hp⟩)
  rwa [hidx] at h

/-! ## The guards -/

/-- One guard clause, encoded from its index: a unit clause pinning the initial block, one of
the two validity groups (supplied already encoded), an acceptance clause, or the chain's first
bit. -/
noncomputable def guardEnc (validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
    accWire₁U accWire₂U y0U pU : List Bool) : List Bool :=
  ifLtLen pU wU
    (clause1 w (initBitU qU horU hor2U tapesU qstartU x pU) pU)
    (ifLtLen (pU.drop wU.length) vcU validAEnc
      (ifLtLen ((pU.drop wU.length).drop vcU.length) vcU validBEnc
        (ifEqLen (((pU.drop wU.length).drop vcU.length).drop vcU.length) []
          (clause1 w [true] accWire₁U)
          (ifEqLen (((pU.drop wU.length).drop vcU.length).drop vcU.length) [false]
            (clause1 w [true] accWire₂U)
            (clause1 w [true] y0U)))))

theorem guardEnc_mem_FP
    {validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU accWire₁U accWire₂U y0U pU
      : List Bool → List Bool}
    (hva : validAEnc ∈ FP) (hvb : validBEnc ∈ FP) (hw : w ∈ FP) (hq : qU ∈ FP)
    (hhor : horU ∈ FP) (hhor2 : hor2U ∈ FP) (ht : tapesU ∈ FP) (hqs : qstartU ∈ FP)
    (hx : x ∈ FP) (hwU : wU ∈ FP) (hvc : vcU ∈ FP) (ha₁ : accWire₁U ∈ FP)
    (ha₂ : accWire₂U ∈ FP) (hy : y0U ∈ FP) (hp : pU ∈ FP) :
    (fun z => guardEnc (validAEnc z) (validBEnc z) (w z) (qU z) (horU z) (hor2U z)
      (tapesU z) (qstartU z) (x z) (wU z) (vcU z) (accWire₁U z) (accWire₂U z) (y0U z)
      (pU z)) ∈ FP := by
  have d1 : (fun z => (pU z).drop (wU z).length) ∈ FP := dropLenFn_mem_FP hwU hp
  have d2 : (fun z => ((pU z).drop (wU z).length).drop (vcU z).length) ∈ FP :=
    dropLenFn_mem_FP hvc d1
  have d3 : (fun z => (((pU z).drop (wU z).length).drop (vcU z).length).drop (vcU z).length)
      ∈ FP := dropLenFn_mem_FP hvc d2
  exact ifLtLen_mem_FP hp hwU
    (clause1_mem_FP hw (initBitU_mem_FP hq hhor hhor2 ht hqs hx hp) hp)
    (ifLtLen_mem_FP d1 hvc hva
      (ifLtLen_mem_FP d2 hvc hvb
        (ifEqLen_mem_FP d3 (constFn_mem_FP [])
          (clause1_mem_FP hw (constFn_mem_FP [true]) ha₁)
          (ifEqLen_mem_FP d3 (constFn_mem_FP [false])
            (clause1_mem_FP hw (constFn_mem_FP [true]) ha₂)
            (clause1_mem_FP hw (constFn_mem_FP [true]) hy)))))

/-- **A guard clause pinning one bit of the initial block.** -/
theorem guardEnc_const_eq (validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
    accWire₁U accWire₂U y0U : List Bool)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (hhor2 : hor2U.length = T + 2) (htapes : tapesU.length = k + 2)
    (hqstart : qstartU.length = stateIndex tm tm.qstart)
    (p : ℕ) (hpw : p < wU.length) (hle : p ≤ w.length) (hpc : p < configWidth tm T) :
    guardEnc validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU accWire₁U
        accWire₂U y0U (List.replicate p true)
      = DataEncode.bitstringEncode
        [(ConfigAtom.value (Cfg.init tm.qstart x) ((configAtomEquiv tm T).symm ⟨p, hpc⟩),
          p)] := by
  have hbit := initBitU_length_of_lt tm T qU horU hor2U tapesU qstartU x hq hhor hhor2 htapes
    hqstart p hpc
  have hmin : min (List.replicate p true).length w.length = (List.replicate p true).length := by
    rw [List.length_replicate]
    omega
  rw [guardEnc, ifLtLen_pos (by rw [List.length_replicate]; exact hpw)]
  by_cases hb : ConfigAtom.value (Cfg.init tm.qstart x) ((configAtomEquiv tm T).symm ⟨p, hpc⟩)
  · have hne : initBitU qU horU hor2U tapesU qstartU x (List.replicate p true) ≠ [] := by
      intro h
      rw [h, if_pos hb] at hbit
      exact absurd hbit (by simp)
    rw [clause1_eq true (by rw [litEnc_pos' hne, hmin])]
    simp [hb]
  · have hnil : initBitU qU horU hor2U tapesU qstartU x (List.replicate p true) = [] := by
      rw [if_neg hb] at hbit
      exact List.eq_nil_of_length_eq_zero hbit
    have hbf : ConfigAtom.value (Cfg.init tm.qstart x)
        ((configAtomEquiv tm T).symm ⟨p, hpc⟩) = false := by simpa using hb
    rw [hnil, clause1_eq false (by rw [litEnc_neg', hmin])]
    simp [hbf]

/-- **The first acceptance guard.** -/
theorem guardEnc_acc₁_eq (validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
    accWire₁U accWire₂U y0U : List Bool) (p : ℕ)
    (hp : p = wU.length + vcU.length + vcU.length) (hle : accWire₁U.length ≤ w.length) :
    guardEnc validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU accWire₁U
        accWire₂U y0U (List.replicate p true)
      = DataEncode.bitstringEncode [(true, accWire₁U.length)] := by
  rw [guardEnc, ifLtLen_neg (by rw [List.length_replicate, hp]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate, hp]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_drop, List.length_replicate, hp]; omega),
    ifEqLen_pos (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate, hp,
        List.length_nil]
      omega),
    clause1_eq true (by rw [litEnc_pos' (by simp), Nat.min_eq_left hle])]

/-- **The second acceptance guard.** -/
theorem guardEnc_acc₂_eq (validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
    accWire₁U accWire₂U y0U : List Bool) (p : ℕ)
    (hp : p = wU.length + vcU.length + vcU.length + 1) (hle : accWire₂U.length ≤ w.length) :
    guardEnc validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU accWire₁U
        accWire₂U y0U (List.replicate p true)
      = DataEncode.bitstringEncode [(true, accWire₂U.length)] := by
  rw [guardEnc, ifLtLen_neg (by rw [List.length_replicate, hp]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate, hp]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_drop, List.length_replicate, hp]; omega),
    ifEqLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate, hp,
        List.length_nil]
      omega),
    ifEqLen_pos (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate, hp]
      simp
      omega),
    clause1_eq true (by rw [litEnc_pos' (by simp), Nat.min_eq_left hle])]

/-- **The guard that starts the chain.** -/
theorem guardEnc_y0_eq (validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
    accWire₁U accWire₂U y0U : List Bool) (p : ℕ)
    (hp : p = wU.length + vcU.length + vcU.length + 2) (hle : y0U.length ≤ w.length) :
    guardEnc validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU accWire₁U
        accWire₂U y0U (List.replicate p true)
      = DataEncode.bitstringEncode [(true, y0U.length)] := by
  rw [guardEnc, ifLtLen_neg (by rw [List.length_replicate, hp]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate, hp]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_drop, List.length_replicate, hp]; omega),
    ifEqLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate, hp,
        List.length_nil]
      omega),
    ifEqLen_neg (by
      rw [List.length_drop, List.length_drop, List.length_drop, List.length_replicate, hp]
      simp
      omega),
    clause1_eq true (by rw [litEnc_pos' (by simp), Nat.min_eq_left hle])]

/-- The guard family's first validity block is the supplied encoding. -/
theorem guardEnc_validA_eq (validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
    accWire₁U accWire₂U y0U : List Bool) (p : ℕ)
    (h₁ : wU.length ≤ p) (h₂ : p < wU.length + vcU.length) :
    guardEnc validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU accWire₁U
        accWire₂U y0U (List.replicate p true) = validAEnc := by
  rw [guardEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_pos (by rw [List.length_drop, List.length_replicate]; omega)]

/-- The guard family's second validity block is the supplied encoding. -/
theorem guardEnc_validB_eq (validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
    accWire₁U accWire₂U y0U : List Bool) (p : ℕ)
    (h₁ : wU.length + vcU.length ≤ p) (h₂ : p < wU.length + vcU.length + vcU.length) :
    guardEnc validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU accWire₁U
        accWire₂U y0U (List.replicate p true) = validBEnc := by
  rw [guardEnc, ifLtLen_neg (by rw [List.length_replicate]; omega),
    ifLtLen_neg (by rw [List.length_drop, List.length_replicate]; omega),
    ifLtLen_pos (by rw [List.length_drop, List.length_drop, List.length_replicate]; omega)]

/-- **A guard clause, encoded**, given that the validity families are encoded. -/
theorem guardEnc_eq (validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
    accWire₁U accWire₂U y0U : List Bool) (L : FlatLayout)
    (validC : ℕ → List (List CLit)) (init : Fin L.W → Bool)
    (hVC : ∀ off, (validC off).length = vcU.length)
    (hWc : L.W = configWidth tm T) (hW : wU.length = L.W)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (hhor2 : hor2U.length = T + 2) (htapes : tapesU.length = k + 2)
    (hqstart : qstartU.length = stateIndex tm tm.qstart)
    (hinit : ∀ (r : ℕ) (hr : r < L.W), init ⟨r, hr⟩
      = ConfigAtom.value (Cfg.init tm.qstart x)
        ((configAtomEquiv tm T).symm ⟨r, by omega⟩))
    (ha₁ : accWire₁U.length = configWire tm T L.bStart (ConfigAtom.state tm.qhalt))
    (ha₂ : accWire₂U.length
      = configWire tm T L.bStart (ConfigAtom.cell TapeSlot.output ⟨1, by omega⟩ Γ.one))
    (hy0 : y0U.length = L.y0)
    (hWle : L.W ≤ w.length) (ha₁le : accWire₁U.length ≤ w.length)
    (ha₂le : accWire₂U.length ≤ w.length) (hy0le : y0U.length ≤ w.length)
    (p : ℕ) (hp : p < wU.length + (vcU.length + (vcU.length + (2 + 1))))
    (hvA : wU.length ≤ p → p < wU.length + vcU.length →
      ((validC 0)[p - wU.length]?).map DataEncode.bitstringEncode = some validAEnc)
    (hvB : wU.length + vcU.length ≤ p → p < wU.length + vcU.length + vcU.length →
      ((validC L.bStart)[p - wU.length - vcU.length]?).map DataEncode.bitstringEncode
        = some validBEnc) :
    ((L.guardClauses validC (cfgAccC tm T) init)[p]?).map DataEncode.bitstringEncode
      = some (guardEnc validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
          accWire₁U accWire₂U y0U (List.replicate p true)) := by
  have hAC : ∀ off, (cfgAccC tm T off).length = 2 := fun off => cfgAccC_length tm T off
  by_cases c0 : p < L.W
  · rw [L.guardClauses_getElem?_const validC (cfgAccC tm T) init (p := p) c0,
      guardEnc_const_eq tm T validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
        accWire₁U accWire₂U y0U hq hhor hhor2 htapes hqstart p (by omega) (by omega)
        (by omega), Option.map_some, hinit p c0, Nat.zero_add]
  · by_cases c1 : p < L.W + vcU.length
    · rw [L.guardClauses_getElem?_validA validC (cfgAccC tm T) vcU.length hVC init
        (p := p) (by omega) (by omega),
        guardEnc_validA_eq validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
          accWire₁U accWire₂U y0U p (by omega) (by omega)]
      have := hvA (by omega) (by omega)
      rw [hW] at this
      exact this
    · by_cases c2 : p < L.W + vcU.length + vcU.length
      · rw [L.guardClauses_getElem?_validB validC (cfgAccC tm T) vcU.length hVC init
          (p := p) (by omega) (by omega),
          guardEnc_validB_eq validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
            accWire₁U accWire₂U y0U p (by omega) (by omega)]
        have := hvB (by omega) (by omega)
        rw [hW] at this
        exact this
      · by_cases c3 : p < L.W + vcU.length + vcU.length + 2
        · rw [L.guardClauses_getElem?_acc validC (cfgAccC tm T) vcU.length 2 hVC hAC init
            (p := p) (by omega) (by omega), cfgAccC]
          by_cases c4 : p = L.W + vcU.length + vcU.length
          · have hidx : p - L.W - vcU.length - vcU.length = 0 := by omega
            rw [hidx,
              guardEnc_acc₁_eq validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
                accWire₁U accWire₂U y0U p (by omega) ha₁le, ha₁]
            rfl
          · have hidx : p - L.W - vcU.length - vcU.length = 1 := by omega
            rw [hidx,
              guardEnc_acc₂_eq validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
                accWire₁U accWire₂U y0U p (by omega) ha₂le, ha₂]
            rfl
        · rw [L.guardClauses_getElem?_unit validC (cfgAccC tm T) vcU.length 2 hVC hAC init
            (p := p) (by omega)]
          have hidx : p - L.W - vcU.length - vcU.length - 2 = 0 := by omega
          rw [hidx,
            guardEnc_y0_eq validAEnc validBEnc w qU horU hor2U tapesU qstartU x wU vcU
              accWire₁U accWire₂U y0U p (by omega) hy0le, hy0]
          rfl

/-- **The base family's equality half, encoded.** -/
theorem baseEnc_eq_value (stepEnc w uU vU s1U w2U : List Bool) (s p : ℕ)
    (hs1 : s1U.length = s + 1) (hw2 : w2U.length = configWidth tm T * 2)
    (hp : p < configWidth tm T * 2)
    (h₁ : uU.length + p / 2 ≤ w.length) (h₂ : vU.length + p / 2 ≤ w.length)
    (hs1le : s1U.length ≤ w.length) :
    ((cfgBaseC tm T uU.length vU.length s)[p]?).map DataEncode.bitstringEncode
      = some (baseEnc stepEnc w uU vU s1U w2U (List.replicate p true)) := by
  rw [baseEnc_eq_eq stepEnc w uU vU s1U w2U (List.replicate p true)
      (by rw [List.length_replicate, hw2]; exact hp),
    cfgBaseC_getElem?_eq tm T uU.length vU.length s p hp,
    eqClauses_getElem?_eq (configWidth tm T) uU.length vU.length p hp, Option.map_some,
    Option.map_some,
    eqClauseEnc_eq w uU vU (List.replicate p true)
      (by rwa [List.length_replicate]) (by rwa [List.length_replicate]),
    List.length_replicate,
    consLitEnc_eq false _ (by rw [litEnc_neg', Nat.min_eq_left hs1le]), hs1]

/-- **The base family's step half, encoded**, given that the step clause is. -/
theorem baseEnc_step_value (stepEnc w uU vU s1U w2U : List Bool) (s p : ℕ)
    (hs1 : s1U.length = s + 1) (hw2 : w2U.length = configWidth tm T * 2)
    (hp : configWidth tm T * 2 ≤ p) (hs1le : s1U.length ≤ w.length)
    (hstep : ((stepClauses tm T uU.length vU.length s)[p - configWidth tm T * 2]?).map
      DataEncode.bitstringEncode = some stepEnc) :
    ((cfgBaseC tm T uU.length vU.length s)[p]?).map DataEncode.bitstringEncode
      = some (baseEnc stepEnc w uU vU s1U w2U (List.replicate p true)) := by
  rw [baseEnc_step_eq stepEnc w uU vU s1U w2U (List.replicate p true)
      (by rw [List.length_replicate, hw2]; exact hp),
    cfgBaseC_getElem?_step tm T uU.length vU.length s p hp]
  rcases hc : (stepClauses tm T uU.length vU.length s)[p - configWidth tm T * 2]? with _ | c
  · rw [hc] at hstep
    exact absurd hstep (by simp)
  · rw [hc, Option.map_some] at hstep
    rw [Option.map_some, ← Option.some.inj hstep,
      consLitEnc_eq true c (by rw [litEnc_pos' (by simp), Nat.min_eq_left hs1le]), hs1]
    rfl

/-! ## The values of a view clause's later literals -/

theorem viewLitEnc_last_pos (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
    : List Bool) (hj0 : jU.length ≠ 0) (hj1 : jU.length ≠ 1)
    (hge : 2 * tapesU.length ≤ jU.length - 2) (hb : bU ≠ [])
    (hle : vU.length + forcedU.length ≤ w.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      = DataEncode.bitstringEncode
          ((true, vU.length + forcedU.length) : Bool × ℕ) := by
  have hlen : (vU ++ forcedU).length = vU.length + forcedU.length := List.length_append
  rw [viewLitEnc_last_eq tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
    hj0 hj1 hge, litEnc_pos hb (by rw [hlen]; exact hle), hlen]

theorem viewLitEnc_last_neg (w uU vU sU qU hdU horU hor2U caseU viewU forcedU tapesU jU
    : List Bool) (hj0 : jU.length ≠ 0) (hj1 : jU.length ≠ 1)
    (hge : 2 * tapesU.length ≤ jU.length - 2)
    (hle : vU.length + forcedU.length ≤ w.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU [] tapesU jU
      = DataEncode.bitstringEncode
          ((false, vU.length + forcedU.length) : Bool × ℕ) := by
  have hlen : (vU ++ forcedU).length = vU.length + forcedU.length := List.length_append
  rw [viewLitEnc_last_eq tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU [] tapesU jU
    hj0 hj1 hge, litEnc_neg (by rw [hlen]; exact hle), hlen]

theorem viewLitEnc_tape_head (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
    : List Bool) (hj0 : jU.length ≠ 0) (hj1 : jU.length ≠ 1)
    (hlt : jU.length - 2 < 2 * tapesU.length)
    (hr : (jU.length - 2) % 2 = 0)
    (hle : (headWireU uU qU (divC 2 (dropOne (dropOne jU)))
      (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) horU).length ≤ w.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      = DataEncode.bitstringEncode
          ((false, (headWireU uU qU (divC 2 (dropOne (dropOne jU)))
            (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) horU).length)
            : Bool × ℕ) := by
  have hd2 : (dropOne (dropOne jU)).length = jU.length - 2 := by
    rw [dropOne, dropOne, List.length_drop, List.length_drop]
    omega
  have hm : (modC 2 (dropOne (dropOne jU))).length = (jU.length - 2) % 2 := by
    rw [modC_eq (by norm_num), List.length_replicate, hd2]
  rw [viewLitEnc_tape_eq tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      hj0 hj1 hlt, ifEqLen_pos (by rw [hm, hr]; rfl), litEnc_neg hle]

theorem viewLitEnc_tape_cell (w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
    : List Bool) (hj0 : jU.length ≠ 0) (hj1 : jU.length ≠ 1)
    (hlt : jU.length - 2 < 2 * tapesU.length)
    (hr : (jU.length - 2) % 2 ≠ 0)
    (hle : (cellWireU uU qU hdU (divC 2 (dropOne (dropOne jU)))
      (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) hor2U
      (tableU2 (caseList tm) (tapeList k) (fun c t => (symbolIndex (c.read t)).val)
        caseU (divC 2 (dropOne (dropOne jU))))).length ≤ w.length) :
    viewLitEnc tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      = DataEncode.bitstringEncode
          ((false, (cellWireU uU qU hdU (divC 2 (dropOne (dropOne jU)))
            (headDigitU horU (divC 2 (dropOne (dropOne jU))) viewU) hor2U
            (tableU2 (caseList tm) (tapeList k)
              (fun c t => (symbolIndex (c.read t)).val) caseU
              (divC 2 (dropOne (dropOne jU))))).length) : Bool × ℕ) := by
  have hd2 : (dropOne (dropOne jU)).length = jU.length - 2 := by
    rw [dropOne, dropOne, List.length_drop, List.length_drop]
    omega
  have hm : (modC 2 (dropOne (dropOne jU))).length = (jU.length - 2) % 2 := by
    rw [modC_eq (by norm_num), List.length_replicate, hd2]
  rw [viewLitEnc_tape_eq tm w uU vU sU qU hdU horU hor2U caseU viewU forcedU bU tapesU jU
      hj0 hj1 hlt, ifEqLen_neg (by rw [hm]; simpa using hr), litEnc_neg hle]

/-! ## The values of a validity group's later clauses -/

theorem cellGroupEnc_succ_eq (w offU qU hdU tapeU posU horU startU mU pU : List Bool)
    (hp : pU ≠ [])
    (h₁ : (cellWireU offU qU hdU tapeU posU horU []).length + (pU.length - 1) / 4
      ≤ w.length)
    (h₂ : (cellWireU offU qU hdU tapeU posU horU []).length + (pU.length - 1) % 4
      ≤ w.length) :
    cellGroupEnc w offU qU hdU tapeU posU horU startU mU pU
      = DataEncode.bitstringEncode
          (if (cellWireU offU qU hdU tapeU posU horU []).length + (pU.length - 1) / 4
                = (cellWireU offU qU hdU tapeU posU horU []).length
                  + (pU.length - 1) % 4 then
              [(false, (cellWireU offU qU hdU tapeU posU horU []).length
                  + (pU.length - 1) / 4),
                (true, (cellWireU offU qU hdU tapeU posU horU []).length
                  + (pU.length - 1) / 4)]
            else [(false, (cellWireU offU qU hdU tapeU posU horU []).length
                  + (pU.length - 1) / 4),
                (false, (cellWireU offU qU hdU tapeU posU horU []).length
                  + (pU.length - 1) % 4)]) := by
  have hn : ([false, false, false, false] : List Bool).length = 4 := rfl
  rw [cellGroupEnc, oneHotEnc_succ w (cellWireU offU qU hdU tapeU posU horU startU)
    (cellWireU offU qU hdU tapeU posU horU []) mU [false, false, false, false] pU hp
    (by rw [hn]; omega) (by rw [hn]; exact h₁) (by rw [hn]; exact h₂), hn]

theorem validEnc_head_succ_value (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
    : List Bool) (hge : sqU.length ≤ pU.length)
    (hlt : (offInTape sqU tbU pU).length < hsU.length)
    (hne : offInTape sqU tbU pU ≠ []) (hhor : 0 < horU.length)
    (h₁ : (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length
        + ((offInTape sqU tbU pU).length - 1) / horU.length ≤ w.length)
    (h₂ : (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length
        + ((offInTape sqU tbU pU).length - 1) % horU.length ≤ w.length) :
    validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
      = DataEncode.bitstringEncode
          (if (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length
                + ((offInTape sqU tbU pU).length - 1) / horU.length
              = (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length
                + ((offInTape sqU tbU pU).length - 1) % horU.length then
              [(false, (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length
                  + ((offInTape sqU tbU pU).length - 1) / horU.length),
                (true, (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length
                  + ((offInTape sqU tbU pU).length - 1) / horU.length)]
            else [(false, (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length
                  + ((offInTape sqU tbU pU).length - 1) / horU.length),
                (false, (headWireU offU qU (tapeOfIdx sqU tbU pU) [] horU).length
                  + ((offInTape sqU tbU pU).length - 1) % horU.length)]) := by
  rw [validEnc_head_succ_eq w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU hge hlt,
    headGroupEnc_succ_eq w offU qU (tapeOfIdx sqU tbU pU) horU
      (headCountU x SU (tapeOfIdx sqU tbU pU) lastU horU) (offInTape sqU tbU pU) hne hhor
      h₁ h₂]

/-- The cell-group index a validity clause index names. -/
noncomputable def cellIdx (sqU tbU hsU pU : List Bool) : List Bool :=
  modFn2 (pair cellSizeU ((offInTape sqU tbU pU).drop hsU.length))

/-- The cell position a validity clause index names. -/
noncomputable def cellPos (sqU tbU hsU pU : List Bool) : List Bool :=
  divFn2 (pair cellSizeU ((offInTape sqU tbU pU).drop hsU.length))

theorem validEnc_cell_succ_value (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
    : List Bool) (hge : sqU.length ≤ pU.length)
    (hge2 : hsU.length ≤ (offInTape sqU tbU pU).length)
    (hne : cellIdx sqU tbU hsU pU ≠ [])
    (h₁ : (cellWireU offU qU hdU (tapeOfIdx sqU tbU pU) (cellPos sqU tbU hsU pU) hor2U []).length
        + ((cellIdx sqU tbU hsU pU).length - 1) / 4 ≤ w.length)
    (h₂ : (cellWireU offU qU hdU (tapeOfIdx sqU tbU pU) (cellPos sqU tbU hsU pU) hor2U []).length
        + ((cellIdx sqU tbU hsU pU).length - 1) % 4 ≤ w.length) :
    validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU
      = DataEncode.bitstringEncode
          (if (cellWireU offU qU hdU (tapeOfIdx sqU tbU pU) (cellPos sqU tbU hsU pU)
                  hor2U []).length
                + ((cellIdx sqU tbU hsU pU).length - 1) / 4
              = (cellWireU offU qU hdU (tapeOfIdx sqU tbU pU) (cellPos sqU tbU hsU pU)
                  hor2U []).length
                + ((cellIdx sqU tbU hsU pU).length - 1) % 4 then
              [(false, (cellWireU offU qU hdU (tapeOfIdx sqU tbU pU)
                  (cellPos sqU tbU hsU pU) hor2U []).length
                  + ((cellIdx sqU tbU hsU pU).length - 1) / 4),
                (true, (cellWireU offU qU hdU (tapeOfIdx sqU tbU pU)
                  (cellPos sqU tbU hsU pU) hor2U []).length
                  + ((cellIdx sqU tbU hsU pU).length - 1) / 4)]
            else [(false, (cellWireU offU qU hdU (tapeOfIdx sqU tbU pU)
                  (cellPos sqU tbU hsU pU) hor2U []).length
                  + ((cellIdx sqU tbU hsU pU).length - 1) / 4),
                (false, (cellWireU offU qU hdU (tapeOfIdx sqU tbU pU)
                  (cellPos sqU tbU hsU pU) hor2U []).length
                  + ((cellIdx sqU tbU hsU pU).length - 1) % 4)]) := by
  rw [validEnc_cell_eq w offU qU sqU tbU hdU horU hor2U x SU lastU hsU pU hge hge2,
    show divFn2 (pair cellSizeU ((offInTape sqU tbU pU).drop hsU.length))
      = cellPos sqU tbU hsU pU from rfl,
    show modFn2 (pair cellSizeU ((offInTape sqU tbU pU).drop hsU.length))
      = cellIdx sqU tbU hsU pU from rfl,
    cellGroupEnc_succ_eq w offU qU hdU (tapeOfIdx sqU tbU pU) (cellPos sqU tbU hsU pU)
      hor2U (symStartU x SU (tapeOfIdx sqU tbU pU) lastU (cellPos sqU tbU hsU pU))
      (symCountU SU (tapeOfIdx sqU tbU pU) lastU (cellPos sqU tbU hsU pU))
      (cellIdx sqU tbU hsU pU) hne h₁ h₂]

/-- **A cell group's at-most-one clauses, encoded.** -/
theorem validEnc_cell_succ (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU : List Bool)
    (S p : ℕ) (hsq : sqU.length = 1 + Fintype.card tm.Q * Fintype.card tm.Q)
    (htb : tbU.length = tapeBlockSize T) (hhs : hsU.length = 1 + (T + 1) * (T + 1))
    (hhd : hdU.length = (k + 2) * (T + 1)) (hhor2 : hor2U.length = T + 2)
    (hq : qU.length = Fintype.card tm.Q)
    (h₁ : sqU.length ≤ p) (h₂ : p < sqU.length + (k + 2) * tapeBlockSize T)
    (hoffge : hsU.length ≤ (p - sqU.length) % tapeBlockSize T)
    (hcellpos : 0 < ((p - sqU.length) % tapeBlockSize T - hsU.length) % (1 + 4 * 4))
    (hb : ∀ j, j < 4 →
      (cellWireU offU qU hdU (tapeOfIdx sqU tbU (List.replicate p true))
        (cellPos sqU tbU hsU (List.replicate p true)) hor2U []).length + j ≤ w.length) :
    ((cfgValidC tm T x S offU.length)[p]?).map DataEncode.bitstringEncode
      = some (validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
          (List.replicate p true)) := by
  have htbpos : 0 < tapeBlockSize T := tapeBlockSize_pos T
  have hcomm : (k + 2) * tapeBlockSize T = tapeBlockSize T * (k + 2) := Nat.mul_comm _ _
  have hi : (p - sqU.length) / tapeBlockSize T < k + 2 := Nat.div_lt_of_lt_mul (by omega)
  have hlenrep : (List.replicate p true).length = p := List.length_replicate
  have htape : (tapeOfIdx sqU tbU (List.replicate p true)).length
      = ((tapeSlotEquiv k).symm ⟨(p - sqU.length) / tapeBlockSize T, hi⟩).index.val := by
    rw [tapeOfIdx_length _ _ _ (by omega), hlenrep, htb, tapeSlotEquiv_symm_index]
  have hr : (offInTape sqU tbU (List.replicate p true)).length
      = (p - sqU.length) % tapeBlockSize T := by
    rw [offInTape_length _ _ _ (by omega), hlenrep, htb]
  have htbeq : tapeBlockSize T = 1 + (T + 1) * (T + 1) + (T + 2) * (1 + 4 * 4) := rfl
  have hrlt : (p - sqU.length) % tapeBlockSize T
      < 1 + (T + 1) * (T + 1) + (T + 2) * (1 + 4 * 4) := by
    rw [← htbeq]; exact Nat.mod_lt _ htbpos
  have hdrop : ((offInTape sqU tbU (List.replicate p true)).drop hsU.length).length
      = (p - sqU.length) % tapeBlockSize T - hsU.length := by
    rw [List.length_drop, hr]
  have hposlt : ((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4) < T + 2 :=
    Nat.div_lt_of_lt_mul (by omega)
  have hpos : (cellPos sqU tbU hsU (List.replicate p true)).length
      = ((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4) := by
    rw [cellPos, divFn2_eq (by rw [cellSizeU_length]; omega), List.length_replicate, hdrop,
      cellSizeU_length]
  have hidx : (cellIdx sqU tbU hsU (List.replicate p true)).length
      = ((p - sqU.length) % tapeBlockSize T - hsU.length) % (1 + 4 * 4) := by
    rw [cellIdx, modFn2_eq (by rw [cellSizeU_length]; omega), List.length_replicate, hdrop,
      cellSizeU_length]
  have hidxlt : ((p - sqU.length) % tapeBlockSize T - hsU.length) % (1 + 4 * 4)
      < 1 + 4 * 4 := Nat.mod_lt _ (by omega)
  have hbound : (p - sqU.length) % tapeBlockSize T - hsU.length
      < (List.finRange (T + 2)).length * (1 + 4 * 4) := by
    rw [List.length_finRange]
    omega
  have hwire : (cellWireU offU qU hdU (tapeOfIdx sqU tbU (List.replicate p true))
      (cellPos sqU tbU hsU (List.replicate p true)) hor2U []).length
      = offU.length + cellBase tm T
        ((tapeSlotEquiv k).symm ⟨(p - sqU.length) / tapeBlockSize T, hi⟩)
        ⟨((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4), hposlt⟩ :=
    cellWireU_zero tm T offU.length _ _ rfl hq hhd htape hpos hhor2
  have hb' : ∀ j, j < 4 → offU.length + cellBase tm T
      ((tapeSlotEquiv k).symm ⟨(p - sqU.length) / tapeBlockSize T, hi⟩)
      ⟨((p - sqU.length) % tapeBlockSize T - hsU.length) / (1 + 4 * 4), hposlt⟩ + j
      ≤ w.length := by
    intro j hj'
    rw [← hwire]
    exact hb j hj'
  obtain ⟨j, hj⟩ : ∃ j, ((p - sqU.length) % tapeBlockSize T - hsU.length) % (1 + 4 * 4)
      = j + 1 :=
    ⟨((p - sqU.length) % tapeBlockSize T - hsU.length) % (1 + 4 * 4) - 1, by omega⟩
  rw [cfgValidC_getElem?_tape tm T x S offU.length p (by omega) (by omega), ← hsq,
    tapeList_getElem? _ hi, Option.bind_some,
    List.getElem?_append_right (by rw [headGroupC_length, ← hhs]; omega),
    headGroupC_length, ← hhs,
    getElem?_flatMap_const (1 + 4 * 4) (by omega) _
      (fun pos => cellGroupC_length tm T x S offU.length _ pos) _ _ hbound,
    finRange_getElem? _ _ hposlt, Option.bind_some, hj,
    cellGroupC_getElem?_succ tm T x S offU.length j _ _ (by omega), Option.map_some,
    validEnc_cell_succ_value w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
      (List.replicate p true) (by rw [hlenrep]; omega) (by rw [hr]; omega)
      (by
        intro hnil
        rw [hnil, List.length_nil] at hidx
        omega)
      (by
        rw [hwire, hidx, hj, Nat.add_sub_cancel]
        exact hb' _ (Nat.div_lt_of_lt_mul (by omega)))
      (by
        rw [hwire, hidx, hj, Nat.add_sub_cancel]
        exact hb' _ (Nat.mod_lt _ (by omega))),
    hwire, hidx, hj, Nat.add_sub_cancel, ← Nat.add_assoc, ← Nat.add_assoc]

/-- **A validity clause at any index, encoded.** -/
theorem validEnc_eq (w offU qU sqU tbU hdU horU hor2U x SU lastU hsU : List Bool)
    (S p : ℕ) (hsq : sqU.length = 1 + Fintype.card tm.Q * Fintype.card tm.Q)
    (htb : tbU.length = tapeBlockSize T) (hhs : hsU.length = 1 + (T + 1) * (T + 1))
    (hhd : hdU.length = (k + 2) * (T + 1)) (hhor : horU.length = T + 1)
    (hhor2 : hor2U.length = T + 2) (hSU : SU.length = S) (hlast : lastU.length = k + 1)
    (hq : qU.length = Fintype.card tm.Q) (hcard : 0 < Fintype.card tm.Q)
    (hp : p < sqU.length + (k + 2) * tapeBlockSize T)
    (hbState : ∀ j, j < Fintype.card tm.Q → offU.length + j ≤ w.length)
    (hbHead : ∀ i, i < T + 1 →
      (headWireU offU qU (tapeOfIdx sqU tbU (List.replicate p true)) [] horU).length + i
        ≤ w.length)
    (hbHead0 : ∀ j, j < (headCountU x SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU
        horU).length →
      (headWireU offU qU (tapeOfIdx sqU tbU (List.replicate p true)) [] horU).length + j
        ≤ w.length)
    (hbCell0 : ∀ j, j < (symCountU SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU
        (cellPos sqU tbU hsU (List.replicate p true))).length →
      (cellWireU offU qU hdU (tapeOfIdx sqU tbU (List.replicate p true))
        (cellPos sqU tbU hsU (List.replicate p true)) hor2U
        (symStartU x SU (tapeOfIdx sqU tbU (List.replicate p true)) lastU
          (cellPos sqU tbU hsU (List.replicate p true)))).length + j ≤ w.length)
    (hbCell : ∀ j, j < 4 →
      (cellWireU offU qU hdU (tapeOfIdx sqU tbU (List.replicate p true))
        (cellPos sqU tbU hsU (List.replicate p true)) hor2U []).length + j ≤ w.length) :
    ((cfgValidC tm T x S offU.length)[p]?).map DataEncode.bitstringEncode
      = some (validEnc w offU qU sqU tbU hdU horU hor2U x SU lastU hsU
          (List.replicate p true)) := by
  by_cases hstate : p < sqU.length
  · exact validEnc_state_eq tm T w offU qU sqU tbU hdU horU hor2U x SU lastU hsU S p hstate
      hsq hq hcard hbState
  · by_cases hzero : (p - sqU.length) % tapeBlockSize T = 0
    · exact validEnc_head_zero tm T w offU qU sqU tbU hdU horU hor2U x SU lastU hsU S p hsq
        htb (by omega) hSU hlast hhor hq (by omega) (by omega) hzero hbHead0
    · by_cases hhead : (p - sqU.length) % tapeBlockSize T < hsU.length
      · exact validEnc_head_succ tm T w offU qU sqU tbU hdU horU hor2U x SU lastU hsU S p
          hsq htb hhs hhor hq (by omega) (by omega) (by omega) hhead hbHead
      · by_cases hcellz : ((p - sqU.length) % tapeBlockSize T - hsU.length) % (1 + 4 * 4)
            = 0
        · exact validEnc_cell_zero tm T w offU qU sqU tbU hdU horU hor2U x SU lastU hsU S p
            hsq htb hhs hhd hhor2 hSU hlast hq (by omega) (by omega) (by omega) hcellz
            hbCell0
        · exact validEnc_cell_succ tm T w offU qU sqU tbU hdU horU hor2U x SU lastU hsU S p
            hsq htb hhs hhd hhor2 hq (by omega) (by omega) (by omega) (by omega) hbCell

theorem card_le_configWidth : Fintype.card tm.Q ≤ configWidth tm T := by
  rw [configWidth]
  omega

/-- A validity index inside the tape blocks names one of the `k + 2` tapes. -/
theorem tapeOfIdx_lt (sqU tbU pU : List Bool) (htb : tbU.length = tapeBlockSize T)
    (hp : pU.length < sqU.length + (k + 2) * tapeBlockSize T) :
    (tapeOfIdx sqU tbU pU).length < k + 2 := by
  have hpos : 0 < tapeBlockSize T := tapeBlockSize_pos T
  have hc : (k + 2) * tapeBlockSize T = tapeBlockSize T * (k + 2) := Nat.mul_comm _ _
  have hpos2 : 0 < tapeBlockSize T * (k + 2) := by positivity
  rw [tapeOfIdx_length _ _ _ (by rw [htb]; exact hpos), htb]
  exact Nat.div_lt_of_lt_mul (by omega)

/-- Any wire of a block that fits inside the variable count is itself inside it. -/
theorem wire_add_le (off N : ℕ) (atom : ConfigAtom tm T)
    (hoff : off + configWidth tm T ≤ N) : off + configIndex tm T atom ≤ N := by
  have := configIndex_lt tm T atom
  omega

/-- A head wire of a block that fits, plus a position, is inside the variable count. -/
theorem headWire_add_le (off N : ℕ) (tape : TapeSlot k) (j : ℕ) (hj : j < T + 1)
    {offU qU tapeU horU : List Bool} (hoffU : offU.length = off)
    (hq : qU.length = Fintype.card tm.Q) (htape : tapeU.length = tape.index.val)
    (hhor : horU.length = T + 1) (hoff : off + configWidth tm T ≤ N) :
    (headWireU offU qU tapeU [] horU).length + j ≤ N := by
  rw [headWireU_zero_add tm T off tape j hj hoffU hq htape hhor, configWire]
  exact wire_add_le tm T off N _ hoff

/-- A cell wire of a block that fits, plus a symbol offset, is inside the variable count. -/
theorem cellWire_add_le (off N : ℕ) (tape : TapeSlot k) (pos : Fin (T + 2)) (sym : Γ)
    (j : ℕ) (hj : (symbolIndex sym).val + j < 4)
    {offU qU hdU tapeU posU horU symU : List Bool} (hoffU : offU.length = off)
    (hq : qU.length = Fintype.card tm.Q) (hhd : hdU.length = (k + 2) * (T + 1))
    (htape : tapeU.length = tape.index.val) (hpos : posU.length = pos.val)
    (hhor : horU.length = T + 2) (hsym : symU.length = (symbolIndex sym).val)
    (hoff : off + configWidth tm T ≤ N) :
    (cellWireU offU qU hdU tapeU posU horU symU).length + j ≤ N := by
  have hlt : (symbolIndex sym).val + j
      < (Finset.univ : Finset Γ).card := by
    rw [Finset.card_univ]
    simpa using hj
  obtain ⟨sym', hsym'⟩ : ∃ sym' : Γ, (symbolIndex sym').val = (symbolIndex sym).val + j :=
    ⟨symbolList[(symbolIndex sym).val + j]'(by rw [symbolList_length]; omega),
      symbolIndex_symbolList _ (by omega)⟩
  have hwire : (cellWireU offU qU hdU tapeU posU horU symU).length + j
      = off + configIndex tm T (.cell tape pos sym') := by
    rw [cellWireU_length, hoffU, hq, hhd, htape, hpos, hhor, hsym, configIndex_cell, hsym']
    ring
  rw [hwire]
  exact wire_add_le tm T off N _ hoff

/-- A validity index names a cell position inside the tape. -/
theorem cellPos_lt (sqU tbU hsU pU : List Bool) (htb : tbU.length = tapeBlockSize T)
    (hhs : hsU.length = 1 + (T + 1) * (T + 1)) :
    (cellPos sqU tbU hsU pU).length < T + 2 := by
  have htbpos : 0 < tapeBlockSize T := tapeBlockSize_pos T
  have htbeq : tapeBlockSize T = 1 + (T + 1) * (T + 1) + (T + 2) * (1 + 4 * 4) := rfl
  have hrlt : (pU.length - sqU.length) % tbU.length
      < 1 + (T + 1) * (T + 1) + (T + 2) * (1 + 4 * 4) := by
    rw [htb, ← htbeq]
    exact Nat.mod_lt _ htbpos
  have hdrop : ((offInTape sqU tbU pU).drop hsU.length).length
      < (T + 2) * (1 + 4 * 4) := by
    rw [List.length_drop, offInTape_length _ _ _ (by rw [htb]; exact htbpos), hhs]
    omega
  rw [cellPos, divFn2_eq (by rw [cellSizeU_length]; omega), List.length_replicate,
    cellSizeU_length]
  refine Nat.div_lt_of_lt_mul ?_
  have hc : (T + 2) * (1 + 4 * 4) = (1 + 4 * 4) * (T + 2) := Nat.mul_comm _ _
  omega

/-! ## The validity emitter at the machine's sizes -/

open Polynomial in
/-- One validity clause of the block at `offU`, with every size supplied by the layout's
polynomials. -/
noncomputable def validEncAt (sp : Polynomial ℕ) (offU pU z : List Bool) : List Bool :=
  validEnc (rulerOf (nvarP tm sp) z) offU (rulerOf (C (Fintype.card tm.Q)) z)
    (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
    (rulerOf (headBlockP (k := k) sp) z)
    (rulerOf (horP sp) z) (rulerOf (hor2P sp) z) (pairFst z) (rulerOf sp z)
    (rulerOf (C (k + 1)) z) (rulerOf (headGroupP sp) z) pU

open Polynomial in
theorem validEncAt_mem_FP (sp : Polynomial ℕ) {offU pU : List Bool → List Bool}
    (ho : offU ∈ FP) (hp : pU ∈ FP)
    :
    (fun z => validEncAt tm sp (offU z) (pU z) z) ∈ FP :=
  validEnc_mem_FP (rulerOf_mem_FP (nvarP tm sp)) ho
    (rulerOf_mem_FP (C (Fintype.card tm.Q))) (rulerOf_mem_FP (stateGroupP tm))
    (rulerOf_mem_FP (tapeBlockP sp)) (rulerOf_mem_FP (headBlockP (k := k) sp))
    (rulerOf_mem_FP (horP sp)) (rulerOf_mem_FP (hor2P sp)) pairFst_mem_FP
    (rulerOf_mem_FP sp) (rulerOf_mem_FP (C (k + 1))) (rulerOf_mem_FP (headGroupP sp)) hp

open Polynomial in
/-- **A validity clause of the block at `offU`, encoded at the machine's sizes.** -/
theorem validEncAt_eq (sp : Polynomial ℕ) (offU : List Bool) (p : ℕ) (z : List Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T)
    (hcard : 0 < Fintype.card tm.Q)
    (hp : p < 1 + Fintype.card tm.Q * Fintype.card tm.Q + (k + 2) * tapeBlockSize T)
    (hoff : offU.length + configWidth tm T
      ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length)
        offU.length)[p]?).map DataEncode.bitstringEncode
      = some (validEncAt tm sp offU (List.replicate p true) z) := by
  have hnv : (rulerOf (nvarP tm sp) z).length
      = (nvarP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  have hql : (rulerOf (C (Fintype.card tm.Q)) z).length = Fintype.card tm.Q := by
    rw [rulerOf_length', eval_C]
  have hsql : (rulerOf (stateGroupP tm) z).length
      = 1 + Fintype.card tm.Q * Fintype.card tm.Q := by
    rw [rulerOf_length', stateGroupP_eval]
  have htbl : (rulerOf (tapeBlockP sp) z).length = tapeBlockSize T := by
    rw [rulerOf_length', tapeBlockP_eval, hT]
  have hhsl : (rulerOf (headGroupP sp) z).length = 1 + (T + 1) * (T + 1) := by
    rw [rulerOf_length', headGroupP_eval, hT]
  have hhdl : (rulerOf (headBlockP (k := k) sp) z).length = (k + 2) * (T + 1) := by
    rw [rulerOf_length', headBlockP_eval, hT]
  have hhorl : (rulerOf (horP sp) z).length = T + 1 := by
    rw [rulerOf_length', horP_eval, hT]
  have hhor2l : (rulerOf (hor2P sp) z).length = T + 2 := by
    rw [rulerOf_length', hor2P_eval, hT]
  have hlastl : (rulerOf (C (k + 1)) z).length = k + 1 := by rw [rulerOf_length', eval_C]
  have hSUl : (rulerOf sp z).length = sp.eval (pairFst z).length := rulerOf_length' _ _
  have hoffN : offU.length + configWidth tm T ≤ (rulerOf (nvarP tm sp) z).length := by
    rw [hnv]; exact hoff
  have htlt := tapeOfIdx_lt T (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
    (List.replicate p true) htbl (by rw [List.length_replicate, hsql]; exact hp)
  have htape : (tapeOfIdx (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
      (List.replicate p true)).length
      = ((tapeSlotEquiv k).symm ⟨_, htlt⟩).index.val := by
    rw [tapeSlotEquiv_symm_index]
  have hposlt := cellPos_lt T (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
    (rulerOf (headGroupP sp) z) (List.replicate p true) htbl hhsl
  have hbHead : ∀ i, i < T + 1 →
      (headWireU offU (rulerOf (C (Fintype.card tm.Q)) z)
        (tapeOfIdx (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
          (List.replicate p true)) [] (rulerOf (horP sp) z)).length + i
        ≤ (rulerOf (nvarP tm sp) z).length := fun i hi =>
    headWire_add_le tm T offU.length _ ((tapeSlotEquiv k).symm ⟨_, htlt⟩) i hi rfl hql
      htape hhorl hoffN
  refine validEnc_eq tm T _ offU _ _ _ _ _ _ _ _ _ _ (sp.eval (pairFst z).length) p
    hsql htbl hhsl hhdl hhorl hhor2l hSUl hlastl hql hcard (by rw [hsql]; exact hp)
    (fun j hj => by
      have := card_le_configWidth tm T
      omega)
    hbHead
    (fun j hj => by
      refine hbHead j ?_
      rw [headCountU_length_eq (T := T) (pairFst z) (rulerOf sp z) _ (rulerOf (C (k + 1)) z)
        (rulerOf (horP sp) z) ((tapeSlotEquiv k).symm ⟨_, htlt⟩) htape hlastl hhorl] at hj
      omega)
    ?_
    (fun j hj =>
      cellWire_add_le tm T offU.length _ ((tapeSlotEquiv k).symm ⟨_, htlt⟩)
        ⟨_, hposlt⟩ Γ.zero j (by
          simp only [show (symbolIndex Γ.zero).val = 0 from rfl]
          omega) rfl hql hhdl htape rfl hhor2l rfl hoffN)
  · intro j hj
    have hstart : (symStartU (pairFst z) (rulerOf sp z)
        (tapeOfIdx (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
          (List.replicate p true)) (rulerOf (C (k + 1)) z)
        (cellPos (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
          (rulerOf (headGroupP sp) z) (List.replicate p true))).length
        = symStart T (pairFst z) (sp.eval (pairFst z).length)
          ((tapeSlotEquiv k).symm ⟨_, htlt⟩) ⟨_, hposlt⟩ := by
      rw [symStartU_length_eq (T := T) (pairFst z) (rulerOf sp z) _
        (rulerOf (C (k + 1)) z) _ ((tapeSlotEquiv k).symm ⟨_, htlt⟩) ⟨_, hposlt⟩ htape
        hlastl rfl, hSUl]
    have hcount : (symCountU (rulerOf sp z)
        (tapeOfIdx (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
          (List.replicate p true)) (rulerOf (C (k + 1)) z)
        (cellPos (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
          (rulerOf (headGroupP sp) z) (List.replicate p true))).length
        = (allowedSyms T (pairFst z) (sp.eval (pairFst z).length)
          ((tapeSlotEquiv k).symm ⟨_, htlt⟩) ⟨_, hposlt⟩).length := by
      rw [symCountU_length_eq (T := T) (x := pairFst z) (rulerOf sp z) _
        (rulerOf (C (k + 1)) z) _ ((tapeSlotEquiv k).symm ⟨_, htlt⟩) ⟨_, hposlt⟩ htape
        hlastl rfl, hSUl]
    have hlt4 := symStart_add_allowedSyms_le T (pairFst z)
      (sp.eval (pairFst z).length) ((tapeSlotEquiv k).symm ⟨_, htlt⟩) ⟨_, hposlt⟩
    have hs4 := symStart_lt T (pairFst z) (sp.eval (pairFst z).length)
      ((tapeSlotEquiv k).symm ⟨_, htlt⟩) ⟨_, hposlt⟩
    rw [hcount] at hj
    refine cellWire_add_le tm T offU.length _ ((tapeSlotEquiv k).symm ⟨_, htlt⟩)
      ⟨_, hposlt⟩ (symbolList[symStart T (pairFst z) (sp.eval (pairFst z).length)
        ((tapeSlotEquiv k).symm ⟨_, htlt⟩) ⟨_, hposlt⟩]'(by
          rw [symbolList_length]; exact hs4)) j ?_ rfl hql hhdl htape rfl hhor2l ?_ hoffN
    · rw [symbolIndex_symbolList _ hs4]
      omega
    · rw [hstart, symbolIndex_symbolList _ hs4]

open Polynomial in
/-- The validity clauses of the first block, encoded. -/
theorem validEncAt_zero_eq (sp : Polynomial ℕ) (p : ℕ) (z : List Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T) (hcard : 0 < Fintype.card tm.Q)
    (hp : p < (validCountP tm sp).eval (pairFst z).length) :
    ((cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length) 0)[p]?).map
        DataEncode.bitstringEncode
      = some (validEncAt tm sp [] (List.replicate p true) z) := by
  have hvc : (validCountP tm sp).eval (pairFst z).length
      = 1 + Fintype.card tm.Q * Fintype.card tm.Q + (k + 2) * tapeBlockSize T := by
    rw [validCountP_eval tm sp _ (pairFst z) (sp.eval (pairFst z).length) 0,
      cfgValidC_length, hT]
  have h := validEncAt_eq tm T sp [] p z hT hcard (by rw [← hvc]; exact hp)
    (by
      rw [List.length_nil, Nat.zero_add, ← hT, ← widthP_eval]
      exact widthP_le_nvarP tm sp _)
  rw [List.length_nil] at h
  exact h

open Polynomial in
/-- The validity clauses of the second block, encoded. -/
theorem validEncAt_bStart_eq (sp : Polynomial ℕ) (p : ℕ) (z : List Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T) (hcard : 0 < Fintype.card tm.Q)
    (hp : p < (validCountP tm sp).eval (pairFst z).length) :
    ((cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length)
        (flatLayoutOf tm sp (pairFst z)).bStart)[p]?).map DataEncode.bitstringEncode
      = some (validEncAt tm sp (rulerOf (bStartP tm sp) z) (List.replicate p true) z) := by
  have hvc : (validCountP tm sp).eval (pairFst z).length
      = 1 + Fintype.card tm.Q * Fintype.card tm.Q + (k + 2) * tapeBlockSize T := by
    rw [validCountP_eval tm sp _ (pairFst z) (sp.eval (pairFst z).length) 0,
      cfgValidC_length, hT]
  have hb : (rulerOf (bStartP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).bStart := by
    rw [rulerOf_length', bStartP_eval]
  have h := validEncAt_eq tm T sp (rulerOf (bStartP tm sp) z) p z hT hcard
    (by rw [← hvc]; exact hp)
    (by
      rw [hb, FlatLayout.bStart, flatLayoutOf_W, ← hT, ← widthP_eval]
      have := twoWidthP_le_nvarP tm sp (pairFst z).length
      rw [twoWidthP] at this
      simp only [eval_mul, eval_C] at this
      omega)
  rw [hb] at h
  exact h

/-! ## A level's offsets at the machine's sizes -/

open Polynomial in
/-- The start of level `jU`. -/
noncomputable def levMidU (sp : Polynomial ℕ) (jU z : List Bool) : List Bool :=
  levOffU (rulerOf (twoWidthP tm sp + C 1) z) (rulerOf (levelSizeP tm sp) z) jU []

open Polynomial in
/-- A block inside level `jU`, at offset `c` blocks of width `W`. -/
noncomputable def levBlkU (sp : Polynomial ℕ) (c : ℕ) (jU z : List Bool) : List Bool :=
  levOffU (rulerOf (twoWidthP tm sp + C 1) z) (rulerOf (levelSizeP tm sp) z) jU
    (rulerOf (C c * widthP tm sp) z)

open Polynomial in
/-- The chain bit before level `jU`. -/
noncomputable def levYU (sp : Polynomial ℕ) (jU z : List Bool) : List Bool :=
  levOffU (rulerOf (twoWidthP tm sp) z) (rulerOf (levelSizeP tm sp) z) jU []

open Polynomial in
/-- The chain bit after level `jU`. -/
noncomputable def levYSuccU (sp : Polynomial ℕ) (jU z : List Bool) : List Bool :=
  levOffU (rulerOf (twoWidthP tm sp) z) (rulerOf (levelSizeP tm sp) z) jU
    (rulerOf (levelSizeP tm sp) z)

open Polynomial in
/-- The left endpoint of level `jU`. -/
noncomputable def levLeftU (sp : Polynomial ℕ) (jU z : List Bool) : List Bool :=
  ifEqLen jU [] []
    (levOffU (rulerOf (twoWidthP tm sp + C 1) z) (rulerOf (levelSizeP tm sp) z)
      (dropOne jU) (rulerOf (widthP tm sp) z))

open Polynomial in
/-- The right endpoint of level `jU`. -/
noncomputable def levRightU (sp : Polynomial ℕ) (jU z : List Bool) : List Bool :=
  ifEqLen jU [] (rulerOf (widthP tm sp) z)
    (levOffU (rulerOf (twoWidthP tm sp + C 1) z) (rulerOf (levelSizeP tm sp) z)
      (dropOne jU) (rulerOf (twoWidthP tm sp) z))

open Polynomial in
theorem levMidU_length (sp : Polynomial ℕ) (jU z : List Bool) :
    (levMidU tm sp jU z).length = (flatLayoutOf tm sp (pairFst z)).mid jU.length := by
  rw [levMidU, levOffU_length, FlatLayout.mid, FlatLayout.levStart, FlatLayout.levelSize,
    flatLayoutOf_W]
  simp only [rulerOf_length', twoWidthP, levelSizeP, eval_add, eval_mul, eval_C,
    List.length_nil]
  ring

open Polynomial in
theorem levBlkU_length (sp : Polynomial ℕ) (c : ℕ) (jU z : List Bool) :
    (levBlkU tm sp c jU z).length
      = (flatLayoutOf tm sp (pairFst z)).levStart jU.length
        + c * (flatLayoutOf tm sp (pairFst z)).W := by
  rw [levBlkU, levOffU_length, FlatLayout.levStart, FlatLayout.levelSize, flatLayoutOf_W]
  simp only [rulerOf_length', twoWidthP, levelSizeP, eval_add, eval_mul, eval_C]
  ring

open Polynomial in
theorem levYU_length (sp : Polynomial ℕ) (jU z : List Bool) :
    (levYU tm sp jU z).length = (flatLayoutOf tm sp (pairFst z)).yAt jU.length := by
  rw [levYU, levOffU_length, FlatLayout.yAt, flatLayoutOf_W]
  rcases Nat.eq_zero_or_pos jU.length with h | h
  · rw [if_pos h, h, FlatLayout.y0, flatLayoutOf_W]
    simp only [rulerOf_length', twoWidthP, levelSizeP, eval_add, eval_mul, eval_C,
      List.length_nil]
    ring
  · rw [if_neg (by omega), FlatLayout.levStart, FlatLayout.levelSize, flatLayoutOf_W]
    simp only [rulerOf_length', twoWidthP, levelSizeP, eval_add, eval_mul, eval_C,
      List.length_nil]
    have hj : jU.length - 1 + 1 = jU.length := by omega
    have hexp : (7 * (widthP tm sp).eval (pairFst z).length + 1) * jU.length
        = (7 * (widthP tm sp).eval (pairFst z).length + 1) * (jU.length - 1)
          + (7 * (widthP tm sp).eval (pairFst z).length + 1) := by
      conv_lhs => rw [← hj]
      ring
    omega

open Polynomial in
theorem levYSuccU_length (sp : Polynomial ℕ) (jU z : List Bool) :
    (levYSuccU tm sp jU z).length
      = (flatLayoutOf tm sp (pairFst z)).yAt (jU.length + 1) := by
  rw [levYSuccU, levOffU_length, FlatLayout.yAt, if_neg (by omega), FlatLayout.levStart,
    FlatLayout.levelSize, flatLayoutOf_W]
  simp only [rulerOf_length', twoWidthP, levelSizeP, eval_add, eval_mul, eval_C,
    Nat.add_sub_cancel]
  ring

open Polynomial in
theorem levLeftU_length (sp : Polynomial ℕ) (jU z : List Bool) :
    (levLeftU tm sp jU z).length
      = (flatLayoutOf tm sp (pairFst z)).leftOf jU.length := by
  rw [levLeftU, FlatLayout.leftOf]
  rcases Nat.eq_zero_or_pos jU.length with h | h
  · rw [ifEqLen_pos (by rw [h]; rfl), if_pos h, List.length_nil]
  · rw [ifEqLen_neg (by simp only [List.length_nil]; omega), if_neg (by omega), levOffU_length,
      FlatLayout.uBlk, FlatLayout.levStart, FlatLayout.levelSize, flatLayoutOf_W]
    simp only [rulerOf_length', twoWidthP, levelSizeP, eval_add, eval_mul, eval_C, dropOne,
      List.length_drop]
    ring

open Polynomial in
theorem levRightU_length (sp : Polynomial ℕ) (jU z : List Bool) :
    (levRightU tm sp jU z).length
      = (flatLayoutOf tm sp (pairFst z)).rightOf jU.length := by
  rw [levRightU, FlatLayout.rightOf]
  rcases Nat.eq_zero_or_pos jU.length with h | h
  · rw [ifEqLen_pos (by rw [h]; rfl), if_pos h, FlatLayout.bStart, flatLayoutOf_W,
      rulerOf_length']
  · rw [ifEqLen_neg (by simp only [List.length_nil]; omega), if_neg (by omega), levOffU_length,
      FlatLayout.vBlk, FlatLayout.levStart, FlatLayout.levelSize, flatLayoutOf_W]
    simp only [rulerOf_length', twoWidthP, levelSizeP, eval_add, eval_mul, eval_C, dropOne,
      List.length_drop]
    ring

open Polynomial in
theorem levMidU_mem_FP (sp : Polynomial ℕ) {jU : List Bool → List Bool} (hj : jU ∈ FP) :
    (fun z => levMidU tm sp (jU z) z) ∈ FP :=
  levOffU_mem_FP (rulerOf_mem_FP _) (rulerOf_mem_FP _) hj (constFn_mem_FP [])

open Polynomial in
theorem levBlkU_mem_FP (sp : Polynomial ℕ) (c : ℕ) {jU : List Bool → List Bool}
    (hj : jU ∈ FP) : (fun z => levBlkU tm sp c (jU z) z) ∈ FP :=
  levOffU_mem_FP (rulerOf_mem_FP _) (rulerOf_mem_FP _) hj (rulerOf_mem_FP _)

open Polynomial in
theorem levYU_mem_FP (sp : Polynomial ℕ) {jU : List Bool → List Bool} (hj : jU ∈ FP) :
    (fun z => levYU tm sp (jU z) z) ∈ FP :=
  levOffU_mem_FP (rulerOf_mem_FP _) (rulerOf_mem_FP _) hj (constFn_mem_FP [])

open Polynomial in
theorem levYSuccU_mem_FP (sp : Polynomial ℕ) {jU : List Bool → List Bool} (hj : jU ∈ FP) :
    (fun z => levYSuccU tm sp (jU z) z) ∈ FP :=
  levOffU_mem_FP (rulerOf_mem_FP _) (rulerOf_mem_FP _) hj (rulerOf_mem_FP _)

open Polynomial in
theorem levLeftU_mem_FP (sp : Polynomial ℕ) {jU : List Bool → List Bool} (hj : jU ∈ FP) :
    (fun z => levLeftU tm sp (jU z) z) ∈ FP :=
  ifEqLen_mem_FP hj (constFn_mem_FP []) (constFn_mem_FP [])
    (levOffU_mem_FP (rulerOf_mem_FP _) (rulerOf_mem_FP _) (dropOneFn_mem_FP hj)
      (rulerOf_mem_FP _))

open Polynomial in
theorem levRightU_mem_FP (sp : Polynomial ℕ) {jU : List Bool → List Bool} (hj : jU ∈ FP) :
    (fun z => levRightU tm sp (jU z) z) ∈ FP :=
  ifEqLen_mem_FP hj (constFn_mem_FP []) (rulerOf_mem_FP _)
    (levOffU_mem_FP (rulerOf_mem_FP _) (rulerOf_mem_FP _) (dropOneFn_mem_FP hj)
      (rulerOf_mem_FP _))

/-! ## A level's clauses at the machine's sizes -/

open Polynomial in
/-- The level a matrix index names, clamped to the number of levels so that every offset the
emitter builds stays inside the variable count. -/
noncomputable def levIdxAt (sp : Polynomial ℕ) (jU z : List Bool) : List Bool :=
  jU.take (rulerOf (levelsP tm sp) z).length

open Polynomial in
theorem levIdxAt_le (sp : Polynomial ℕ) (jU z : List Bool) :
    (levIdxAt tm sp jU z).length ≤ (levelsP tm sp).eval (pairFst z).length := by
  rw [levIdxAt, List.length_take, rulerOf, polyRuler_length]
  omega

open Polynomial in
theorem levIdxAt_mem_FP (sp : Polynomial ℕ) {jU : List Bool → List Bool} (hj : jU ∈ FP) :
    (fun z => levIdxAt tm sp (jU z) z) ∈ FP :=
  Cobham.takeLenFn_mem_FP (rulerOf_mem_FP _) hj

open Polynomial in
/-- One clause of level `jU`, with every size supplied by the layout's polynomials. -/
noncomputable def levelEncAt (sp : Polynomial ℕ) (jU pU z : List Bool) : List Bool :=
  levelEnc (rulerOf (nvarP tm sp) z) (rulerOf (C (Fintype.card tm.Q)) z)
    (rulerOf (stateGroupP tm) z) (rulerOf (tapeBlockP sp) z)
    (rulerOf (headBlockP (k := k) sp) z) (rulerOf (horP sp) z) (rulerOf (hor2P sp) z)
    (pairFst z) (rulerOf sp z) (rulerOf (C (k + 1)) z) (rulerOf (headGroupP sp) z)
    (rulerOf (validCountP tm sp) z) (rulerOf (C 4 * widthP tm sp) z)
    (levYU tm sp (levIdxAt tm sp jU z) z) (levYSuccU tm sp (levIdxAt tm sp jU z) z)
    (rulerOf (widthP tm sp) z) (levMidU tm sp (levIdxAt tm sp jU z) z)
    (levBlkU tm sp 1 (levIdxAt tm sp jU z) z) (levBlkU tm sp 2 (levIdxAt tm sp jU z) z)
    (levLeftU tm sp (levIdxAt tm sp jU z) z) (levRightU tm sp (levIdxAt tm sp jU z) z)
    (levBlkU tm sp 3 (levIdxAt tm sp jU z) z) (levBlkU tm sp 4 (levIdxAt tm sp jU z) z)
    (levBlkU tm sp 5 (levIdxAt tm sp jU z) z) (levBlkU tm sp 6 (levIdxAt tm sp jU z) z)
    pU

open Polynomial in
theorem levelEncAt_mem_FP (sp : Polynomial ℕ) {jU pU : List Bool → List Bool}
    (hj : jU ∈ FP) (hp : pU ∈ FP) :
    (fun z => levelEncAt tm sp (jU z) (pU z) z) ∈ FP := by
  have hidx : (fun z => levIdxAt tm sp (jU z) z) ∈ FP := levIdxAt_mem_FP tm sp hj
  exact levelEnc_mem_FP (rulerOf_mem_FP (nvarP tm sp))
    (rulerOf_mem_FP (C (Fintype.card tm.Q))) (rulerOf_mem_FP (stateGroupP tm))
    (rulerOf_mem_FP (tapeBlockP sp)) (rulerOf_mem_FP (headBlockP (k := k) sp))
    (rulerOf_mem_FP (horP sp)) (rulerOf_mem_FP (hor2P sp)) pairFst_mem_FP
    (rulerOf_mem_FP sp) (rulerOf_mem_FP (C (k + 1))) (rulerOf_mem_FP (headGroupP sp))
    (rulerOf_mem_FP (validCountP tm sp)) (rulerOf_mem_FP (C 4 * widthP tm sp))
    (levYU_mem_FP tm sp hidx) (levYSuccU_mem_FP tm sp hidx)
    (rulerOf_mem_FP (widthP tm sp)) (levMidU_mem_FP tm sp hidx)
    (levBlkU_mem_FP tm sp 1 hidx) (levBlkU_mem_FP tm sp 2 hidx)
    (levLeftU_mem_FP tm sp hidx) (levRightU_mem_FP tm sp hidx)
    (levBlkU_mem_FP tm sp 3 hidx) (levBlkU_mem_FP tm sp 4 hidx)
    (levBlkU_mem_FP tm sp 5 hidx) (levBlkU_mem_FP tm sp 6 hidx) hp

/-! ## A view's clause as a term -/

open Polynomial in
/-- One view clause, encoded: the literals of `viewLitEnc`, emitted by the nested list
emitter. -/
noncomputable def viewClauseEncF (sp : Polynomial ℕ)
    (uU vU sU caseU viewU forcedU bU : List Bool → List Bool) (z : List Bool) : List Bool :=
  emitListAt
    (fun y => viewLitEnc tm (rulerOf (nvarP tm sp) (pairFst y)) (uU (pairFst y))
      (vU (pairFst y)) (sU (pairFst y)) (rulerOf (C (Fintype.card tm.Q)) (pairFst y))
      (rulerOf (headBlockP (k := k) sp) (pairFst y)) (rulerOf (horP sp) (pairFst y))
      (rulerOf (hor2P sp) (pairFst y)) (caseU (pairFst y)) (viewU (pairFst y))
      (forcedU (pairFst y)) (bU (pairFst y)) (rulerOf (tapesP (k := k)) (pairFst y))
      ((pairSnd y).take (rulerOf (C 2 * tapesP (k := k) + C 3) (pairFst y)).length))
    (rulerOf (C 2 * tapesP (k := k) + C 3) z) z

open Polynomial in
theorem viewClauseEncF_mem_FP (sp : Polynomial ℕ)
    {uU vU sU caseU viewU forcedU bU : List Bool → List Bool}
    (hu : uU ∈ FP) (hv : vU ∈ FP) (hs : sU ∈ FP) (hcase : caseU ∈ FP) (hview : viewU ∈ FP)
    (hforced : forcedU ∈ FP) (hb : bU ∈ FP)
    {C₀ : ℕ} (hC : ∀ y, (caseU (pairFst y)).length ≤ C₀)
    {E : ℕ} (hE : ∀ y, (divC 2 (dropOne (dropOne ((pairSnd y).take
      (rulerOf (C 2 * tapesP (k := k) + C 3) (pairFst y)).length)))).length ≤ E)
    {K : ℕ} (hK : ∀ y,
      (pair (caseU (pairFst y)) (divC 2 (dropOne (dropOne ((pairSnd y).take
        (rulerOf (C 2 * tapesP (k := k) + C 3) (pairFst y)).length))))).length ≤ K)
    {width : List Bool → List Bool} (hwd : width ∈ FP)
    (hbound : ∀ y, (rulerOf (horP sp) (pairFst y)).length ^ E
      + 2 * (rulerOf (horP sp) (pairFst y)).length + 4 ≤ (width y).length) :
    (fun z => viewClauseEncF tm sp uU vU sU caseU viewU forcedU bU z) ∈ FP := by
  have hproj : ∀ {f : List Bool → List Bool}, f ∈ FP → (fun y => f (pairFst y)) ∈ FP :=
    fun hf => mem_FP_of_eq (mem_FP_comp pairFst_mem_FP hf) fun _ => rfl
  have hrul : ∀ q : Polynomial ℕ, (fun y => rulerOf q (pairFst y)) ∈ FP :=
    fun q => hproj (rulerOf_mem_FP q)
  exact emitListAt_mem_FP
    (viewLitEnc_mem_FP tm (hrul (nvarP tm sp)) (hproj hu) (hproj hv) (hproj hs)
      (hrul (C (Fintype.card tm.Q))) (hrul (headBlockP (k := k) sp)) (hrul (horP sp))
      (hrul (hor2P sp)) (hproj hcase) (hproj hview) (hproj hforced) (hproj hb)
      (hrul (tapesP (k := k)))
      (Cobham.takeLenFn_mem_FP (hrul (C 2 * tapesP (k := k) + C 3)) Cobham.sndBlock_mem_FP)
      hC hE hK hwd hbound)
    (rulerOf_mem_FP _) id_mem_FP

open Polynomial in
/-- A width that dominates every table lookup inside a view's literals. -/
noncomputable def viewWidthP (sp : Polynomial ℕ) : Polynomial ℕ :=
  horP sp ^ (k + 3) + C 2 * horP sp + C 4

open Polynomial in
/-- The membership of `viewClauseEncF`, with every side condition discharged: the clamp on
the literal index bounds the tables uniformly. -/
theorem viewClauseEncF_mem_FP' (sp : Polynomial ℕ)
    {uU vU sU caseU viewU forcedU bU : List Bool → List Bool}
    (hu : uU ∈ FP) (hv : vU ∈ FP) (hs : sU ∈ FP) (hcase : caseU ∈ FP) (hview : viewU ∈ FP)
    (hforced : forcedU ∈ FP) (hb : bU ∈ FP)
    {C₀ : ℕ} (hC : ∀ y, (caseU (pairFst y)).length ≤ C₀) :
    (fun z => viewClauseEncF tm sp uU vU sU caseU viewU forcedU bU z) ∈ FP := by
  have hlen : ∀ y : List Bool, (divC 2 (dropOne (dropOne ((pairSnd y).take
      (rulerOf (C 2 * tapesP (k := k) + C 3) (pairFst y)).length)))).length ≤ k + 3 := by
    intro y
    rw [divC_eq (by norm_num), List.length_replicate, dropOne, dropOne, List.length_drop,
      List.length_drop, List.length_take, rulerOf_length']
    simp only [tapesP, eval_add, eval_mul, eval_C]
    omega
  have hwd : (fun y => rulerOf (viewWidthP (k := k) sp) (pairFst y)) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp pairFst_mem_FP (rulerOf_mem_FP _)) fun _ => rfl
  have hbound : ∀ y : List Bool, (rulerOf (horP sp) (pairFst y)).length ^ (k + 3)
      + 2 * (rulerOf (horP sp) (pairFst y)).length + 4
      ≤ (rulerOf (viewWidthP (k := k) sp) (pairFst y)).length := by
    intro y
    rw [rulerOf_length', rulerOf_length', viewWidthP]
    simp only [eval_add, eval_mul, eval_pow, eval_C]
    omega
  exact viewClauseEncF_mem_FP tm sp hu hv hs hcase hview hforced hb hC hlen
    (K := 2 * C₀ + 2 + (k + 3))
    (fun y => by rw [pair_length]; have := hC y; have := hlen y; omega) hwd hbound

private theorem getElem_of_getElem? {α : Type} {l : List α} {j : ℕ} {x : α}
    (h : l[j]? = some x) (hj : j < l.length) : l[j]'hj = x := by
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

open Polynomial in
/-- **A view clause, encoded**: the emitted literals are exactly `forceAtom`'s. -/
theorem viewClauseEncF_eq (sp : Polynomial ℕ)
    (uU vU sU caseU viewU forcedU bU : List Bool → List Bool) (z : List Bool)
    (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (a : ConfigAtom tm T) (b : Bool)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (caseU z).length < (caseList tm).length)
    (hc : (caseList tm)[(caseU z).length]'hcase = c)
    (hview : (viewU z).length = i.val)
    (hforced : (forcedU z).length = configIndex tm T a)
    (hbnil : (bU z) = [] → b = false) (hbne : (bU z) ≠ [] → b = true)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    viewClauseEncF tm sp uU vU sU caseU viewU forcedU bU z
      = DataEncode.bitstringEncode
          (forceAtom tm T (uU z).length (vU z).length (sU z).length
            (c, headTupleOf k T i) a b) := by
  have hnv : (rulerOf (nvarP tm sp) z).length
      = (nvarP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  have hqq : (rulerOf (C (Fintype.card tm.Q)) z).length = Fintype.card tm.Q := by
    rw [rulerOf_length', eval_C]
  have hhor : (rulerOf (horP sp) z).length = T + 1 := by rw [rulerOf_length', hT]
  have hhor2 : (rulerOf (hor2P sp) z).length = T + 2 := by rw [rulerOf_length', hT2]
  have hhdl : (rulerOf (headBlockP (k := k) sp) z).length = (k + 2) * (T + 1) := by
    rw [rulerOf_length', hhd]
  have htapes : (rulerOf (tapesP (k := k)) z).length = k + 2 := by
    rw [rulerOf_length', tapesP, eval_C]
  have hwire : ∀ atom : ConfigAtom tm T,
      (uU z).length + configIndex tm T atom ≤ (rulerOf (nvarP tm sp) z).length := by
    intro atom
    have := configIndex_lt tm T atom
    rw [hnv]
    omega
  have hwirev : ∀ atom : ConfigAtom tm T,
      (vU z).length + configIndex tm T atom ≤ (rulerOf (nvarP tm sp) z).length := by
    intro atom
    have := configIndex_lt tm T atom
    rw [hnv]
    omega
  refine emitListAt_eq' _ _ _ (by
    rw [forceAtom_length, rulerOf_length']
    simp only [tapesP, eval_add, eval_mul, eval_C]) (fun j hj => ?_)
  rw [forceAtom_length] at hj
  rw [pairFst_pair, pairSnd_pair]
  have hjt : ((List.replicate j true).take (rulerOf (C 2 * tapesP (k := k) + C 3) z).length)
      = List.replicate j true := by
    refine List.take_of_length_le ?_
    rw [List.length_replicate, rulerOf_length']
    simp only [tapesP, eval_add, eval_mul, eval_C]
    omega
  rw [hjt]
  have hjlen : (List.replicate j true).length = j := List.length_replicate
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have hva := getElem_of_getElem? (forceAtom_getElem?_zero tm T (uU z).length
      (vU z).length (sU z).length (c, headTupleOf k T i) a b)
      (by rw [forceAtom_length]; omega)
    rw [hva, List.replicate_zero,
      viewLitEnc_zero_eq (tm := tm) (c := c) (hlt := hcase) (hc := hc)
        (hs := by rw [hnv]; exact hs)]
  · rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj1 : j = 1 := by omega
      subst hj1
      have hva := getElem_of_getElem? (forceAtom_getElem?_one tm T (uU z).length
        (vU z).length (sU z).length (c, headTupleOf k T i) a b)
        (by rw [forceAtom_length]; omega)
      rw [hva, viewLitEnc_one_eq (tm := tm) (c := c) (hlt := hcase) (hc := hc)
        (hj := by rw [hjlen]) (hu := by exact hwire (ConfigAtom.state c.state))]
      rfl
    · rcases Nat.lt_or_ge (j - 2) (2 * (k + 2)) with hjt2 | hjt2
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
        have hm : m < 2 * (k + 2) := by omega
        have hidx : m / 2 < k + 2 := Nat.div_lt_of_lt_mul (by omega)
        have hgt : (tapeList k)[m / 2]? = some ((tapeSlotEquiv k).symm ⟨m / 2, hidx⟩) :=
          tapeList_getElem? _ hidx
        have htapeval : (m + 2 - 2) / 2
            = ((tapeSlotEquiv k).symm ⟨m / 2, hidx⟩).index.val := by
          rw [tapeSlotEquiv_symm_index]
          simp
        have hltT : (List.replicate (m + 2) true).length - 2
            < 2 * (rulerOf (tapesP (k := k)) z).length := by
          rw [hjlen, htapes]
          omega
        have hfa := forceAtom_getElem?_tape tm T (uU z).length (vU z).length (sU z).length
          (c, headTupleOf k T i) a b m hm
        rw [hgt, Option.map_some] at hfa
        have hval := getElem_of_getElem? hfa (by rw [forceAtom_length]; omega)
        rcases Nat.even_or_odd m with he | ho
        · rw [Nat.even_iff] at he
          have heven : (m + 2 - 2) % 2 = 0 := by omega
          rw [hval, if_pos (by omega),
            viewLitEnc_tape_head_eq (tm := tm) (T := T) (i := i)
              (tape := (tapeSlotEquiv k).symm ⟨m / 2, hidx⟩)
              (hj0 := by rw [hjlen]; omega) (hj1 := by rw [hjlen]; omega)
              (hlt := hltT)
              (heven := by rw [hjlen]; exact heven)
              (htape := by rw [hjlen]; exact htapeval) (hq := hqq) (hhor := hhor)
              (hview := hview)
              (hb := by exact hwire (ConfigAtom.head _ (headTupleOf k T i _)))]
        · rw [Nat.odd_iff] at ho
          have hodd : (m + 2 - 2) % 2 = 1 := by omega
          rw [hval, if_neg (by omega),
            viewLitEnc_tape_cell_eq (tm := tm) (T := T) (i := i)
              (tape := (tapeSlotEquiv k).symm ⟨m / 2, hidx⟩) (c := c)
              (pos := headCellPosition (headTupleOf k T i
                ((tapeSlotEquiv k).symm ⟨m / 2, hidx⟩)))
              (hj0 := by rw [hjlen]; omega) (hj1 := by rw [hjlen]; omega)
              (hlt := hltT)
              (hodd := by rw [hjlen]; exact hodd)
              (htape := by rw [hjlen]; exact htapeval) (hq := hqq) (hhd := hhdl)
              (hhor := hhor) (hhor2 := hhor2) (hview := hview) (hcase := hcase) (hc := hc)
              (hpos := rfl) (hb := by exact hwire (ConfigAtom.cell _ _ _))]
      · have hjeq : j = 2 * (k + 2) + 2 := by omega
        subst hjeq
        have hlast := getElem_of_getElem? (forceAtom_getElem?_last tm T (uU z).length
          (vU z).length (sU z).length (c, headTupleOf k T i) a b)
          (by rw [forceAtom_length]; omega)
        have hlenv : ((vU z) ++ (forcedU z)).length
            = configWire tm T (vU z).length a := by
          rw [List.length_append, hforced, configWire]
        rw [hlast, viewLitEnc_last_eq (tm := tm) (hj0 := by rw [hjlen]; omega)
          (hj1 := by rw [hjlen]; omega) (hge := by rw [hjlen, htapes]; omega)]
        rcases hbb : bU z with _ | ⟨d, ds⟩
        · rw [litEnc_neg (by rw [hlenv]; exact hwirev a), hlenv,
            hbnil (by simp [hbb])]
        · rw [litEnc_pos (by simp) (by rw [hlenv]; exact hwirev a), hlenv,
            hbne (by simp [hbb])]

open Polynomial in
/-- **A view clause, encoded**, with the forced bit given as a decidable proposition — the
shape `stepClausesView` produces. -/
theorem viewClauseEncF_decide_eq (sp : Polynomial ℕ)
    (uU vU sU caseU viewU forcedU bU : List Bool → List Bool) (z : List Bool)
    (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (a : ConfigAtom tm T)
    (P : Prop) [Decidable P]
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (caseU z).length < (caseList tm).length)
    (hc : (caseList tm)[(caseU z).length]'hcase = c)
    (hview : (viewU z).length = i.val)
    (hforced : (forcedU z).length = configIndex tm T a)
    (hbit : (bU z) ≠ [] ↔ P)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    viewClauseEncF tm sp uU vU sU caseU viewU forcedU bU z
      = DataEncode.bitstringEncode
          (forceAtom tm T (uU z).length (vU z).length (sU z).length
            (c, headTupleOf k T i) a (decide P)) :=
  viewClauseEncF_eq tm T sp uU vU sU caseU viewU forcedU bU z c i a (decide P) hT hT2 hhd
    hcase hc hview hforced
    (fun hnil => by
      have : ¬ P := fun hp => (hbit.mpr hp) hnil
      simp [this])
    (fun hne => by simp [hbit.mp hne]) hs hu hv

open Polynomial in
/-- **The view clause at a state index, encoded.** -/
theorem viewClauseEncF_state_value (sp : Polynomial ℕ)
    (uU vU sU caseU viewU forcedU bU : List Bool → List Bool) (z : List Bool)
    (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (q : ℕ)
    (hq : q < Fintype.card tm.Q)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (caseU z).length < (caseList tm).length)
    (hc : (caseList tm)[(caseU z).length]'hcase = c)
    (hview : (viewU z).length = i.val)
    (hforcedlen : (forcedU z).length = q)
    (hbit : (bU z) ≠ []
      ↔ newStateOfCase tm c = (stateList tm)[q]'(by rw [stateList_length]; exact hq))
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClausesView tm T (uU z).length (vU z).length (sU z).length
        (c, headTupleOf k T i))[q]?).map DataEncode.bitstringEncode
      = some (viewClauseEncF tm sp uU vU sU caseU viewU forcedU bU z) := by
  have hqlt : q < (stateList tm).length := by rw [stateList_length]; exact hq
  have hst : stateIndex tm ((stateList tm)[q]'hqlt) = q := stateIndex_stateList tm q hq
  rw [stepClausesView_getElem?_state tm T (uU z).length (vU z).length (sU z).length _ q hq,
    List.getElem?_eq_getElem hqlt, Option.map_some, Option.map_some,
    viewClauseEncF_decide_eq tm T sp uU vU sU caseU viewU forcedU bU z c i
      (ConfigAtom.state ((stateList tm)[q]'hqlt))
      (newStateV tm T (c, headTupleOf k T i) = (stateList tm)[q]'hqlt) hT hT2 hhd hcase hc
      hview (by rw [configIndex_state, hst]; exact hforcedlen)
      (by rw [newStateV_eq_ofCase]; exact hbit) hs hu hv]

open Polynomial in
/-- **The view clause at a head index, encoded.** -/
theorem viewClauseEncF_head_value (sp : Polynomial ℕ)
    (uU vU sU caseU viewU forcedU bU : List Bool → List Bool) (z : List Bool)
    (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (q : ℕ)
    (tape : TapeSlot k) (p : Fin (T + 1))
    (h₁ : Fintype.card tm.Q ≤ q) (h₂ : q < Fintype.card tm.Q + (k + 2) * (T + 1))
    (htape : tape.index.val = (q - Fintype.card tm.Q) / (T + 1))
    (hp : p.val = (q - Fintype.card tm.Q) % (T + 1))
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (caseU z).length < (caseList tm).length)
    (hc : (caseList tm)[(caseU z).length]'hcase = c)
    (hview : (viewU z).length = i.val)
    (hforcedlen : (forcedU z).length = q)
    (hbit : (bU z) ≠ [] ↔ newHeadV tm T (c, headTupleOf k T i) tape = p.val)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClausesView tm T (uU z).length (vU z).length (sU z).length
        (c, headTupleOf k T i))[q]?).map DataEncode.bitstringEncode
      = some (viewClauseEncF tm sp uU vU sU caseU viewU forcedU bU z) := by
  have hdm := Nat.div_add_mod (q - Fintype.card tm.Q) (T + 1)
  have hcomm : (T + 1) * ((q - Fintype.card tm.Q) / (T + 1))
      = ((q - Fintype.card tm.Q) / (T + 1)) * (T + 1) := Nat.mul_comm _ _
  rw [stepClausesView_getElem?_head tm T (uU z).length (vU z).length (sU z).length _ q h₁ h₂,
    ← htape, tapeList_getElem?_index, Option.bind_some, List.getElem?_map, ← hp,
    finRange_getElem? _ _ p.isLt, Option.map_some, Option.map_some, Fin.eta,
    viewClauseEncF_decide_eq tm T sp uU vU sU caseU viewU forcedU bU z c i
      (ConfigAtom.head tape p)
      (newHeadV tm T (c, headTupleOf k T i) tape = p.val) hT hT2 hhd hcase hc hview
      (by rw [configIndex_head, htape, hp]; omega) hbit hs hu hv]

open Polynomial in
/-- **The view clause at a cell index, encoded.** -/
theorem viewClauseEncF_cell_value (sp : Polynomial ℕ)
    (uU vU sU caseU viewU forcedU bU : List Bool → List Bool) (z : List Bool)
    (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (q : ℕ)
    (tape : TapeSlot k) (m : ℕ) (hm : m < 4)
    (h₁ : Fintype.card tm.Q + (k + 2) * (T + 1) ≤ q)
    (h₂ : q < Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (htape : tape.index.val = (q - Fintype.card tm.Q - (k + 2) * (T + 1)) / 4)
    (hmv : m = (q - Fintype.card tm.Q - (k + 2) * (T + 1)) % 4)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (caseU z).length < (caseList tm).length)
    (hc : (caseList tm)[(caseU z).length]'hcase = c)
    (hview : (viewU z).length = i.val)
    (hforcedlen : (forcedU z).length
      = configIndex tm T (.cell tape (headCellPosition (headTupleOf k T i tape))
        (symbolList[m]'(by rw [symbolList_length]; exact hm))))
    (hbit : (bU z) ≠ []
      ↔ newSymV tm T (c, headTupleOf k T i) tape
        = symbolList[m]'(by rw [symbolList_length]; exact hm))
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClausesView tm T (uU z).length (vU z).length (sU z).length
        (c, headTupleOf k T i))[q]?).map DataEncode.bitstringEncode
      = some (viewClauseEncF tm sp uU vU sU caseU viewU forcedU bU z) := by
  rw [stepClausesView_getElem?_cell tm T (uU z).length (vU z).length (sU z).length _ q h₁ h₂,
    ← htape, tapeList_getElem?_index, Option.bind_some, List.getElem?_map, ← hmv,
    symbolList_getElem? _ hm, Option.map_some, Option.map_some,
    viewClauseEncF_decide_eq tm T sp uU vU sU caseU viewU forcedU bU z c i
      (ConfigAtom.cell tape (headCellPosition (headTupleOf k T i tape))
        (symbolList[m]'(by rw [symbolList_length]; exact hm)))
      (newSymV tm T (c, headTupleOf k T i) tape
        = symbolList[m]'(by rw [symbolList_length]; exact hm)) hT hT2 hhd hcase hc hview
      hforcedlen hbit hs hu hv]

/-! ## Decoding a step-clause index at the machine's sizes -/

open Polynomial in
/-- The view a step index names. -/
noncomputable def stepViewIdx (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  divFn2 (pair (rulerOf (viewClauseP tm sp) z) pU)

open Polynomial in
/-- The atom a step index names. -/
noncomputable def stepAtomIdx (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  modFn2 (pair (rulerOf (viewClauseP tm sp) z) pU)

open Polynomial in
/-- The transition case a step index names, clamped to the number of cases so that it is a
bounded key on every input. -/
noncomputable def stepCaseIdx (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  (divFn2 (pair (rulerOf (horP sp ^ (k + 2)) z) (stepViewIdx tm sp pU z))).take
    (rulerOf (C (Fintype.card (TransitionCase tm))) z).length

open Polynomial in
/-- The head tuple a step index names. -/
noncomputable def stepTupleIdx (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  modFn2 (pair (rulerOf (horP sp ^ (k + 2)) z) (stepViewIdx tm sp pU z))

open Polynomial in
theorem stepViewIdx_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => stepViewIdx tm sp (pU z) z) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP (rulerOf_mem_FP _) hp) divFn2_mem_FP)
    fun _ => rfl

open Polynomial in
theorem stepAtomIdx_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => stepAtomIdx tm sp (pU z) z) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP (rulerOf_mem_FP _) hp) modFn2_mem_FP)
    fun _ => rfl

open Polynomial in
theorem stepCaseIdx_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => stepCaseIdx tm sp (pU z) z) ∈ FP :=
  Cobham.takeLenFn_mem_FP (rulerOf_mem_FP _)
    (mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP (rulerOf_mem_FP _)
      (stepViewIdx_mem_FP tm sp hp)) divFn2_mem_FP) fun _ => rfl)

open Polynomial in
theorem stepCaseIdx_length_le (sp : Polynomial ℕ) (pU z : List Bool) :
    (stepCaseIdx tm sp pU z).length ≤ Fintype.card (TransitionCase tm) := by
  rw [stepCaseIdx, List.length_take, rulerOf_length', eval_C]
  omega

/-! ## The step index's decoders are bounded -/

open Polynomial in
theorem horP_eval_pos (sp : Polynomial ℕ) (n : ℕ) : 0 < (horP sp).eval n := by
  simp only [horP, horizonP, eval_add, eval_C, eval_X]
  omega

open Polynomial in
theorem viewClauseP_eval_pos (sp : Polynomial ℕ) (n : ℕ) :
    0 < (viewClauseP tm sp).eval n := by
  simp only [viewClauseP, eval_add, eval_mul, eval_C]
  omega

open Polynomial in
open Polynomial in
theorem stepViewIdx_length (sp : Polynomial ℕ) (pU z : List Bool) :
    (stepViewIdx tm sp pU z).length
      = pU.length / (viewClauseP tm sp).eval (pairFst z).length := by
  rw [stepViewIdx, divFn2_eq (by rw [rulerOf_length']; exact viewClauseP_eval_pos tm sp _),
    List.length_replicate, rulerOf_length']

open Polynomial in
theorem stepAtomIdx_length (sp : Polynomial ℕ) (pU z : List Bool) :
    (stepAtomIdx tm sp pU z).length
      = pU.length % (viewClauseP tm sp).eval (pairFst z).length := by
  rw [stepAtomIdx, modFn2_eq (by rw [rulerOf_length']; exact viewClauseP_eval_pos tm sp _),
    List.length_replicate, rulerOf_length']

open Polynomial in
theorem stepTupleIdx_length (sp : Polynomial ℕ) (pU z : List Bool) :
    (stepTupleIdx tm sp pU z).length
      = pU.length / (viewClauseP tm sp).eval (pairFst z).length
        % ((horP sp).eval (pairFst z).length) ^ (k + 2) := by
  have hpow : 0 < (rulerOf (horP sp ^ (k + 2)) z).length := by
    rw [rulerOf_length', eval_pow]
    exact Nat.pow_pos (horP_eval_pos sp _)
  rw [stepTupleIdx, modFn2_eq hpow, List.length_replicate, stepViewIdx_length]
  simp only [rulerOf_length', eval_pow]

open Polynomial in
theorem stepCaseIdx_length (sp : Polynomial ℕ) (pU z : List Bool) :
    (stepCaseIdx tm sp pU z).length
      = min (pU.length / (viewClauseP tm sp).eval (pairFst z).length
          / ((horP sp).eval (pairFst z).length) ^ (k + 2))
        (Fintype.card (TransitionCase tm)) := by
  have hpow : 0 < (rulerOf (horP sp ^ (k + 2)) z).length := by
    rw [rulerOf_length', eval_pow]
    exact Nat.pow_pos (horP_eval_pos sp _)
  rw [stepCaseIdx, List.length_take, divFn2_eq hpow, List.length_replicate,
    stepViewIdx_length]
  simp only [rulerOf_length', eval_C, eval_pow]
  exact Nat.min_comm _ _

/-- A step index's atom is smaller than a view's clause count. -/
theorem stepAtomIdx_length_lt (sp : Polynomial ℕ) (pU z : List Bool) :
    (stepAtomIdx tm sp pU z).length < (viewClauseP tm sp).eval (pairFst z).length := by
  have hb : 0 < (rulerOf (viewClauseP tm sp) z).length := by
    rw [rulerOf_length']; exact viewClauseP_eval_pos tm sp _
  rw [stepAtomIdx, modFn2_eq hb, List.length_replicate]
  have h := Nat.mod_lt pU.length hb
  simp only [rulerOf_length'] at h ⊢
  exact h

open Polynomial in
/-- The tape a step index's head atom names is one of finitely many. -/
theorem atHeadTape_stepAtom_le (sp : Polynomial ℕ) (pU z : List Bool) :
    (atHeadTape (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (horP sp) z)
      (stepAtomIdx tm sp pU z)).length ≤ 5 * k + 10 := by
  have hhor : 0 < (rulerOf (horP sp) z).length := by
    rw [rulerOf_length']; exact horP_eval_pos sp _
  rw [atHeadTape, divFn2_eq hhor, List.length_replicate, atRest, List.length_drop,
    rulerOf_length', eval_C]
  have hlt := stepAtomIdx_length_lt tm sp pU z
  simp only [viewClauseP, eval_add, eval_mul, eval_C] at hlt
  rw [← rulerOf_length' (horP sp) z] at hlt
  have hcomm : (k + 2) * (rulerOf (horP sp) z).length
      = (rulerOf (horP sp) z).length * (k + 2) := Nat.mul_comm _ _
  have hle : (stepAtomIdx tm sp pU z).length - Fintype.card tm.Q
      ≤ (rulerOf (horP sp) z).length * (k + 2) + 4 * (k + 2) := by omega
  calc ((stepAtomIdx tm sp pU z).length - Fintype.card tm.Q)
        / (rulerOf (horP sp) z).length
      ≤ ((rulerOf (horP sp) z).length * (k + 2) + 4 * (k + 2))
        / (rulerOf (horP sp) z).length := Nat.div_le_div_right hle
    _ = (k + 2) + 4 * (k + 2) / (rulerOf (horP sp) z).length := Nat.mul_add_div hhor _ _
    _ ≤ 5 * k + 10 := by
        have := Nat.div_le_self (4 * (k + 2)) (rulerOf (horP sp) z).length
        omega

open Polynomial in
/-- The tape a step index's cell atom names is one of finitely many. -/
theorem atCellTape_stepAtom_le (sp : Polynomial ℕ) (pU z : List Bool) :
    (atCellTape (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (horP sp) z)
      (rulerOf (tapesP (k := k)) z) (stepAtomIdx tm sp pU z)).length ≤ 5 * k + 10 := by
  rw [atCellTape, divC_eq (by norm_num), List.length_replicate, atRest2, List.length_drop,
    length_mulLen, atRest, List.length_drop, rulerOf_length', rulerOf_length', eval_C,
    tapesP, eval_C]
  have hlt := stepAtomIdx_length_lt tm sp pU z
  simp only [viewClauseP, eval_add, eval_mul, eval_C] at hlt
  rw [← rulerOf_length' (horP sp) z] at hlt
  have hle : (stepAtomIdx tm sp pU z).length - Fintype.card tm.Q
      - (k + 2) * (rulerOf (horP sp) z).length ≤ 4 * (k + 2) := by omega
  have hdiv := Nat.div_le_div_right (c := 4) hle
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)] at hdiv
  omega

open Polynomial in
theorem stepTupleIdx_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => stepTupleIdx tm sp (pU z) z) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP (rulerOf_mem_FP _)
    (stepViewIdx_mem_FP tm sp hp)) modFn2_mem_FP) fun _ => rfl

open Polynomial in
/-- The wire of the atom a step index forces. -/
noncomputable def stepForcedWireU (sp : Polynomial ℕ) (pU : List Bool → List Bool)
    (z : List Bool) : List Bool :=
  atomWireU [] (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (headBlockP (k := k) sp) z)
    (rulerOf (horP sp) z) (rulerOf (hor2P sp) z) (rulerOf (tapesP (k := k)) z)
    (stepTupleIdx tm sp (pU z) z) (stepAtomIdx tm sp (pU z) z)

open Polynomial in
/-- The value a step index forces on that atom. -/
noncomputable def stepForcedBitU (sp : Polynomial ℕ) (pU : List Bool → List Bool)
    (z : List Bool) : List Bool :=
  atomForcedU tm (stepCaseIdx tm sp (pU z) z) (rulerOf (C (Fintype.card tm.Q)) z)
    (rulerOf (horP sp) z) (rulerOf (tapesP (k := k)) z) (stepTupleIdx tm sp (pU z) z)
    (stepAtomIdx tm sp (pU z) z)

open Polynomial in
theorem stepForcedWireU_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool}
    (hp : pU ∈ FP)
    {E : ℕ} (hE : ∀ z, (atCellTape (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (horP sp) z)
      (rulerOf (tapesP (k := k)) z) (stepAtomIdx tm sp (pU z) z)).length ≤ E)
    {width : List Bool → List Bool} (hwd : width ∈ FP)
    (hbound : ∀ z, (rulerOf (horP sp) z).length ^ E
      + 2 * (rulerOf (horP sp) z).length + 4 ≤ (width z).length) :
    (fun z => stepForcedWireU tm sp pU z) ∈ FP :=
  atomWireU_mem_FP (constFn_mem_FP []) (rulerOf_mem_FP _) (rulerOf_mem_FP _)
    (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _) (stepTupleIdx_mem_FP tm sp hp)
    (stepAtomIdx_mem_FP tm sp hp) hE hwd hbound

open Polynomial in
theorem stepForcedBitU_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP)
    {C₀ : ℕ} (hC : ∀ z, (stepCaseIdx tm sp (pU z) z).length ≤ C₀)
    {K₁ : ℕ} (hK₁ : ∀ z, (pair (stepCaseIdx tm sp (pU z) z)
      (atHeadTape (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (horP sp) z)
        (stepAtomIdx tm sp (pU z) z))).length ≤ K₁)
    {K₂ : ℕ} (hK₂ : ∀ z, (pair (stepCaseIdx tm sp (pU z) z)
      (atCellTape (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (horP sp) z)
        (rulerOf (tapesP (k := k)) z) (stepAtomIdx tm sp (pU z) z))).length ≤ K₂)
    {E : ℕ}
    (hE₁ : ∀ z, (atHeadTape (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (horP sp) z)
      (stepAtomIdx tm sp (pU z) z)).length ≤ E)
    (hE₂ : ∀ z, (atCellTape (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (horP sp) z)
      (rulerOf (tapesP (k := k)) z) (stepAtomIdx tm sp (pU z) z)).length ≤ E)
    {width : List Bool → List Bool} (hwd : width ∈ FP)
    (hbound : ∀ z, (rulerOf (horP sp) z).length ^ E
      + 2 * (rulerOf (horP sp) z).length + 4 ≤ (width z).length) :
    (fun z => stepForcedBitU tm sp pU z) ∈ FP :=
  atomForcedU_mem_FP tm (stepCaseIdx_mem_FP tm sp hp) (rulerOf_mem_FP _)
    (rulerOf_mem_FP _) (rulerOf_mem_FP _) (stepTupleIdx_mem_FP tm sp hp)
    (stepAtomIdx_mem_FP tm sp hp) hC hK₁ hK₂ hE₁ hE₂ hwd hbound

/-! ## A step clause at the machine's sizes -/

open Polynomial in
/-- One step clause: a view's forced atom, or a frame clause. -/
noncomputable def stepEncAt (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool) : List Bool :=
  stepIdxEnc
    (viewClauseEncF tm sp uU vU sU (fun w => stepCaseIdx tm sp (pU w) w)
      (fun w => stepTupleIdx tm sp (pU w) w) (stepForcedWireU tm sp pU)
      (stepForcedBitU tm sp pU) z)
    (rulerOf (nvarP tm sp) z) (uU z) (vU z) (rulerOf (C (Fintype.card tm.Q)) z)
    (rulerOf (headBlockP (k := k) sp) z) (rulerOf (horP sp) z) (rulerOf (hor2P sp) z)
    (rulerOf (viewCountP tm sp) z) (rulerOf (viewClauseP tm sp) z)
    (rulerOf (frameTapeP sp) z) (rulerOf (framePosP sp) z) (rulerOf (C (4 * 2)) z) (pU z)

open Polynomial in
theorem stepEncAt_mem_FP (sp : Polynomial ℕ) {uU vU sU pU : List Bool → List Bool}
    (hu : uU ∈ FP) (hv : vU ∈ FP) (hp : pU ∈ FP)
    (hview : (fun z => viewClauseEncF tm sp uU vU sU (fun w => stepCaseIdx tm sp (pU w) w)
      (fun w => stepTupleIdx tm sp (pU w) w) (stepForcedWireU tm sp pU)
      (stepForcedBitU tm sp pU) z) ∈ FP) :
    (fun z => stepEncAt tm sp uU vU sU pU z) ∈ FP :=
  stepIdxEnc_mem_FP hview (rulerOf_mem_FP _) hu hv (rulerOf_mem_FP _) (rulerOf_mem_FP _)
    (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _)
    (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _) hp

open Polynomial in
/-- A width that dominates every table lookup inside a step clause. -/
noncomputable def stepWidthP (sp : Polynomial ℕ) : Polynomial ℕ :=
  horP sp ^ (5 * k + 10) + C 2 * horP sp + C 4

open Polynomial in
theorem stepWidth_bound (sp : Polynomial ℕ) (z : List Bool) :
    (rulerOf (horP sp) z).length ^ (5 * k + 10) + 2 * (rulerOf (horP sp) z).length + 4
      ≤ (rulerOf (stepWidthP (k := k) sp) z).length := by
  rw [rulerOf_length', rulerOf_length', stepWidthP]
  simp only [eval_add, eval_mul, eval_pow, eval_C]
  omega

open Polynomial in
theorem stepForcedWireU_mem_FP' (sp : Polynomial ℕ) {pU : List Bool → List Bool}
    (hp : pU ∈ FP) :
    (fun z => stepForcedWireU tm sp pU z) ∈ FP :=
  stepForcedWireU_mem_FP tm sp hp (E := 5 * k + 10)
    (fun z => atCellTape_stepAtom_le tm sp (pU z) z)
    (rulerOf_mem_FP (stepWidthP (k := k) sp)) (stepWidth_bound sp)

open Polynomial in
theorem stepForcedBitU_mem_FP' (sp : Polynomial ℕ) {pU : List Bool → List Bool}
    (hp : pU ∈ FP) : (fun z => stepForcedBitU tm sp pU z) ∈ FP :=
  stepForcedBitU_mem_FP tm sp hp (C₀ := Fintype.card (TransitionCase tm))
    (fun z => stepCaseIdx_length_le tm sp (pU z) z)
    (K₁ := 2 * Fintype.card (TransitionCase tm) + 2 + (5 * k + 10))
    (fun z => by
      rw [pair_length]
      have h₁ := stepCaseIdx_length_le tm sp (pU z) z
      have h₂ := atHeadTape_stepAtom_le tm sp (pU z) z
      omega)
    (K₂ := 2 * Fintype.card (TransitionCase tm) + 2 + (5 * k + 10))
    (fun z => by
      rw [pair_length]
      have h₁ := stepCaseIdx_length_le tm sp (pU z) z
      have h₂ := atCellTape_stepAtom_le tm sp (pU z) z
      omega)
    (E := 5 * k + 10)
    (fun z => atHeadTape_stepAtom_le tm sp (pU z) z)
    (fun z => atCellTape_stepAtom_le tm sp (pU z) z)
    (rulerOf_mem_FP (stepWidthP (k := k) sp)) (stepWidth_bound sp)

open Polynomial in
/-- The membership of `stepEncAt`, with every side condition discharged. -/
theorem stepEncAt_mem_FP' (sp : Polynomial ℕ) {uU vU sU pU : List Bool → List Bool}
    (hu : uU ∈ FP) (hv : vU ∈ FP) (hs : sU ∈ FP) (hp : pU ∈ FP) :
    (fun z => stepEncAt tm sp uU vU sU pU z) ∈ FP :=
  stepEncAt_mem_FP tm sp hu hv hp
    (viewClauseEncF_mem_FP' tm sp hu hv hs (stepCaseIdx_mem_FP tm sp hp)
      (stepTupleIdx_mem_FP tm sp hp) (stepForcedWireU_mem_FP' tm sp hp)
      (stepForcedBitU_mem_FP' tm sp hp) (C₀ := Fintype.card (TransitionCase tm))
      (fun y => stepCaseIdx_length_le tm sp (pU (pairFst y)) (pairFst y)))

open Polynomial in
/-- **A step clause in the view region at the machine's sizes.** -/
theorem stepEncAt_view_value (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool) (V : StepView tm T)
    (hviewC : (viewCountP tm sp).eval (pairFst z).length = (viewList tm T).length)
    (hvc : (viewClauseP tm sp).eval (pairFst z).length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hp : (pU z).length < (viewCountP tm sp).eval (pairFst z).length
      * (viewClauseP tm sp).eval (pairFst z).length)
    (hV : (viewList tm T)[(pU z).length
      / (viewClauseP tm sp).eval (pairFst z).length]? = some V)
    (hval : ((stepClausesView tm T (uU z).length (vU z).length (sU z).length
        V)[(pU z).length % (viewClauseP tm sp).eval (pairFst z).length]?).map
        DataEncode.bitstringEncode
      = some (viewClauseEncF tm sp uU vU sU (fun w => stepCaseIdx tm sp (pU w) w)
          (fun w => stepTupleIdx tm sp (pU w) w) (stepForcedWireU tm sp pU)
          (stepForcedBitU tm sp pU) z))
    (hrep : pU z = List.replicate (pU z).length true) :
    ((stepClauses tm T (uU z).length (vU z).length (sU z).length)[(pU z).length]?).map
        DataEncode.bitstringEncode
      = some (stepEncAt tm sp uU vU sU pU z) := by
  have hviews : (rulerOf (viewCountP tm sp) z).length = (viewList tm T).length := by
    rw [rulerOf_length']; exact hviewC
  have hscv : (rulerOf (viewClauseP tm sp) z).length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4) := by
    rw [rulerOf_length']; exact hvc
  have hlen : (rulerOf (viewClauseP tm sp) z).length
      = (viewClauseP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  rw [stepEncAt]
  conv_rhs => rw [hrep]
  exact stepIdxEnc_view_value tm T _ _ _ _ _ _ _ _ _ _ _ _ _ (uU z).length (vU z).length
    (sU z).length (pU z).length V hviews hscv
    (by rw [hscv]; omega)
    (by rw [hviews, hlen, ← hviewC]; exact hp) (by rw [hlen]; exact hV)
    (by rw [hlen]; exact hval)

open Polynomial in
/-- **A step clause whose atom is a state, encoded at the machine's sizes.** -/
theorem stepEncAt_state_clause (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool) (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (q : ℕ)
    (hq : q < Fintype.card tm.Q)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (stepCaseIdx tm sp (pU z) z).length < (caseList tm).length)
    (hc : (caseList tm)[(stepCaseIdx tm sp (pU z) z).length]'hcase = c)
    (hviewIdx : (stepTupleIdx tm sp (pU z) z).length = i.val)
    (hatom : (stepAtomIdx tm sp (pU z) z).length = q)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClausesView tm T (uU z).length (vU z).length (sU z).length
        (c, headTupleOf k T i))[q]?).map DataEncode.bitstringEncode
      = some (viewClauseEncF tm sp uU vU sU (fun w => stepCaseIdx tm sp (pU w) w)
          (fun w => stepTupleIdx tm sp (pU w) w) (stepForcedWireU tm sp pU)
          (stepForcedBitU tm sp pU) z) := by
  have hqlt : q < (stateList tm).length := by rw [stateList_length]; exact hq
  have hst : stateIndex tm ((stateList tm)[q]'hqlt) = q := stateIndex_stateList tm q hq
  have hqr : (rulerOf (C (Fintype.card tm.Q)) z).length = Fintype.card tm.Q := by
    rw [rulerOf_length', eval_C]
  refine viewClauseEncF_state_value tm T sp uU vU sU _ _ _ _ z c i q hq hT hT2 hhd
    hcase hc hviewIdx ?_ ?_ hs hu hv
  · rw [stepForcedWireU,
      atomWireU_state_eq (tm := tm) (T := T) (q := (stateList tm)[q]'hqlt) (hq := hqr)
        (ha := by rw [hatom, hst]),
      configIndex_state, hst]
  · rw [stepForcedBitU,
      atomForcedU_state_eq (tm := tm) (c := c) (q := (stateList tm)[q]'hqlt)
        (hclt := hcase) (hc := hc) (hq := hqr) (ha := by rw [hatom, hst])]

open Polynomial in
/-- **A step clause whose atom is a head, encoded at the machine's sizes.** -/
theorem stepEncAt_head_clause (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool) (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (q : ℕ)
    (tape : TapeSlot k) (p : Fin (T + 1))
    (h₁ : Fintype.card tm.Q ≤ q) (h₂ : q < Fintype.card tm.Q + (k + 2) * (T + 1))
    (htape : tape.index.val = (q - Fintype.card tm.Q) / (T + 1))
    (hp : p.val = (q - Fintype.card tm.Q) % (T + 1))
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (stepCaseIdx tm sp (pU z) z).length < (caseList tm).length)
    (hc : (caseList tm)[(stepCaseIdx tm sp (pU z) z).length]'hcase = c)
    (hviewIdx : (stepTupleIdx tm sp (pU z) z).length = i.val)
    (hatom : (stepAtomIdx tm sp (pU z) z).length = q)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClausesView tm T (uU z).length (vU z).length (sU z).length
        (c, headTupleOf k T i))[q]?).map DataEncode.bitstringEncode
      = some (viewClauseEncF tm sp uU vU sU (fun w => stepCaseIdx tm sp (pU w) w)
          (fun w => stepTupleIdx tm sp (pU w) w) (stepForcedWireU tm sp pU)
          (stepForcedBitU tm sp pU) z) := by
  have hqr : (rulerOf (C (Fintype.card tm.Q)) z).length = Fintype.card tm.Q := by
    rw [rulerOf_length', eval_C]
  have hhor : (rulerOf (horP sp) z).length = T + 1 := by rw [rulerOf_length']; exact hT
  have htp : (rulerOf (tapesP (k := k)) z).length = k + 2 := by
    rw [rulerOf_length', tapesP, eval_C]
  have hdm := Nat.div_add_mod (q - Fintype.card tm.Q) (T + 1)
  have hcomm : (T + 1) * ((q - Fintype.card tm.Q) / (T + 1))
      = ((q - Fintype.card tm.Q) / (T + 1)) * (T + 1) := Nat.mul_comm _ _
  have hav : (stepAtomIdx tm sp (pU z) z).length
      = Fintype.card tm.Q + (tape.index.val * (T + 1) + p.val) := by
    rw [hatom, htape, hp]
    omega
  refine viewClauseEncF_head_value tm T sp uU vU sU _ _ _ _ z c i q tape p h₁ h₂ htape hp
    hT hT2 hhd hcase hc hviewIdx ?_ ?_ hs hu hv
  · rw [stepForcedWireU,
      atomWireU_head_eq (tm := tm) (T := T) (tape := tape) (p := p) (hq := hqr)
        (hhor := hhor) (htapes := htp) (ha := hav), configIndex_head, htape, hp]
    omega
  · rw [stepForcedBitU,
      atomForcedU_head_eq (tm := tm) (T := T) (c := c) (i := i) (tape := tape) (p := p)
        (hclt := hcase) (hc := hc) (hq := hqr) (hhor := hhor) (htapes := htp)
        (hview := hviewIdx) (ha := hav)]

open Polynomial in
/-- **A step clause whose atom is a cell, encoded at the machine's sizes.** -/
theorem stepEncAt_cell_clause (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool) (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (q : ℕ)
    (tape : TapeSlot k) (m : ℕ) (hm : m < 4)
    (h₁ : Fintype.card tm.Q + (k + 2) * (T + 1) ≤ q)
    (h₂ : q < Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (htape : tape.index.val = (q - Fintype.card tm.Q - (k + 2) * (T + 1)) / 4)
    (hmv : m = (q - Fintype.card tm.Q - (k + 2) * (T + 1)) % 4)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (stepCaseIdx tm sp (pU z) z).length < (caseList tm).length)
    (hc : (caseList tm)[(stepCaseIdx tm sp (pU z) z).length]'hcase = c)
    (hviewIdx : (stepTupleIdx tm sp (pU z) z).length = i.val)
    (hatom : (stepAtomIdx tm sp (pU z) z).length = q)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClausesView tm T (uU z).length (vU z).length (sU z).length
        (c, headTupleOf k T i))[q]?).map DataEncode.bitstringEncode
      = some (viewClauseEncF tm sp uU vU sU (fun w => stepCaseIdx tm sp (pU w) w)
          (fun w => stepTupleIdx tm sp (pU w) w) (stepForcedWireU tm sp pU)
          (stepForcedBitU tm sp pU) z) := by
  have hmlt : m < symbolList.length := by rw [symbolList_length]; exact hm
  have hsym : (symbolIndex (symbolList[m]'hmlt)).val = m := symbolIndex_symbolList m hm
  have hqr : (rulerOf (C (Fintype.card tm.Q)) z).length = Fintype.card tm.Q := by
    rw [rulerOf_length', eval_C]
  have hhor : (rulerOf (horP sp) z).length = T + 1 := by rw [rulerOf_length']; exact hT
  have hhor2 : (rulerOf (hor2P sp) z).length = T + 2 := by rw [rulerOf_length']; exact hT2
  have hhdl : (rulerOf (headBlockP (k := k) sp) z).length = (k + 2) * (T + 1) := by
    rw [rulerOf_length']; exact hhd
  have htp : (rulerOf (tapesP (k := k)) z).length = k + 2 := by
    rw [rulerOf_length', tapesP, eval_C]
  have hdm := Nat.div_add_mod (q - Fintype.card tm.Q - (k + 2) * (T + 1)) 4
  have hav : (stepAtomIdx tm sp (pU z) z).length
      = Fintype.card tm.Q + (k + 2) * (T + 1)
        + (tape.index.val * 4 + (symbolIndex (symbolList[m]'hmlt)).val) := by
    rw [hatom, htape, hsym, hmv]
    omega
  refine viewClauseEncF_cell_value tm T sp uU vU sU _ _ _ _ z c i q tape m hm h₁ h₂ htape
    hmv hT hT2 hhd hcase hc hviewIdx ?_ ?_ hs hu hv
  · rw [stepForcedWireU,
      atomWireU_cell_eq (tm := tm) (T := T) (tape := tape) (sym := symbolList[m]'hmlt)
        (i := i) (hq := hqr) (hhd := hhdl) (hhor := hhor) (hhor2 := hhor2) (htapes := htp)
        (hview := hviewIdx) (ha := hav)]
  · rw [stepForcedBitU,
      atomForcedU_cell_eq (tm := tm) (T := T) (c := c) (i := i) (tape := tape)
        (sym := symbolList[m]'hmlt) (hclt := hcase) (hc := hc) (hq := hqr) (hhor := hhor)
        (htapes := htp) (hview := hviewIdx) (ha := hav)]

open Polynomial in
/-- **A step clause of a view at any atom index, encoded at the machine's sizes.** -/
theorem stepEncAt_view_clause (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool) (c : TransitionCase tm) (i : Fin ((T + 1) ^ (k + 2))) (q : ℕ)
    (hq : q < Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hcase : (stepCaseIdx tm sp (pU z) z).length < (caseList tm).length)
    (hc : (caseList tm)[(stepCaseIdx tm sp (pU z) z).length]'hcase = c)
    (hviewIdx : (stepTupleIdx tm sp (pU z) z).length = i.val)
    (hatom : (stepAtomIdx tm sp (pU z) z).length = q)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClausesView tm T (uU z).length (vU z).length (sU z).length
        (c, headTupleOf k T i))[q]?).map DataEncode.bitstringEncode
      = some (viewClauseEncF tm sp uU vU sU (fun w => stepCaseIdx tm sp (pU w) w)
          (fun w => stepTupleIdx tm sp (pU w) w) (stepForcedWireU tm sp pU)
          (stepForcedBitU tm sp pU) z) := by
  by_cases hst : q < Fintype.card tm.Q
  · exact stepEncAt_state_clause tm T sp uU vU sU pU z c i q hst hT hT2 hhd hcase hc
      hviewIdx hatom hs hu hv
  · by_cases hhead : q < Fintype.card tm.Q + (k + 2) * (T + 1)
    · have hdiv : (q - Fintype.card tm.Q) / (T + 1) < k + 2 :=
        Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      have hmod : (q - Fintype.card tm.Q) % (T + 1) < T + 1 := Nat.mod_lt _ (by omega)
      exact stepEncAt_head_clause tm T sp uU vU sU pU z c i q
        ((tapeSlotEquiv k).symm ⟨_, hdiv⟩) ⟨_, hmod⟩ (by omega) hhead
        (by rw [tapeSlotEquiv_symm_index]) rfl hT hT2 hhd hcase hc hviewIdx hatom hs hu hv
    · have hc4 : (k + 2) * 4 = 4 * (k + 2) := Nat.mul_comm _ _
      have hdiv : (q - Fintype.card tm.Q - (k + 2) * (T + 1)) / 4 < k + 2 :=
        Nat.div_lt_of_lt_mul (by omega)
      have hmod : (q - Fintype.card tm.Q - (k + 2) * (T + 1)) % 4 < 4 :=
        Nat.mod_lt _ (by omega)
      exact stepEncAt_cell_clause tm T sp uU vU sU pU z c i q
        ((tapeSlotEquiv k).symm ⟨_, hdiv⟩) _ hmod (by omega) (by omega)
        (by rw [tapeSlotEquiv_symm_index]) rfl hT hT2 hhd hcase hc hviewIdx hatom hs hu hv

open Polynomial in
/-- The frame-block sizes at the machine's rulers. -/
theorem frameTapeP_eval (sp : Polynomial ℕ) (n : ℕ) :
    (frameTapeP sp).eval n
      = ((horizonP sp).eval n + 1) * (((horizonP sp).eval n + 2) * (4 * 2)) := by
  rw [frameTapeP, eval_mul, eval_mul, eval_C, horP_eval, hor2P_eval]

open Polynomial in
theorem framePosP_eval (sp : Polynomial ℕ) (n : ℕ) :
    (framePosP sp).eval n = ((horizonP sp).eval n + 2) * (4 * 2) := by
  rw [framePosP, eval_mul, eval_C, hor2P_eval]

/-- A head wire with in-range tape and position fits inside the variable count. -/
theorem headWireU_le (uU qU tapeU posU horU : List Bool) (N : ℕ)
    (hq : qU.length = Fintype.card tm.Q) (hhor : horU.length = T + 1)
    (ht : tapeU.length < k + 2) (hp : posU.length < T + 1)
    (hu : uU.length + configWidth tm T ≤ N) :
    (headWireU uU qU tapeU posU horU).length ≤ N := by
  have hblk : tapeU.length * (T + 1) + posU.length < (k + 2) * (T + 1) := by
    have h1 : (tapeU.length + 1) * (T + 1) ≤ (k + 2) * (T + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (tapeU.length + 1) * (T + 1) = tapeU.length * (T + 1) + (T + 1) := by ring
    omega
  rw [headWireU_length, hq, hhor, configWidth] at *
  omega

/-- A cell wire with in-range tape, position and symbol fits inside the variable count. -/
theorem cellWireU_le (uU qU hdU tapeU posU horU symU : List Bool) (N : ℕ)
    (hq : qU.length = Fintype.card tm.Q) (hhd : hdU.length = (k + 2) * (T + 1))
    (hhor : horU.length = T + 2) (ht : tapeU.length < k + 2) (hp : posU.length < T + 2)
    (hs : symU.length < 4) (hu : uU.length + configWidth tm T ≤ N) :
    (cellWireU uU qU hdU tapeU posU horU symU).length ≤ N := by
  have hblk : (tapeU.length * (T + 2) + posU.length) * 4 + symU.length
      < 4 * (k + 2) * (T + 2) := by
    have h1 : (tapeU.length + 1) * (T + 2) ≤ (k + 2) * (T + 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (tapeU.length + 1) * (T + 2) = tapeU.length * (T + 2) + (T + 2) := by ring
    have h3 : 4 * (k + 2) * (T + 2) = ((k + 2) * (T + 2)) * 4 := by ring
    omega
  rw [cellWireU_length, hq, hhd, hhor, configWidth] at *
  omega

theorem frTape_lt (blkTU pU : List Bool) (hb : 0 < blkTU.length)
    (hp : pU.length < (k + 2) * blkTU.length) : (frTape blkTU pU).length < k + 2 := by
  have hc : (k + 2) * blkTU.length = blkTU.length * (k + 2) := Nat.mul_comm _ _
  rw [frTape_length _ _ hb]
  exact Nat.div_lt_of_lt_mul (by omega)

theorem frHead_lt (blkTU blkPU pU : List Bool) (hbt : 0 < blkTU.length)
    (hbp : 0 < blkPU.length) (hb : blkTU.length = (T + 1) * blkPU.length) :
    (frHead blkTU blkPU pU).length < T + 1 := by
  have hmod : pU.length % blkTU.length < blkTU.length := Nat.mod_lt _ hbt
  have hc : (T + 1) * blkPU.length = blkPU.length * (T + 1) := Nat.mul_comm _ _
  rw [frHead_length _ _ _ hbt hbp]
  exact Nat.div_lt_of_lt_mul (by omega)

theorem frPos_lt (blkTU blkPU blkPosU pU : List Bool) (hbt : 0 < blkTU.length)
    (hbp : 0 < blkPU.length) (hbpos : 0 < blkPosU.length)
    (hb : blkPU.length = (T + 2) * blkPosU.length) :
    (frPos blkTU blkPU blkPosU pU).length < T + 2 := by
  have hmod : pU.length % blkTU.length % blkPU.length < blkPU.length := Nat.mod_lt _ hbp
  have hc : (T + 2) * blkPosU.length = blkPosU.length * (T + 2) := Nat.mul_comm _ _
  rw [frPos_length _ _ _ _ hbt hbp hbpos]
  exact Nat.div_lt_of_lt_mul (by omega)

theorem frSym_lt (blkTU blkPU blkPosU pU : List Bool) (hbt : 0 < blkTU.length)
    (hbp : 0 < blkPU.length) (hbpos : blkPosU.length = 4 * 2) :
    (frSym blkTU blkPU blkPosU pU).length < 4 := by
  have hpos : 0 < blkPosU.length := by rw [hbpos]; omega
  have hmod : pU.length % blkTU.length % blkPU.length % blkPosU.length < blkPosU.length :=
    Nat.mod_lt _ hpos
  rw [frSym_length' _ _ _ _ hbt hbp hpos, hbpos] at *
  omega

open Polynomial in
/-- **A frame clause at the machine's sizes, encoded.** -/
theorem frameIdxEncAt_value (sp : Polynomial ℕ) (uU vU : List Bool) (i : ℕ)
    (z : List Bool)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hi : i < (k + 2) * ((T + 1) * ((T + 2) * (4 * 2))))
    (hu : uU.length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : vU.length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((frameClauses tm T uU.length vU.length)[i]?).map DataEncode.bitstringEncode
      = some (frameIdxEnc (rulerOf (nvarP tm sp) z) uU vU
          (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (headBlockP (k := k) sp) z)
          (rulerOf (horP sp) z) (rulerOf (hor2P sp) z) (rulerOf (frameTapeP sp) z)
          (rulerOf (framePosP sp) z) (rulerOf (C (4 * 2)) z) (List.replicate i true)) := by
  have hqr : (rulerOf (C (Fintype.card tm.Q)) z).length = Fintype.card tm.Q := by
    rw [rulerOf_length', eval_C]
  have hhorr : (rulerOf (horP sp) z).length = T + 1 := by rw [rulerOf_length']; exact hT
  have hhor2r : (rulerOf (hor2P sp) z).length = T + 2 := by rw [rulerOf_length']; exact hT2
  have hhdr : (rulerOf (headBlockP (k := k) sp) z).length = (k + 2) * (T + 1) := by
    rw [rulerOf_length']; exact hhd
  have hbT : (rulerOf (frameTapeP sp) z).length = (T + 1) * ((T + 2) * (4 * 2)) := by
    rw [rulerOf_length', frameTapeP_eval, ← hT, ← hT2, horP_eval, hor2P_eval]
  have hbP : (rulerOf (framePosP sp) z).length = (T + 2) * (4 * 2) := by
    rw [rulerOf_length', framePosP_eval, ← hT2, hor2P_eval]
  have hbPos : (rulerOf (C (4 * 2)) z).length = 4 * 2 := by rw [rulerOf_length', eval_C]
  have hnv : (rulerOf (nvarP tm sp) z).length
      = (nvarP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  have hlen : (List.replicate i true).length = i := List.length_replicate
  have htlt : (frTape (rulerOf (frameTapeP sp) z) (List.replicate i true)).length < k + 2 :=
    frTape_lt _ _ (by rw [hbT]; positivity) (by rw [hlen, hbT]; exact hi)
  have hhlt : (frHead (rulerOf (frameTapeP sp) z) (rulerOf (framePosP sp) z)
      (List.replicate i true)).length < T + 1 :=
    frHead_lt T _ _ _ (by rw [hbT]; positivity) (by rw [hbP]; positivity)
      (by rw [hbT, hbP])
  have hplt : (frPos (rulerOf (frameTapeP sp) z) (rulerOf (framePosP sp) z)
      (rulerOf (C (4 * 2)) z) (List.replicate i true)).length < T + 2 :=
    frPos_lt T _ _ _ _ (by rw [hbT]; positivity) (by rw [hbP]; positivity)
      (by rw [hbPos]; omega) (by rw [hbP, hbPos])
  have hslt : (frSym (rulerOf (frameTapeP sp) z) (rulerOf (framePosP sp) z)
      (rulerOf (C (4 * 2)) z) (List.replicate i true)).length < 4 :=
    frSym_lt _ _ _ _ (by rw [hbT]; positivity) (by rw [hbP]; positivity) hbPos
  exact frameIdxEnc_value tm T _ uU vU _ _ _ _ _ _ _ hqr hhdr hhorr hhor2r hbT hbP hbPos
    i hi
    (headWireU_le tm T uU _ _ _ _ _ hqr hhorr htlt hhlt (by rw [hnv]; exact hu))
    (cellWireU_le tm T uU _ _ _ _ _ _ _ hqr hhdr hhor2r htlt hplt hslt
      (by rw [hnv]; exact hu))
    (cellWireU_le tm T vU _ _ _ _ _ _ _ hqr hhdr hhor2r htlt hplt hslt
      (by rw [hnv]; exact hv))

open Polynomial in
/-- **A step clause in the frame region at the machine's sizes.** -/
theorem stepEncAt_frame_value (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hviewC : (viewCountP tm sp).eval (pairFst z).length = (viewList tm T).length)
    (hvc : (viewClauseP tm sp).eval (pairFst z).length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hge : (viewCountP tm sp).eval (pairFst z).length
      * (viewClauseP tm sp).eval (pairFst z).length ≤ (pU z).length)
    (hlt : (pU z).length - (viewCountP tm sp).eval (pairFst z).length
        * (viewClauseP tm sp).eval (pairFst z).length
      < (k + 2) * ((T + 1) * ((T + 2) * (4 * 2))))
    (hrep : pU z = List.replicate (pU z).length true)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClauses tm T (uU z).length (vU z).length
        (sU z).length)[(pU z).length]?).map DataEncode.bitstringEncode
      = some (stepEncAt tm sp uU vU sU pU z) := by
  have hviews : (rulerOf (viewCountP tm sp) z).length = (viewList tm T).length := by
    rw [rulerOf_length']; exact hviewC
  have hscv : (rulerOf (viewClauseP tm sp) z).length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4) := by
    rw [rulerOf_length']; exact hvc
  rw [stepEncAt]
  conv_rhs => rw [hrep]
  exact stepIdxEnc_frame_value tm T _ _ _ _ _ _ _ _ _ _ _ _ _ (uU z).length (vU z).length
    (pU z).length hviews hscv (by rw [hviews, hscv, ← hviewC, ← hvc]; exact hge)
    (sU z).length
    (by
      rw [hviews, hscv, ← hviewC, ← hvc]
      exact frameIdxEncAt_value tm T sp (uU z) (vU z) _ z hT hT2 hhd hlt hu hv)

open Polynomial in
/-- **A step clause in the view region at the machine's sizes.** -/
theorem stepEncAt_viewRegion_value (sp : Polynomial ℕ)
    (uU vU sU pU : List Bool → List Bool) (z : List Bool)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hviewC : (viewCountP tm sp).eval (pairFst z).length = (viewList tm T).length)
    (hvc : (viewClauseP tm sp).eval (pairFst z).length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hp : (pU z).length < (viewCountP tm sp).eval (pairFst z).length
      * (viewClauseP tm sp).eval (pairFst z).length)
    (hrep : pU z = List.replicate (pU z).length true)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClauses tm T (uU z).length (vU z).length
        (sU z).length)[(pU z).length]?).map DataEncode.bitstringEncode
      = some (stepEncAt tm sp uU vU sU pU z) := by
  have hvcpos : 0 < (viewClauseP tm sp).eval (pairFst z).length :=
    viewClauseP_eval_pos tm sp _
  have hpow : 0 < (T + 1) ^ (k + 2) := by positivity
  have hvl : (viewList tm T).length
      = Fintype.card (TransitionCase tm) * (T + 1) ^ (k + 2) := viewList_length tm T
  have hview : (pU z).length / (viewClauseP tm sp).eval (pairFst z).length
      < (viewList tm T).length := by
    rw [← hviewC]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hp)
  have hcIdx : (pU z).length / (viewClauseP tm sp).eval (pairFst z).length
      / (T + 1) ^ (k + 2) < (caseList tm).length := by
    rw [caseList_length]
    refine Nat.div_lt_of_lt_mul ?_
    rw [Nat.mul_comm]
    rw [hvl] at hview
    exact hview
  have htIdx : (pU z).length / (viewClauseP tm sp).eval (pairFst z).length
      % (T + 1) ^ (k + 2) < (T + 1) ^ (k + 2) := Nat.mod_lt _ hpow
  have hcase : (stepCaseIdx tm sp (pU z) z).length = (pU z).length
      / (viewClauseP tm sp).eval (pairFst z).length / (T + 1) ^ (k + 2) := by
    rw [stepCaseIdx_length, hT]
    rw [caseList_length] at hcIdx
    omega
  have hV : (viewList tm T)[(pU z).length
      / (viewClauseP tm sp).eval (pairFst z).length]?
      = some ((caseList tm)[(pU z).length
          / (viewClauseP tm sp).eval (pairFst z).length / (T + 1) ^ (k + 2)]'hcIdx,
        headTupleOf k T ⟨_, htIdx⟩) := by
    rw [viewList_getElem? tm T _ (by rw [caseList_length, ← hvl]; exact hview),
      List.getElem?_eq_getElem hcIdx, Option.map_some]
  exact stepEncAt_view_value tm T sp uU vU sU pU z _ hviewC hvc hp hV
    (stepEncAt_view_clause tm T sp uU vU sU pU z _ ⟨_, htIdx⟩ _
      (by rw [← hvc]; exact Nat.mod_lt _ hvcpos) hT hT2 hhd (by rw [hcase]; exact hcIdx)
      (by simp only [hcase]) (by rw [stepTupleIdx_length, hT])
      (by rw [stepAtomIdx_length]) hs hu hv) hrep

open Polynomial in
/-- **A step clause at the machine's sizes, encoded.** -/
theorem stepEncAt_value (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hviewC : (viewCountP tm sp).eval (pairFst z).length = (viewList tm T).length)
    (hvc : (viewClauseP tm sp).eval (pairFst z).length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hp : (pU z).length < (viewCountP tm sp).eval (pairFst z).length
        * (viewClauseP tm sp).eval (pairFst z).length
      + (k + 2) * ((T + 1) * ((T + 2) * (4 * 2))))
    (hrep : pU z = List.replicate (pU z).length true)
    (hs : (sU z).length ≤ (nvarP tm sp).eval (pairFst z).length)
    (hu : (uU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length)
    (hv : (vU z).length + configWidth tm T ≤ (nvarP tm sp).eval (pairFst z).length) :
    ((stepClauses tm T (uU z).length (vU z).length
        (sU z).length)[(pU z).length]?).map DataEncode.bitstringEncode
      = some (stepEncAt tm sp uU vU sU pU z) := by
  by_cases hview : (pU z).length < (viewCountP tm sp).eval (pairFst z).length
      * (viewClauseP tm sp).eval (pairFst z).length
  · exact stepEncAt_viewRegion_value tm T sp uU vU sU pU z hT hT2 hhd hviewC hvc hview
      hrep hs hu hv
  · exact stepEncAt_frame_value tm T sp uU vU sU pU z hT hT2 hhd hviewC hvc (by omega)
      (by omega) hrep hu hv

/-! ## A base clause at the machine's sizes -/

open Polynomial in
/-- One base clause: block equality guarded by the selector, or a step clause. -/
noncomputable def baseEncAt (sp : Polynomial ℕ) (uU vU sU pU : List Bool → List Bool)
    (z : List Bool) : List Bool :=
  baseEnc
    (stepEncAt tm sp uU vU sU
      (fun w => (pU w).drop (rulerOf (twoWidthP tm sp) w).length) z)
    (rulerOf (nvarP tm sp) z) (uU z) (vU z) (sU z ++ [false])
    (rulerOf (twoWidthP tm sp) z) (pU z)

open Polynomial in
theorem baseEncAt_mem_FP (sp : Polynomial ℕ) {uU vU sU pU : List Bool → List Bool}
    (hu : uU ∈ FP) (hv : vU ∈ FP) (hs : sU ∈ FP) (hp : pU ∈ FP)
    (hstep : (fun z => stepEncAt tm sp uU vU sU
      (fun w => (pU w).drop (rulerOf (twoWidthP tm sp) w).length) z) ∈ FP) :
    (fun z => baseEncAt tm sp uU vU sU pU z) ∈ FP :=
  baseEnc_mem_FP hstep (rulerOf_mem_FP _) hu hv
    (Cobham.appendFn_mem_FP hs (constFn_mem_FP [false])) (rulerOf_mem_FP _) hp

open Polynomial in
/-- The membership of `baseEncAt`, with every side condition discharged. -/
theorem baseEncAt_mem_FP' (sp : Polynomial ℕ) {uU vU sU pU : List Bool → List Bool}
    (hu : uU ∈ FP) (hv : vU ∈ FP) (hs : sU ∈ FP) (hp : pU ∈ FP) :
    (fun z => baseEncAt tm sp uU vU sU pU z) ∈ FP :=
  baseEncAt_mem_FP tm sp hu hv hs hp
    (stepEncAt_mem_FP' tm sp hu hv hs (dropLenFn_mem_FP (rulerOf_mem_FP _) hp))

/-! ## The guards at the machine's sizes -/

open Polynomial in
/-- One guard clause, with every size supplied by the layout's polynomials. -/
noncomputable def guardEncAt (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  guardEnc
    (validEncAt tm sp [] (pU.drop (rulerOf (widthP tm sp) z).length) z)
    (validEncAt tm sp (rulerOf (bStartP tm sp) z)
      ((pU.drop (rulerOf (widthP tm sp) z).length).drop
        (rulerOf (validCountP tm sp) z).length) z)
    (rulerOf (nvarP tm sp) z) (rulerOf (C (Fintype.card tm.Q)) z) (rulerOf (horP sp) z)
    (rulerOf (hor2P sp) z) (rulerOf (tapesP (k := k)) z) (rulerOf (qstartP tm) z)
    (pairFst z) (rulerOf (widthP tm sp) z) (rulerOf (validCountP tm sp) z)
    (rulerOf (accStateP tm sp) z) (rulerOf (accCellP tm sp) z) (rulerOf (y0P tm sp) z)
    pU

open Polynomial in
theorem guardEncAt_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => guardEncAt tm sp (pU z) z) ∈ FP := by
  have d1 : (fun z => (pU z).drop (rulerOf (widthP tm sp) z).length) ∈ FP :=
    dropLenFn_mem_FP (rulerOf_mem_FP _) hp
  have d2 : (fun z => ((pU z).drop (rulerOf (widthP tm sp) z).length).drop
      (rulerOf (validCountP tm sp) z).length) ∈ FP :=
    dropLenFn_mem_FP (rulerOf_mem_FP _) d1
  exact guardEnc_mem_FP (validEncAt_mem_FP tm sp (constFn_mem_FP []) d1)
    (validEncAt_mem_FP tm sp (rulerOf_mem_FP _) d2)
    (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _)
    (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _) pairFst_mem_FP
    (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _)
    (rulerOf_mem_FP _) hp

/-! ## How many clauses the base family has -/

theorem cfgBaseC_length (u v s : ℕ) :
    (cfgBaseC tm T u v s).length
      = configWidth tm T * 2
        + ((viewList tm T).length
            * (Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
          + (k + 2) * ((T + 1) * ((T + 2) * (4 * 2)))) := by
  rw [cfgBaseC, QBF.orCNF, List.length_append, QBF.disjLit_length, QBF.disjLit_length,
    eqClauses_length, stepClauses_length]

open Polynomial in
/-- How many clauses the base family has. -/
noncomputable def baseCountP (sp : Polynomial ℕ) : Polynomial ℕ :=
  C 2 * widthP tm sp + (viewCountP tm sp * viewClauseP tm sp
    + tapesP (k := k) * frameTapeP sp)

open Polynomial in
theorem baseCountP_eval (sp : Polynomial ℕ) (x : List Bool) (u v s : ℕ) :
    (baseCountP tm sp).eval x.length
      = (cfgBaseC tm ((horizonP sp).eval x.length) u v s).length := by
  rw [cfgBaseC_length, viewList_length, ← widthP_eval]
  simp only [baseCountP, viewCountP, viewClauseP, tapesP, frameTapeP, horP, hor2P,
    eval_add, eval_mul, eval_pow, eval_C]
  ring

open Polynomial in
/-- How many clauses the whole matrix has. -/
noncomputable def matrixCountP (sp : Polynomial ℕ) : Polynomial ℕ :=
  guardCountP tm sp + levelCountP tm sp * levelsP tm sp + baseCountP tm sp

open Polynomial in
theorem matrixCountP_eval (sp : Polynomial ℕ) (x : List Bool)
    (init : Fin (flatLayoutOf tm sp x).W → Bool) :
    (matrixCountP tm sp).eval x.length
      = ((flatLayoutOf tm sp x).fullClauses
          (cfgValidC tm ((horizonP sp).eval x.length) x (sp.eval x.length))
          (cfgBaseC tm ((horizonP sp).eval x.length))
          (cfgAccC tm ((horizonP sp).eval x.length)) init).length := by
  rw [FlatLayout.fullClauses, List.length_append, ← guardCountP_eval tm sp x init,
    FlatLayout.tailClauses_length _ _ _ ((levelCountP tm sp).eval x.length)
      ((baseCountP tm sp).eval x.length) (fun j => (levelCountP_eval tm sp x j).symm)
      (fun u v s => (baseCountP_eval tm sp x u v s).symm), flatLayoutOf_n, matrixCountP]
  simp only [eval_add, eval_mul]
  ring


open Polynomial in
/-- **A guard clause at the machine's sizes, encoded.** -/
theorem guardEncAt_eq (sp : Polynomial ℕ) (p : ℕ) (z : List Bool)
    (validC : ℕ → List (List CLit))
    (init : Fin (flatLayoutOf tm sp (pairFst z)).W → Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T)
    (hVC : ∀ off, (validC off).length = (validCountP tm sp).eval (pairFst z).length)
    (hWc : (flatLayoutOf tm sp (pairFst z)).W = configWidth tm T)
    (hinit : ∀ (r : ℕ) (hr : r < (flatLayoutOf tm sp (pairFst z)).W), init ⟨r, hr⟩
      = ConfigAtom.value (Cfg.init tm.qstart (pairFst z))
        ((configAtomEquiv tm T).symm ⟨r, by rw [← hWc]; exact hr⟩))
    (hp : p < (flatLayoutOf tm sp (pairFst z)).W
      + ((validCountP tm sp).eval (pairFst z).length
        + ((validCountP tm sp).eval (pairFst z).length + (2 + 1))))
    (hvA : (rulerOf (widthP tm sp) z).length ≤ p →
      p < (rulerOf (widthP tm sp) z).length + (rulerOf (validCountP tm sp) z).length →
      ((validC 0)[p - (rulerOf (widthP tm sp) z).length]?).map DataEncode.bitstringEncode
        = some (validEncAt tm sp []
            ((List.replicate p true).drop (rulerOf (widthP tm sp) z).length) z))
    (hvB : (rulerOf (widthP tm sp) z).length + (rulerOf (validCountP tm sp) z).length ≤ p →
      p < (rulerOf (widthP tm sp) z).length + (rulerOf (validCountP tm sp) z).length
        + (rulerOf (validCountP tm sp) z).length →
      ((validC (flatLayoutOf tm sp (pairFst z)).bStart)[p
          - (rulerOf (widthP tm sp) z).length
          - (rulerOf (validCountP tm sp) z).length]?).map DataEncode.bitstringEncode
        = some (validEncAt tm sp (rulerOf (bStartP tm sp) z)
            (((List.replicate p true).drop (rulerOf (widthP tm sp) z).length).drop
              (rulerOf (validCountP tm sp) z).length) z)) :
    (((flatLayoutOf tm sp (pairFst z)).guardClauses validC (cfgAccC tm T)
        init)[p]?).map DataEncode.bitstringEncode
      = some (guardEncAt tm sp (List.replicate p true) z) := by
  have hW : (rulerOf (widthP tm sp) z).length = (flatLayoutOf tm sp (pairFst z)).W := by
    rw [rulerOf_length', flatLayoutOf_W]
  have hvc : (rulerOf (validCountP tm sp) z).length
      = (validCountP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  have hnv : (rulerOf (nvarP tm sp) z).length
      = (nvarP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  have ha₁ : (rulerOf (accStateP tm sp) z).length
      = configWire tm T (flatLayoutOf tm sp (pairFst z)).bStart (.state tm.qhalt) := by
    rw [rulerOf_length']
    exact accStateP_eval' tm sp (pairFst z) T hT
  have ha₂ : (rulerOf (accCellP tm sp) z).length
      = configWire tm T (flatLayoutOf tm sp (pairFst z)).bStart
        (.cell TapeSlot.output ⟨1, by omega⟩ Γ.one) := by
    rw [rulerOf_length']
    exact accCellP_eval' tm sp (pairFst z) T hT
  rw [guardEncAt]
  exact guardEnc_eq tm T _ _ _ _ _ _ _ _ _ _ _ _ _ _ (flatLayoutOf tm sp (pairFst z))
    validC init (fun off => by rw [hVC, hvc]) hWc hW
    (by rw [rulerOf_length', eval_C]) (by rw [rulerOf_length', horP_eval, hT])
    (by rw [rulerOf_length', hor2P_eval, hT])
    (by rw [rulerOf_length', tapesP, eval_C]) (by rw [rulerOf_length', qstartP, eval_C])
    hinit ha₁ ha₂ (by rw [rulerOf_length', y0P_eval])
    (by rw [hnv, flatLayoutOf_W]; exact widthP_le_nvarP tm sp _)
    (by rw [rulerOf_length', hnv]; exact accStateP_le_nvarP tm sp _)
    (by rw [rulerOf_length', hnv]; exact accCellP_le_nvarP tm sp _)
    (by rw [rulerOf_length', hnv]; exact y0P_le_nvarP tm sp _)
    p (by rw [hW, hvc]; exact hp) hvA hvB

open Polynomial in
/-- A level's block, plus a block width, fits inside the variable count. -/
theorem levBlkU_le_nvarP (sp : Polynomial ℕ) (c : ℕ) (hc : c ≤ 6) (jU z : List Bool)
    (hj : jU.length < (flatLayoutOf tm sp (pairFst z)).n) :
    (levBlkU tm sp c jU z).length + (rulerOf (widthP tm sp) z).length
      ≤ (rulerOf (nvarP tm sp) z).length := by
  have hWe : (flatLayoutOf tm sp (pairFst z)).W
      = (widthP tm sp).eval (pairFst z).length := flatLayoutOf_W tm sp _
  have hls : (levelSizeP tm sp).eval (pairFst z).length
      = 7 * (widthP tm sp).eval (pairFst z).length + 1 := by
    simp only [levelSizeP, eval_add, eval_mul, eval_C]
  have htw : (twoWidthP tm sp).eval (pairFst z).length
      = 2 * (widthP tm sp).eval (pairFst z).length := by
    simp only [twoWidthP, eval_mul, eval_C]
  have hbound := levBlock_le_nvarP tm sp (pairFst z).length jU.length
    (c * (widthP tm sp).eval (pairFst z).length
      + (widthP tm sp).eval (pairFst z).length)
    (by rw [← flatLayoutOf_n]; exact hj) (by rw [hls]; nlinarith)
  rw [hls, htw] at hbound
  rw [levBlkU_length, rulerOf_length', rulerOf_length', FlatLayout.levStart,
    FlatLayout.levelSize, hWe]
  omega

open Polynomial in
/-- A level's chain bits fit inside the variable count. -/
theorem levYU_le_nvarP (sp : Polynomial ℕ) (jU z : List Bool)
    (hj : jU.length < (flatLayoutOf tm sp (pairFst z)).n) :
    (levYU tm sp jU z).length ≤ (rulerOf (nvarP tm sp) z).length := by
  have hWe : (flatLayoutOf tm sp (pairFst z)).W
      = (widthP tm sp).eval (pairFst z).length := flatLayoutOf_W tm sp _
  have hls : (levelSizeP tm sp).eval (pairFst z).length
      = 7 * (widthP tm sp).eval (pairFst z).length + 1 := by
    simp only [levelSizeP, eval_add, eval_mul, eval_C]
  have htw : (twoWidthP tm sp).eval (pairFst z).length
      = 2 * (widthP tm sp).eval (pairFst z).length := by
    simp only [twoWidthP, eval_mul, eval_C]
  have hbound := levBlock_le_nvarP tm sp (pairFst z).length jU.length 0
    (by rw [← flatLayoutOf_n]; exact hj) (by omega)
  rw [hls, htw] at hbound
  rw [levYU_length, rulerOf_length', FlatLayout.yAt]
  rcases Nat.eq_zero_or_pos jU.length with h | h
  · rw [if_pos h, FlatLayout.y0, hWe]
    omega
  · rw [if_neg (by omega), FlatLayout.levStart, FlatLayout.levelSize, hWe]
    have hstep : (7 * (widthP tm sp).eval (pairFst z).length + 1) * (jU.length - 1)
        + (7 * (widthP tm sp).eval (pairFst z).length + 1)
        = (7 * (widthP tm sp).eval (pairFst z).length + 1) * jU.length := by
      conv_rhs => rw [show jU.length = (jU.length - 1) + 1 from by omega]
      ring
    omega

open Polynomial in
theorem levYSuccU_le_nvarP (sp : Polynomial ℕ) (jU z : List Bool)
    (hj : jU.length < (flatLayoutOf tm sp (pairFst z)).n) :
    (levYSuccU tm sp jU z).length ≤ (rulerOf (nvarP tm sp) z).length := by
  have hWe : (flatLayoutOf tm sp (pairFst z)).W
      = (widthP tm sp).eval (pairFst z).length := flatLayoutOf_W tm sp _
  have hls : (levelSizeP tm sp).eval (pairFst z).length
      = 7 * (widthP tm sp).eval (pairFst z).length + 1 := by
    simp only [levelSizeP, eval_add, eval_mul, eval_C]
  have htw : (twoWidthP tm sp).eval (pairFst z).length
      = 2 * (widthP tm sp).eval (pairFst z).length := by
    simp only [twoWidthP, eval_mul, eval_C]
  have hbound := levBlock_le_nvarP tm sp (pairFst z).length jU.length
    ((levelSizeP tm sp).eval (pairFst z).length)
    (by rw [← flatLayoutOf_n]; exact hj) (by omega)
  rw [hls, htw] at hbound
  rw [levYSuccU_length, rulerOf_length', FlatLayout.yAt, if_neg (by omega),
    FlatLayout.levStart, FlatLayout.levelSize, hWe, Nat.add_sub_cancel]
  omega

open Polynomial in
theorem levMidU_le_nvarP (sp : Polynomial ℕ) (jU z : List Bool)
    (hj : jU.length < (flatLayoutOf tm sp (pairFst z)).n) :
    (levMidU tm sp jU z).length + (rulerOf (widthP tm sp) z).length
      ≤ (rulerOf (nvarP tm sp) z).length := by
  have h := levBlkU_le_nvarP tm sp 0 (by omega) jU z hj
  rw [levBlkU_length] at h
  rw [levMidU_length, FlatLayout.mid]
  omega

open Polynomial in
theorem levLeftU_le_nvarP (sp : Polynomial ℕ) (jU z : List Bool)
    (hj : jU.length < (flatLayoutOf tm sp (pairFst z)).n) :
    (levLeftU tm sp jU z).length + (rulerOf (widthP tm sp) z).length
      ≤ (rulerOf (nvarP tm sp) z).length := by
  rw [levLeftU_length, rulerOf_length', rulerOf_length', FlatLayout.leftOf]
  rcases Nat.eq_zero_or_pos jU.length with h | h
  · rw [if_pos h]
    have := widthP_le_nvarP tm sp (pairFst z).length
    omega
  · rw [if_neg (by omega)]
    have hb := levBlkU_le_nvarP tm sp 1 (by omega) (List.replicate (jU.length - 1) true) z
      (by rw [List.length_replicate]; omega)
    rw [levBlkU_length, rulerOf_length', rulerOf_length', List.length_replicate,
      FlatLayout.levStart, FlatLayout.levelSize] at hb
    rw [FlatLayout.uBlk, FlatLayout.levStart, FlatLayout.levelSize]
    omega

open Polynomial in
theorem levRightU_le_nvarP (sp : Polynomial ℕ) (jU z : List Bool)
    (hj : jU.length < (flatLayoutOf tm sp (pairFst z)).n) :
    (levRightU tm sp jU z).length + (rulerOf (widthP tm sp) z).length
      ≤ (rulerOf (nvarP tm sp) z).length := by
  rw [levRightU_length, rulerOf_length', rulerOf_length', FlatLayout.rightOf]
  rcases Nat.eq_zero_or_pos jU.length with h | h
  · rw [if_pos h, FlatLayout.bStart, flatLayoutOf_W]
    have := twoWidthP_le_nvarP tm sp (pairFst z).length
    rw [twoWidthP] at this
    simp only [eval_mul, eval_C] at this
    omega
  · rw [if_neg (by omega)]
    have hb := levBlkU_le_nvarP tm sp 2 (by omega) (List.replicate (jU.length - 1) true) z
      (by rw [List.length_replicate]; omega)
    rw [levBlkU_length, rulerOf_length', rulerOf_length', List.length_replicate,
      FlatLayout.levStart, FlatLayout.levelSize] at hb
    rw [FlatLayout.vBlk, FlatLayout.levStart, FlatLayout.levelSize]
    omega

open Polynomial in
/-- **A level clause at the machine's sizes, encoded.** -/
theorem levelEncAt_eq (sp : Polynomial ℕ) (jU : List Bool) (p : ℕ) (z : List Bool)
    (validC : ℕ → List (List CLit))
    (hVC : ∀ off, (validC off).length = (rulerOf (validCountP tm sp) z).length)
    (hj : (levIdxAt tm sp jU z).length < (flatLayoutOf tm sp (pairFst z)).n)
    (hp : p < (rulerOf (validCountP tm sp) z).length
      + (rulerOf (C 4 * widthP tm sp) z).length
      + (rulerOf (C 4 * widthP tm sp) z).length
      + (rulerOf (C 4 * widthP tm sp) z).length
      + (rulerOf (C 4 * widthP tm sp) z).length + 2)
    (hvalid : ∀ q, q < (rulerOf (validCountP tm sp) z).length →
      ((validC ((flatLayoutOf tm sp (pairFst z)).mid
          (levIdxAt tm sp jU z).length))[q]?).map DataEncode.bitstringEncode
        = some (validEncAt tm sp (levMidU tm sp (levIdxAt tm sp jU z) z)
            (List.replicate q true) z)) :
    (((flatLayoutOf tm sp (pairFst z)).levelClauses validC
        (levIdxAt tm sp jU z).length)[p]?).map DataEncode.bitstringEncode
      = some (levelEncAt tm sp jU (List.replicate p true) z) := by
  have hW : (rulerOf (widthP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).W := by rw [rulerOf_length', flatLayoutOf_W]
  rw [levelEncAt]
  exact levelEnc_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (flatLayoutOf tm sp (pairFst z)) validC (levIdxAt tm sp jU z).length hVC
    (by rw [rulerOf_length', flatLayoutOf_W]; simp only [eval_mul, eval_C]; ring) hW
    (levYU_length tm sp _ z) (levYSuccU_length tm sp _ z)
    (by rw [levBlkU_length, FlatLayout.eUA])
    (by rw [levBlkU_length, FlatLayout.eVM])
    (by rw [levBlkU_length, FlatLayout.eUM])
    (by rw [levBlkU_length, FlatLayout.eVB])
    (by rw [levBlkU_length, FlatLayout.uBlk]; ring)
    (by rw [levBlkU_length, FlatLayout.vBlk])
    (levMidU_length tm sp _ z) (levLeftU_length tm sp _ z) (levRightU_length tm sp _ z)
    (levYU_le_nvarP tm sp _ z hj) (levYSuccU_le_nvarP tm sp _ z hj)
    (levBlkU_le_nvarP tm sp 3 (by omega) _ z hj) (levBlkU_le_nvarP tm sp 4 (by omega) _ z hj)
    (levBlkU_le_nvarP tm sp 5 (by omega) _ z hj) (levBlkU_le_nvarP tm sp 6 (by omega) _ z hj)
    (levBlkU_le_nvarP tm sp 1 (by omega) _ z hj) (levBlkU_le_nvarP tm sp 2 (by omega) _ z hj)
    (levMidU_le_nvarP tm sp _ z hj) (levLeftU_le_nvarP tm sp _ z hj)
    (levRightU_le_nvarP tm sp _ z hj) hvalid p (by omega)

open Polynomial in
/-- **The base family's equality half at the machine's sizes, encoded.** -/
theorem baseEncAt_eq_half (sp : Polynomial ℕ) (pU : List Bool → List Bool) (p : ℕ)
    (z : List Bool) (hT : (horizonP sp).eval (pairFst z).length = T)
    (hpU : pU z = List.replicate p true) (hp : p < configWidth tm T * 2) :
    ((cfgBaseC tm T
        ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
        ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
        (flatLayoutOf tm sp (pairFst z)).scr)[p]?).map DataEncode.bitstringEncode
      = some (baseEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
          (rulerOf (scrP tm sp)) pU z) := by
  have hcw : configWidth tm T = (widthP tm sp).eval (pairFst z).length := by
    rw [widthP_eval, hT]
  have hL : (rulerOf (leftLastP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n := by
    rw [rulerOf_length', leftLastP_eval]
  have hR : (rulerOf (rightLastP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n := by
    rw [rulerOf_length', rightLastP_eval]
  have hS : ((rulerOf (scrP tm sp) z) ++ [false]).length
      = (flatLayoutOf tm sp (pairFst z)).scr + 1 := by
    rw [List.length_append, rulerOf_length', scrP_eval]
    rfl
  have hnv : (rulerOf (nvarP tm sp) z).length
      = (nvarP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  rw [baseEncAt, hpU, ← hL, ← hR]
  refine baseEnc_eq_value tm T _ _ _ _ _ _ (flatLayoutOf tm sp (pairFst z)).scr p hS
    (by rw [rulerOf_length', twoWidthP, hcw]; simp only [eval_mul, eval_C]; ring)
    (by rw [hL, hR] at *; exact hp) ?_ ?_
    (by
      rw [hS, hnv]
      have := scrP_le_nvarP tm sp (pairFst z).length
      rw [scrP_eval] at this
      omega)
  · rw [hL, hnv]
    have := leftLastP_le_nvarP tm sp (pairFst z).length
    rw [leftLastP_eval] at this
    have hcw2 : (widthP tm sp).eval (pairFst z).length = configWidth tm T := hcw.symm
    omega
  · rw [hR, hnv]
    have := rightLastP_le_nvarP tm sp (pairFst z).length
    rw [rightLastP_eval] at this
    have hcw2 : (widthP tm sp).eval (pairFst z).length = configWidth tm T := hcw.symm
    omega

open Polynomial in
/-- **The base family's step half at the machine's sizes, encoded.** -/
theorem baseEncAt_step_half (sp : Polynomial ℕ) (pU : List Bool → List Bool) (p : ℕ)
    (z : List Bool) (hT : (horizonP sp).eval (pairFst z).length = T)
    (hpU : pU z = List.replicate p true) (hp : configWidth tm T * 2 ≤ p)
    (hstep : ((stepClauses tm T
        ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
        ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
        (flatLayoutOf tm sp (pairFst z)).scr)[p - configWidth tm T * 2]?).map
        DataEncode.bitstringEncode
      = some (stepEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
          (rulerOf (scrP tm sp))
          (fun w => (pU w).drop (rulerOf (twoWidthP tm sp) w).length) z)) :
    ((cfgBaseC tm T
        ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
        ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
        (flatLayoutOf tm sp (pairFst z)).scr)[p]?).map DataEncode.bitstringEncode
      = some (baseEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
          (rulerOf (scrP tm sp)) pU z) := by
  have hcw : configWidth tm T = (widthP tm sp).eval (pairFst z).length := by
    rw [widthP_eval, hT]
  have hL : (rulerOf (leftLastP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n := by
    rw [rulerOf_length', leftLastP_eval]
  have hR : (rulerOf (rightLastP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n := by
    rw [rulerOf_length', rightLastP_eval]
  have hS : ((rulerOf (scrP tm sp) z) ++ [false]).length
      = (flatLayoutOf tm sp (pairFst z)).scr + 1 := by
    rw [List.length_append, rulerOf_length', scrP_eval]
    rfl
  have hnv : (rulerOf (nvarP tm sp) z).length
      = (nvarP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  rw [baseEncAt, hpU, ← hL, ← hR]
  exact baseEnc_step_value tm T _ _ _ _ _ _ (flatLayoutOf tm sp (pairFst z)).scr p hS
    (by rw [rulerOf_length', twoWidthP, hcw]; simp only [eval_mul, eval_C]; ring)
    (by rw [hL, hR] at *; exact hp)
    (by
      rw [hS, hnv]
      have := scrP_le_nvarP tm sp (pairFst z).length
      rw [scrP_eval] at this
      omega)
    (by rw [hL, hR] at *; exact hstep)

open Polynomial in
/-- The validity clauses of a level's midpoint block, encoded. -/
theorem validEncAt_mid_eq (sp : Polynomial ℕ) (jU : List Bool) (p : ℕ) (z : List Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T) (hcard : 0 < Fintype.card tm.Q)
    (hj : jU.length < (flatLayoutOf tm sp (pairFst z)).n)
    (hp : p < (validCountP tm sp).eval (pairFst z).length) :
    ((cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length)
        ((flatLayoutOf tm sp (pairFst z)).mid jU.length))[p]?).map
        DataEncode.bitstringEncode
      = some (validEncAt tm sp (levMidU tm sp jU z) (List.replicate p true) z) := by
  have hvc : (validCountP tm sp).eval (pairFst z).length
      = 1 + Fintype.card tm.Q * Fintype.card tm.Q + (k + 2) * tapeBlockSize T := by
    rw [validCountP_eval tm sp _ (pairFst z) (sp.eval (pairFst z).length) 0,
      cfgValidC_length, hT]
  have hmid : (levMidU tm sp jU z).length
      = (flatLayoutOf tm sp (pairFst z)).mid jU.length := levMidU_length tm sp jU z
  have h := validEncAt_eq tm T sp (levMidU tm sp jU z) p z hT hcard
    (by rw [← hvc]; exact hp)
    (by
      have hb := levMidU_le_nvarP tm sp jU z hj
      rw [rulerOf_length', rulerOf_length'] at hb
      rw [← hT, ← widthP_eval]
      exact hb)
  rw [hmid] at h
  exact h

open Polynomial in
/-- **A guard clause at the machine's sizes, with the validity families discharged.** -/
theorem guardEncAt_eq' (sp : Polynomial ℕ) (p : ℕ) (z : List Bool)
    (init : Fin (flatLayoutOf tm sp (pairFst z)).W → Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T) (hcard : 0 < Fintype.card tm.Q)
    (hWc : (flatLayoutOf tm sp (pairFst z)).W = configWidth tm T)
    (hinit : ∀ (r : ℕ) (hr : r < (flatLayoutOf tm sp (pairFst z)).W), init ⟨r, hr⟩
      = ConfigAtom.value (Cfg.init tm.qstart (pairFst z))
        ((configAtomEquiv tm T).symm ⟨r, by rw [← hWc]; exact hr⟩))
    (hp : p < (flatLayoutOf tm sp (pairFst z)).W
      + ((validCountP tm sp).eval (pairFst z).length
        + ((validCountP tm sp).eval (pairFst z).length + (2 + 1)))) :
    (((flatLayoutOf tm sp (pairFst z)).guardClauses
        (cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length)) (cfgAccC tm T)
        init)[p]?).map DataEncode.bitstringEncode
      = some (guardEncAt tm sp (List.replicate p true) z) := by
  have hW : (rulerOf (widthP tm sp) z).length = (flatLayoutOf tm sp (pairFst z)).W := by
    rw [rulerOf_length', flatLayoutOf_W]
  have hvc : (rulerOf (validCountP tm sp) z).length
      = (validCountP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  exact guardEncAt_eq tm T sp p z _ init hT
    (fun off => by
      rw [cfgValidC_length,
        validCountP_eval tm sp _ (pairFst z) (sp.eval (pairFst z).length) off,
        cfgValidC_length, hT])
    hWc hinit hp
    (fun h₁ h₂ => by
      rw [List.drop_replicate]
      exact validEncAt_zero_eq tm T sp (p - (rulerOf (widthP tm sp) z).length) z hT hcard
        (by rw [← hvc]; omega))
    (fun h₁ h₂ => by
      rw [List.drop_replicate, List.drop_replicate]
      exact validEncAt_bStart_eq tm T sp
        (p - (rulerOf (widthP tm sp) z).length - (rulerOf (validCountP tm sp) z).length) z
        hT hcard (by rw [← hvc]; omega))

open Polynomial in
/-- **A level clause at the machine's sizes, with the validity family discharged.** -/
theorem levelEncAt_eq' (sp : Polynomial ℕ) (jU : List Bool) (p : ℕ) (z : List Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T) (hcard : 0 < Fintype.card tm.Q)
    (hj : (levIdxAt tm sp jU z).length < (flatLayoutOf tm sp (pairFst z)).n)
    (hp : p < (rulerOf (validCountP tm sp) z).length
      + (rulerOf (C 4 * widthP tm sp) z).length
      + (rulerOf (C 4 * widthP tm sp) z).length
      + (rulerOf (C 4 * widthP tm sp) z).length
      + (rulerOf (C 4 * widthP tm sp) z).length + 2) :
    (((flatLayoutOf tm sp (pairFst z)).levelClauses
        (cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length))
        (levIdxAt tm sp jU z).length)[p]?).map DataEncode.bitstringEncode
      = some (levelEncAt tm sp jU (List.replicate p true) z) := by
  have hvc : (rulerOf (validCountP tm sp) z).length
      = (validCountP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  exact levelEncAt_eq tm sp jU p z _
    (fun off => by
      rw [cfgValidC_length, hvc,
        validCountP_eval tm sp _ (pairFst z) (sp.eval (pairFst z).length) off,
        cfgValidC_length, hT])
    hj hp
    (fun q hq => validEncAt_mid_eq tm T sp (levIdxAt tm sp jU z) q z hT hcard hj
      (by rw [← hvc]; exact hq))

open Polynomial in
/-- **A base clause at the machine's sizes, both halves.** -/
theorem baseEncAt_eq' (sp : Polynomial ℕ) (pU : List Bool → List Bool) (p : ℕ)
    (z : List Bool) (hT : (horizonP sp).eval (pairFst z).length = T)
    (hpU : pU z = List.replicate p true)
    (hstep : configWidth tm T * 2 ≤ p →
      ((stepClauses tm T
          ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
          ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
          (flatLayoutOf tm sp (pairFst z)).scr)[p - configWidth tm T * 2]?).map
          DataEncode.bitstringEncode
        = some (stepEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
            (rulerOf (scrP tm sp))
            (fun w => (pU w).drop (rulerOf (twoWidthP tm sp) w).length) z)) :
    ((cfgBaseC tm T
        ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
        ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
        (flatLayoutOf tm sp (pairFst z)).scr)[p]?).map DataEncode.bitstringEncode
      = some (baseEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
          (rulerOf (scrP tm sp)) pU z) := by
  by_cases h : p < configWidth tm T * 2
  · exact baseEncAt_eq_half tm T sp pU p z hT hpU h
  · exact baseEncAt_step_half tm T sp pU p z hT hpU (by omega) (hstep (by omega))

/-! ## The whole matrix at the machine's sizes -/

open Polynomial in
/-- A clause index, less the guard family. -/
noncomputable def matRegU (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  pU.drop (rulerOf (guardCountP tm sp) z).length

open Polynomial in
/-- The level a clause of the level region belongs to. -/
noncomputable def matLevU (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  divFn2 (pair (rulerOf (levelCountP tm sp) z) (matRegU tm sp pU z))

open Polynomial in
/-- The clause's index inside its level. -/
noncomputable def matInLevU (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  modFn2 (pair (rulerOf (levelCountP tm sp) z) (matRegU tm sp pU z))

open Polynomial in
/-- The clause's index inside the base family. -/
noncomputable def matBaseU (sp : Polynomial ℕ) (pU z : List Bool) : List Bool :=
  (matRegU tm sp pU z).drop
    (mulLen (rulerOf (levelCountP tm sp) z) (rulerOf (levelsP tm sp) z)).length

open Polynomial in
theorem matRegU_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => matRegU tm sp (pU z) z) ∈ FP :=
  dropLenFn_mem_FP (rulerOf_mem_FP _) hp

open Polynomial in
theorem matLevU_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => matLevU tm sp (pU z) z) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP (rulerOf_mem_FP _)
    (matRegU_mem_FP tm sp hp)) divFn2_mem_FP) fun _ => rfl

open Polynomial in
theorem matInLevU_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => matInLevU tm sp (pU z) z) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP (rulerOf_mem_FP _)
    (matRegU_mem_FP tm sp hp)) modFn2_mem_FP) fun _ => rfl

open Polynomial in
theorem matBaseU_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => matBaseU tm sp (pU z) z) ∈ FP :=
  dropLenFn_mem_FP (mulLen_mem_FP (rulerOf_mem_FP _) (rulerOf_mem_FP _))
    (matRegU_mem_FP tm sp hp)

open Polynomial in
/-- One clause of the flat matrix, encoded from its index. -/
noncomputable def matrixEncAt (sp : Polynomial ℕ) (pU : List Bool → List Bool)
    (z : List Bool) : List Bool :=
  matrixEnc (guardEncAt tm sp (pU z) z)
    (baseEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
      (rulerOf (scrP tm sp)) (fun w => matBaseU tm sp (pU w) w) z)
    (levelEncAt tm sp (matLevU tm sp (pU z) z) (matInLevU tm sp (pU z) z) z)
    (rulerOf (nvarP tm sp) z) (rulerOf (guardCountP tm sp) z)
    (rulerOf (levelCountP tm sp) z) (rulerOf (levelsP tm sp) z)
    (rulerOf (yLastP tm sp) z) (pU z)

open Polynomial in
theorem matrixEncAt_mem_FP (sp : Polynomial ℕ) {pU : List Bool → List Bool} (hp : pU ∈ FP) :
    (fun z => matrixEncAt tm sp pU z) ∈ FP :=
  matrixEnc_mem_FP (guardEncAt_mem_FP tm sp hp)
    (baseEncAt_mem_FP' tm sp (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _)
      (matBaseU_mem_FP tm sp hp))
    (levelEncAt_mem_FP tm sp (matLevU_mem_FP tm sp hp) (matInLevU_mem_FP tm sp hp))
    (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _) (rulerOf_mem_FP _)
    (rulerOf_mem_FP _) hp

open Polynomial in
/-- **A clause of the whole matrix, encoded**, given that each family's clause is. -/
theorem matrixEncAt_eq (sp : Polynomial ℕ) (pU : List Bool → List Bool) (z : List Bool)
    (L : FlatLayout) (validC : ℕ → List (List CLit))
    (baseC : ℕ → ℕ → ℕ → List (List CLit)) (accC : ℕ → List (List CLit))
    (init : Fin L.W → Bool) (VC AC : ℕ)
    (hVC : ∀ off, (validC off).length = VC) (hAC : ∀ off, (accC off).length = AC)
    (hLC : ∀ j, (L.levelClauses validC j).length
      = (levelCountP tm sp).eval (pairFst z).length)
    (hgc : (guardCountP tm sp).eval (pairFst z).length = L.W + (VC + (VC + (AC + 1))))
    (hn : (levelsP tm sp).eval (pairFst z).length = L.n)
    (hy : (yLastP tm sp).eval (pairFst z).length = L.yAt L.n)
    (hyle : L.yAt L.n ≤ (nvarP tm sp).eval (pairFst z).length)
    (hguardv : (pU z).length < (guardCountP tm sp).eval (pairFst z).length →
      ((L.guardClauses validC accC init)[(pU z).length]?).map DataEncode.bitstringEncode
        = some (guardEncAt tm sp (pU z) z))
    (hlevelv : (guardCountP tm sp).eval (pairFst z).length ≤ (pU z).length →
      (pU z).length < (guardCountP tm sp).eval (pairFst z).length
        + (levelCountP tm sp).eval (pairFst z).length * L.n →
      ((L.levelClauses validC (((pU z).length
          - (guardCountP tm sp).eval (pairFst z).length)
          / (levelCountP tm sp).eval (pairFst z).length))[((pU z).length
          - (guardCountP tm sp).eval (pairFst z).length)
          % (levelCountP tm sp).eval (pairFst z).length]?).map DataEncode.bitstringEncode
        = some (levelEncAt tm sp (matLevU tm sp (pU z) z) (matInLevU tm sp (pU z) z) z))
    (hbasev : (guardCountP tm sp).eval (pairFst z).length
        + (levelCountP tm sp).eval (pairFst z).length * L.n ≤ (pU z).length →
      ((baseC (L.leftOf L.n) (L.rightOf L.n) L.scr)[(pU z).length
          - (guardCountP tm sp).eval (pairFst z).length
          - (levelCountP tm sp).eval (pairFst z).length * L.n]?).map
          DataEncode.bitstringEncode
        = some (baseEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
            (rulerOf (scrP tm sp)) (fun w => matBaseU tm sp (pU w) w) z))
    (hrep : pU z = List.replicate (pU z).length true) :
    ((L.fullClauses validC baseC accC init)[(pU z).length]?).map DataEncode.bitstringEncode
      = some (matrixEncAt tm sp pU z) := by
  have hlcpos : 0 < (levelCountP tm sp).eval (pairFst z).length := by
    simp only [levelCountP, eval_add, eval_mul, eval_C]
    omega
  have hgcr : (rulerOf (guardCountP tm sp) z).length
      = (guardCountP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  have hlcr : (rulerOf (levelCountP tm sp) z).length
      = (levelCountP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  have hnr : (rulerOf (levelsP tm sp) z).length = L.n := by rw [rulerOf_length']; exact hn
  have hyr : (rulerOf (yLastP tm sp) z).length = L.yAt L.n := by
    rw [rulerOf_length']; exact hy
  have hwr : (rulerOf (nvarP tm sp) z).length
      = (nvarP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  rw [matrixEncAt]
  by_cases hg : (pU z).length < (guardCountP tm sp).eval (pairFst z).length
  · rw [L.fullClauses_getElem?_guard validC baseC accC VC AC hVC hAC init
      (p := (pU z).length) (by rw [← hgc]; exact hg)]
    conv_rhs => rw [hrep]
    rw [matrixEnc_guard_eq _ _ _ _ _ _ _ _ (pU z).length (by rw [hgcr]; exact hg), ← hrep]
    exact hguardv hg
  · rw [L.fullClauses_getElem?_tail validC baseC accC VC AC hVC hAC init
      (p := (pU z).length) (by rw [← hgc]; omega)]
    by_cases hl : (pU z).length < (guardCountP tm sp).eval (pairFst z).length
        + (levelCountP tm sp).eval (pairFst z).length * L.n
    · rw [← hgc,
        L.tailClauses_getElem?_lev validC baseC
          ((levelCountP tm sp).eval (pairFst z).length) hlcpos hLC L.n 0
          ((pU z).length - (guardCountP tm sp).eval (pairFst z).length) (by omega),
        Nat.zero_add]
      conv_rhs => rw [hrep]
      rw [matrixEnc_level_eq _ _ _ _ _ _ _ _ (pU z).length (by rw [hgcr]; omega)
        (by rw [hgcr, hlcr, hnr]; exact hl), ← hrep]
      have h := hlevelv (by omega) hl
      rw [matLevU, matInLevU, matRegU, hrep] at *
      exact h
    · rw [← hgc,
        L.tailClauses_getElem?_base validC baseC
          ((levelCountP tm sp).eval (pairFst z).length) hLC L.n 0
          ((pU z).length - (guardCountP tm sp).eval (pairFst z).length) (by omega),
        Nat.zero_add, QBF.disjLit_getElem?]
      conv_rhs => rw [hrep]
      rw [matrixEnc_base_eq _ _ _ _ _ _ _ _ (pU z).length
        (by rw [hgcr, hlcr, hnr]; omega)]
      have h := hbasev (by omega)
      rcases hc : (baseC (L.leftOf L.n) (L.rightOf L.n) L.scr)[(pU z).length
          - (guardCountP tm sp).eval (pairFst z).length
          - (levelCountP tm sp).eval (pairFst z).length * L.n]? with _ | cl
      · rw [hc] at h
        exact absurd h (by simp)
      · rw [hc] at h
        rw [Option.map_some, Option.map_some, ← Option.some.inj h,
          consLitEnc_eq false cl (by rw [litEnc_neg', hyr, Nat.min_eq_left (by omega)]),
          hyr]

open Polynomial in
/-- The clamp on a level index does not move an index that is already a level. -/
theorem levIdxAt_length (sp : Polynomial ℕ) (jU z : List Bool)
    (h : jU.length ≤ (levelsP tm sp).eval (pairFst z).length) :
    (levIdxAt tm sp jU z).length = jU.length := by
  rw [levIdxAt, List.length_take, rulerOf_length']
  omega

open Polynomial in
theorem levIdxAt_lt (sp : Polynomial ℕ) (jU z : List Bool)
    (h : jU.length < (flatLayoutOf tm sp (pairFst z)).n) :
    (levIdxAt tm sp jU z).length < (flatLayoutOf tm sp (pairFst z)).n := by
  rw [levIdxAt, List.length_take, rulerOf_length']
  omega

open Polynomial in
theorem matRegU_length (sp : Polynomial ℕ) (pU z : List Bool) :
    (matRegU tm sp pU z).length
      = pU.length - (guardCountP tm sp).eval (pairFst z).length := by
  rw [matRegU, List.length_drop, rulerOf_length']

open Polynomial in
theorem matLevU_length (sp : Polynomial ℕ) (pU z : List Bool) :
    (matLevU tm sp pU z).length
      = (pU.length - (guardCountP tm sp).eval (pairFst z).length)
        / (levelCountP tm sp).eval (pairFst z).length := by
  have hpos : 0 < (rulerOf (levelCountP tm sp) z).length := by
    rw [rulerOf_length']
    simp only [levelCountP, eval_add, eval_mul, eval_C]
    omega
  rw [matLevU, divFn2_eq hpos, List.length_replicate, matRegU_length, rulerOf_length']

open Polynomial in
theorem matInLevU_length (sp : Polynomial ℕ) (pU z : List Bool) :
    (matInLevU tm sp pU z).length
      = (pU.length - (guardCountP tm sp).eval (pairFst z).length)
        % (levelCountP tm sp).eval (pairFst z).length := by
  have hpos : 0 < (rulerOf (levelCountP tm sp) z).length := by
    rw [rulerOf_length']
    simp only [levelCountP, eval_add, eval_mul, eval_C]
    omega
  rw [matInLevU, modFn2_eq hpos, List.length_replicate, matRegU_length, rulerOf_length']

open Polynomial in
theorem matBaseU_length (sp : Polynomial ℕ) (pU z : List Bool) :
    (matBaseU tm sp pU z).length
      = pU.length - (guardCountP tm sp).eval (pairFst z).length
        - (levelCountP tm sp).eval (pairFst z).length
          * (levelsP tm sp).eval (pairFst z).length := by
  rw [matBaseU, List.length_drop, matRegU_length, length_mulLen, rulerOf_length',
    rulerOf_length']

open Polynomial in
/-- A base index inside the matrix names a step clause inside the step family. -/
theorem matBaseU_step_lt (sp : Polynomial ℕ) (pU z : List Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T)
    (hp : pU.length < (matrixCountP tm sp).eval (pairFst z).length) :
    (matBaseU tm sp pU z).length - configWidth tm T * 2
      < (viewCountP tm sp).eval (pairFst z).length
          * (viewClauseP tm sp).eval (pairFst z).length
        + (k + 2) * ((T + 1) * ((T + 2) * (4 * 2))) := by
  have hcw : configWidth tm T = (widthP tm sp).eval (pairFst z).length := by
    rw [widthP_eval, hT]
  have hmc : (matrixCountP tm sp).eval (pairFst z).length
      = (guardCountP tm sp).eval (pairFst z).length
        + (levelCountP tm sp).eval (pairFst z).length
          * (levelsP tm sp).eval (pairFst z).length
        + (baseCountP tm sp).eval (pairFst z).length := by
    simp only [matrixCountP, eval_add, eval_mul]
  have hbc : (baseCountP tm sp).eval (pairFst z).length
      = 2 * (widthP tm sp).eval (pairFst z).length
        + ((viewCountP tm sp).eval (pairFst z).length
            * (viewClauseP tm sp).eval (pairFst z).length
          + (k + 2) * ((T + 1) * ((T + 2) * (4 * 2)))) := by
    simp only [baseCountP, tapesP, frameTapeP_eval, eval_add, eval_mul, eval_C, hT]
  have hcomm : configWidth tm T * 2 = 2 * (widthP tm sp).eval (pairFst z).length := by
    rw [hcw]
    ring
  have hgpos : 0 < (k + 2) * ((T + 1) * ((T + 2) * (4 * 2))) := by positivity
  rw [matBaseU_length]
  omega

open Polynomial in
/-- **The step clause of a base index at the machine's sizes.** -/
theorem stepEncAt_base_value (sp : Polynomial ℕ) (pU : List Bool → List Bool)
    (z : List Bool)
    (hT : (horP sp).eval (pairFst z).length = T + 1)
    (hT2 : (hor2P sp).eval (pairFst z).length = T + 2)
    (hhd : (headBlockP (k := k) sp).eval (pairFst z).length = (k + 2) * (T + 1))
    (hviewC : (viewCountP tm sp).eval (pairFst z).length = (viewList tm T).length)
    (hvc : (viewClauseP tm sp).eval (pairFst z).length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4))
    (hrep : matBaseU tm sp (pU z) z
      = List.replicate (matBaseU tm sp (pU z) z).length true)
    (hw2 : (rulerOf (twoWidthP tm sp) z).length = configWidth tm T * 2)
    (hlt : (matBaseU tm sp (pU z) z).length - configWidth tm T * 2
      < (viewCountP tm sp).eval (pairFst z).length
          * (viewClauseP tm sp).eval (pairFst z).length
        + (k + 2) * ((T + 1) * ((T + 2) * (4 * 2)))) :
    ((stepClauses tm T
        ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
        ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
        (flatLayoutOf tm sp (pairFst z)).scr)[(matBaseU tm sp (pU z) z).length
        - configWidth tm T * 2]?).map DataEncode.bitstringEncode
      = some (stepEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
          (rulerOf (scrP tm sp))
          (fun w => (matBaseU tm sp (pU w) w).drop
            (rulerOf (twoWidthP tm sp) w).length) z) := by
  have hL : (rulerOf (leftLastP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n := by
    rw [rulerOf_length', leftLastP_eval]
  have hR : (rulerOf (rightLastP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n := by
    rw [rulerOf_length', rightLastP_eval]
  have hS : (rulerOf (scrP tm sp) z).length
      = (flatLayoutOf tm sp (pairFst z)).scr := by rw [rulerOf_length', scrP_eval]
  have hidx : ((matBaseU tm sp (pU z) z).drop
      (rulerOf (twoWidthP tm sp) z).length).length
      = (matBaseU tm sp (pU z) z).length - configWidth tm T * 2 := by
    rw [List.length_drop, hw2]
  have hnv : (rulerOf (nvarP tm sp) z).length
      = (nvarP tm sp).eval (pairFst z).length := rulerOf_length' _ _
  have hhz : (horizonP sp).eval (pairFst z).length = T := by
    rw [horP_eval] at hT
    omega
  have hcw : configWidth tm T = (widthP tm sp).eval (pairFst z).length := by
    rw [widthP_eval, hhz]
  have h := stepEncAt_value tm T sp (rulerOf (leftLastP tm sp))
    (rulerOf (rightLastP tm sp)) (rulerOf (scrP tm sp))
    (fun w => (matBaseU tm sp (pU w) w).drop (rulerOf (twoWidthP tm sp) w).length) z
    hT hT2 hhd hviewC hvc (by rw [hidx]; exact hlt)
    (by
      show (matBaseU tm sp (pU z) z).drop (rulerOf (twoWidthP tm sp) z).length
        = List.replicate ((matBaseU tm sp (pU z) z).drop
          (rulerOf (twoWidthP tm sp) z).length).length true
      rw [hrep, List.drop_replicate, List.length_replicate])
    (by
      rw [hS, ← scrP_eval]
      have := scrP_le_nvarP tm sp (pairFst z).length
      omega)
    (by
      rw [hL, ← leftLastP_eval, hcw]
      exact leftLastP_le_nvarP tm sp _)
    (by
      rw [hR, ← rightLastP_eval, hcw]
      exact rightLastP_le_nvarP tm sp _)
  rw [hL, hR, hS, hidx] at h
  exact h

open Polynomial in
/-- **A clause of the matrix at the machine's sizes**, with every size discharged. -/
theorem matrixEncAt_eq' (sp : Polynomial ℕ) (pU : List Bool → List Bool) (z : List Bool)
    (init : Fin (flatLayoutOf tm sp (pairFst z)).W → Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T)
    (hrep : pU z = List.replicate (pU z).length true)
    (hguardv : (pU z).length < (guardCountP tm sp).eval (pairFst z).length →
      (((flatLayoutOf tm sp (pairFst z)).guardClauses
          (cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length)) (cfgAccC tm T)
          init)[(pU z).length]?).map DataEncode.bitstringEncode
        = some (guardEncAt tm sp (pU z) z))
    (hlevelv : (guardCountP tm sp).eval (pairFst z).length ≤ (pU z).length →
      (pU z).length < (guardCountP tm sp).eval (pairFst z).length
        + (levelCountP tm sp).eval (pairFst z).length
          * (flatLayoutOf tm sp (pairFst z)).n →
      (((flatLayoutOf tm sp (pairFst z)).levelClauses
          (cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length))
          (((pU z).length - (guardCountP tm sp).eval (pairFst z).length)
            / (levelCountP tm sp).eval (pairFst z).length))[((pU z).length
            - (guardCountP tm sp).eval (pairFst z).length)
            % (levelCountP tm sp).eval (pairFst z).length]?).map
          DataEncode.bitstringEncode
        = some (levelEncAt tm sp (matLevU tm sp (pU z) z) (matInLevU tm sp (pU z) z) z))
    (hbasev : (guardCountP tm sp).eval (pairFst z).length
        + (levelCountP tm sp).eval (pairFst z).length
          * (flatLayoutOf tm sp (pairFst z)).n ≤ (pU z).length →
      ((cfgBaseC tm T
          ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
          ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
          (flatLayoutOf tm sp (pairFst z)).scr)[(pU z).length
          - (guardCountP tm sp).eval (pairFst z).length
          - (levelCountP tm sp).eval (pairFst z).length
            * (flatLayoutOf tm sp (pairFst z)).n]?).map DataEncode.bitstringEncode
        = some (baseEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
            (rulerOf (scrP tm sp)) (fun w => matBaseU tm sp (pU w) w) z)) :
    (((flatLayoutOf tm sp (pairFst z)).fullClauses
        (cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length)) (cfgBaseC tm T)
        (cfgAccC tm T) init)[(pU z).length]?).map DataEncode.bitstringEncode
      = some (matrixEncAt tm sp pU z) :=
  matrixEncAt_eq tm sp pU z (flatLayoutOf tm sp (pairFst z)) _ _ _ init
    ((validCountP tm sp).eval (pairFst z).length) 2
    (fun off => by
      rw [cfgValidC_length,
        validCountP_eval tm sp _ (pairFst z) (sp.eval (pairFst z).length) off,
        cfgValidC_length, hT])
    (fun off => cfgAccC_length tm T off)
    (fun j => by
      rw [← hT]
      exact (levelCountP_eval tm sp (pairFst z) j).symm)
    (guardCountP_eval_layout tm sp (pairFst z))
    (flatLayoutOf_n tm sp (pairFst z))
    (yLastP_eval tm sp (pairFst z))
    (by
      rw [← yLastP_eval]
      exact yLastP_le_nvarP tm sp _)
    hguardv hlevelv hbasev hrep

open Polynomial in
/-- **The level region of the matrix, encoded.** -/
theorem matrix_level_value (sp : Polynomial ℕ) (pU : List Bool → List Bool) (z : List Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T) (hcard : 0 < Fintype.card tm.Q)
    (h₂ : (pU z).length < (guardCountP tm sp).eval (pairFst z).length
      + (levelCountP tm sp).eval (pairFst z).length
        * (flatLayoutOf tm sp (pairFst z)).n) :
    (((flatLayoutOf tm sp (pairFst z)).levelClauses
        (cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length))
        (((pU z).length - (guardCountP tm sp).eval (pairFst z).length)
          / (levelCountP tm sp).eval (pairFst z).length))[((pU z).length
          - (guardCountP tm sp).eval (pairFst z).length)
          % (levelCountP tm sp).eval (pairFst z).length]?).map DataEncode.bitstringEncode
      = some (levelEncAt tm sp (matLevU tm sp (pU z) z)
          (matInLevU tm sp (pU z) z) z) := by
  have hlcpos : 0 < (levelCountP tm sp).eval (pairFst z).length := by
    simp only [levelCountP, eval_add, eval_mul, eval_C]
    omega
  have hcomm : (levelCountP tm sp).eval (pairFst z).length
      * (flatLayoutOf tm sp (pairFst z)).n
      = (flatLayoutOf tm sp (pairFst z)).n
        * (levelCountP tm sp).eval (pairFst z).length := Nat.mul_comm _ _
  have hnpos : 0 < (flatLayoutOf tm sp (pairFst z)).n := by
    rw [flatLayoutOf_n]
    have := levelsP_eval_succ tm sp (pairFst z).length
    omega
  have hprod : 0 < (flatLayoutOf tm sp (pairFst z)).n
      * (levelCountP tm sp).eval (pairFst z).length := Nat.mul_pos hnpos hlcpos
  have hlev : (matLevU tm sp (pU z) z).length
      < (flatLayoutOf tm sp (pairFst z)).n := by
    rw [matLevU_length]
    exact Nat.div_lt_of_lt_mul (by omega)
  have hlev' : (matLevU tm sp (pU z) z).length
      ≤ (levelsP tm sp).eval (pairFst z).length := by
    rw [← flatLayoutOf_n]
    omega
  have hidx : (levIdxAt tm sp (matLevU tm sp (pU z) z) z).length
      = ((pU z).length - (guardCountP tm sp).eval (pairFst z).length)
        / (levelCountP tm sp).eval (pairFst z).length := by
    rw [levIdxAt_length tm sp _ z hlev', matLevU_length]
  have hrep : matInLevU tm sp (pU z) z
      = List.replicate (matInLevU tm sp (pU z) z).length true := by
    have hpos : 0 < (rulerOf (levelCountP tm sp) z).length := by
      rw [rulerOf_length']; exact hlcpos
    rw [matInLevU, modFn2_eq hpos, List.length_replicate]
  have h := levelEncAt_eq' tm T sp (matLevU tm sp (pU z) z)
    (matInLevU tm sp (pU z) z).length z hT hcard (levIdxAt_lt tm sp _ z hlev)
    (by
      have hmod : ((pU z).length - (guardCountP tm sp).eval (pairFst z).length)
          % (levelCountP tm sp).eval (pairFst z).length
          < (levelCountP tm sp).eval (pairFst z).length := Nat.mod_lt _ hlcpos
      rw [matInLevU_length]
      simp only [rulerOf_length', levelCountP, eval_add, eval_mul, eval_C] at hmod ⊢
      omega)
  rw [hidx, matInLevU_length] at h
  rw [h, ← matInLevU_length, ← hrep]

open Polynomial in
/-- **The guard region of the matrix, encoded.** -/
theorem matrix_guard_value (sp : Polynomial ℕ) (pU : List Bool → List Bool) (z : List Bool)
    (init : Fin (flatLayoutOf tm sp (pairFst z)).W → Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T) (hcard : 0 < Fintype.card tm.Q)
    (hWc : (flatLayoutOf tm sp (pairFst z)).W = configWidth tm T)
    (hinit : ∀ (r : ℕ) (hr : r < (flatLayoutOf tm sp (pairFst z)).W), init ⟨r, hr⟩
      = ConfigAtom.value (Cfg.init tm.qstart (pairFst z))
        ((configAtomEquiv tm T).symm ⟨r, by rw [← hWc]; exact hr⟩))
    (hrep : pU z = List.replicate (pU z).length true)
    (h : (pU z).length < (guardCountP tm sp).eval (pairFst z).length) :
    (((flatLayoutOf tm sp (pairFst z)).guardClauses
        (cfgValidC tm T (pairFst z) (sp.eval (pairFst z).length)) (cfgAccC tm T)
        init)[(pU z).length]?).map DataEncode.bitstringEncode
      = some (guardEncAt tm sp (pU z) z) := by
  have hg := guardEncAt_eq' tm T sp (pU z).length z init hT hcard hWc hinit
    (by rw [← guardCountP_eval_layout]; exact h)
  rw [← hrep] at hg
  exact hg

open Polynomial in
/-- **The base region of the matrix, encoded.** -/
theorem matrix_base_value (sp : Polynomial ℕ) (pU : List Bool → List Bool) (z : List Bool)
    (hT : (horizonP sp).eval (pairFst z).length = T)
    (hrep : pU z = List.replicate (pU z).length true)
    (hstep : configWidth tm T * 2 ≤ (matBaseU tm sp (pU z) z).length →
      ((stepClauses tm T
          ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
          ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
          (flatLayoutOf tm sp (pairFst z)).scr)[(matBaseU tm sp (pU z) z).length
          - configWidth tm T * 2]?).map DataEncode.bitstringEncode
        = some (stepEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
            (rulerOf (scrP tm sp))
            (fun w => (matBaseU tm sp (pU w) w).drop
              (rulerOf (twoWidthP tm sp) w).length) z)) :
    ((cfgBaseC tm T
        ((flatLayoutOf tm sp (pairFst z)).leftOf (flatLayoutOf tm sp (pairFst z)).n)
        ((flatLayoutOf tm sp (pairFst z)).rightOf (flatLayoutOf tm sp (pairFst z)).n)
        (flatLayoutOf tm sp (pairFst z)).scr)[(pU z).length
        - (guardCountP tm sp).eval (pairFst z).length
        - (levelCountP tm sp).eval (pairFst z).length
          * (flatLayoutOf tm sp (pairFst z)).n]?).map DataEncode.bitstringEncode
      = some (baseEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
          (rulerOf (scrP tm sp)) (fun w => matBaseU tm sp (pU w) w) z) := by
  have hrepb : matBaseU tm sp (pU z) z
      = List.replicate (matBaseU tm sp (pU z) z).length true := by
    rw [matBaseU, matRegU, hrep, List.drop_replicate, List.drop_replicate,
      List.length_replicate]
  have hidx : (matBaseU tm sp (pU z) z).length
      = (pU z).length - (guardCountP tm sp).eval (pairFst z).length
        - (levelCountP tm sp).eval (pairFst z).length
          * (flatLayoutOf tm sp (pairFst z)).n := by
    rw [matBaseU_length, flatLayoutOf_n]
  have hb := baseEncAt_eq' tm T sp (fun w => matBaseU tm sp (pU w) w)
    (matBaseU tm sp (pU z) z).length z hT hrepb hstep
  rw [hidx] at hb
  exact hb

open Polynomial in
/-- **A clause of the flat matrix at the machine's sizes, encoded.** -/
theorem matrixEncAt_value (sp : Polynomial ℕ) (pU : List Bool → List Bool) (z x : List Bool)
    (hx : pairFst z = x)
    (init : Fin (flatLayoutOf tm sp x).W → Bool)
    (hT : (horizonP sp).eval x.length = T) (hcard : 0 < Fintype.card tm.Q)
    (hWc : (flatLayoutOf tm sp x).W = configWidth tm T)
    (hinit : ∀ (r : ℕ) (hr : r < (flatLayoutOf tm sp x).W), init ⟨r, hr⟩
      = ConfigAtom.value (Cfg.init tm.qstart x)
        ((configAtomEquiv tm T).symm ⟨r, by rw [← hWc]; exact hr⟩))
    (hrep : pU z = List.replicate (pU z).length true)
    (hstep : configWidth tm T * 2 ≤ (matBaseU tm sp (pU z) z).length →
      ((stepClauses tm T
          ((flatLayoutOf tm sp x).leftOf (flatLayoutOf tm sp x).n)
          ((flatLayoutOf tm sp x).rightOf (flatLayoutOf tm sp x).n)
          (flatLayoutOf tm sp x).scr)[(matBaseU tm sp (pU z) z).length
          - configWidth tm T * 2]?).map DataEncode.bitstringEncode
        = some (stepEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
            (rulerOf (scrP tm sp))
            (fun w => (matBaseU tm sp (pU w) w).drop
              (rulerOf (twoWidthP tm sp) w).length) z)) :
    (((flatLayoutOf tm sp x).fullClauses
        (cfgValidC tm T x (sp.eval x.length)) (cfgBaseC tm T)
        (cfgAccC tm T) init)[(pU z).length]?).map DataEncode.bitstringEncode
      = some (matrixEncAt tm sp pU z) := by
  subst hx
  exact matrixEncAt_eq' tm T sp pU z init hT hrep
    (fun h => matrix_guard_value tm T sp pU z init hT hcard hWc hinit hrep h)
    (fun _ h₂ => matrix_level_value tm T sp pU z hT hcard h₂)
    (fun _ => matrix_base_value tm T sp pU z hT hrep hstep)

/-! ## The matrix, emitted -/

open Polynomial in
/-- The whole flat matrix, written out clause by clause. -/
noncomputable def matrixEmit (sp : Polynomial ℕ) (x : List Bool) : List Bool :=
  emitListAt (fun y => matrixEncAt tm sp pairSnd y) (polyRuler (matrixCountP tm sp) x) x

open Polynomial in
/-- **The emitted matrix is the flat matrix.** -/
theorem matrixEmit_eq (sp : Polynomial ℕ) (x : List Bool)
    (init : Fin (flatLayoutOf tm sp x).W → Bool)
    (hT : (horizonP sp).eval x.length = T) (hcard : 0 < Fintype.card tm.Q)
    (hWc : (flatLayoutOf tm sp x).W = configWidth tm T)
    (hinit : ∀ (r : ℕ) (hr : r < (flatLayoutOf tm sp x).W), init ⟨r, hr⟩
      = ConfigAtom.value (Cfg.init tm.qstart x)
        ((configAtomEquiv tm T).symm ⟨r, by rw [← hWc]; exact hr⟩))
    (hstep : ∀ i : ℕ, i < ((flatLayoutOf tm sp x).fullClauses
        (cfgValidC tm T x (sp.eval x.length)) (cfgBaseC tm T) (cfgAccC tm T) init).length →
      configWidth tm T * 2
          ≤ (matBaseU tm sp (pairSnd (pair x (List.replicate i true)))
            (pair x (List.replicate i true))).length →
      ((stepClauses tm T ((flatLayoutOf tm sp x).leftOf (flatLayoutOf tm sp x).n)
          ((flatLayoutOf tm sp x).rightOf (flatLayoutOf tm sp x).n)
          (flatLayoutOf tm sp x).scr)[(matBaseU tm sp
            (pairSnd (pair x (List.replicate i true)))
            (pair x (List.replicate i true))).length
          - configWidth tm T * 2]?).map DataEncode.bitstringEncode
        = some (stepEncAt tm sp (rulerOf (leftLastP tm sp)) (rulerOf (rightLastP tm sp))
            (rulerOf (scrP tm sp))
            (fun w => (matBaseU tm sp (pairSnd w) w).drop
              (rulerOf (twoWidthP tm sp) w).length)
            (pair x (List.replicate i true)))) :
    matrixEmit tm sp x
      = DataEncode.bitstringEncode ((flatLayoutOf tm sp x).fullClauses
          (cfgValidC tm T x (sp.eval x.length)) (cfgBaseC tm T) (cfgAccC tm T) init) := by
  refine emitListAt_eq' _ _ _ (by
    rw [polyRuler_length, matrixCountP_eval tm sp x init, ← hT]) (fun i hi => ?_)
  have hval := matrixEncAt_value tm T sp pairSnd (pair x (List.replicate i true)) x
    (pairFst_pair x _) init hT hcard hWc hinit
    (by rw [pairSnd_pair, List.length_replicate]) (hstep i hi)
  rw [pairSnd_pair, List.length_replicate, List.getElem?_eq_getElem hi,
    Option.map_some] at hval
  exact (Option.some.inj hval).symm

open Polynomial in
/-- **The emitted matrix is the flat matrix**, with every hypothesis discharged. -/
theorem matrixEmit_value (sp : Polynomial ℕ) (x : List Bool)
    (init : Fin (flatLayoutOf tm sp x).W → Bool)
    (hT : (horizonP sp).eval x.length = T) (hcard : 0 < Fintype.card tm.Q)
    (hWc : (flatLayoutOf tm sp x).W = configWidth tm T)
    (hinit : ∀ (r : ℕ) (hr : r < (flatLayoutOf tm sp x).W), init ⟨r, hr⟩
      = ConfigAtom.value (Cfg.init tm.qstart x)
        ((configAtomEquiv tm T).symm ⟨r, by rw [← hWc]; exact hr⟩)) :
    matrixEmit tm sp x
      = DataEncode.bitstringEncode ((flatLayoutOf tm sp x).fullClauses
          (cfgValidC tm T x (sp.eval x.length)) (cfgBaseC tm T) (cfgAccC tm T) init) := by
  have hT1 : (horP sp).eval x.length = T + 1 := by rw [horP_eval, hT]
  have hT2 : (hor2P sp).eval x.length = T + 2 := by rw [hor2P_eval, hT]
  have hhd : (headBlockP (k := k) sp).eval x.length = (k + 2) * (T + 1) := by
    rw [headBlockP_eval, hT]
  have hviewC : (viewCountP tm sp).eval x.length = (viewList tm T).length := by
    rw [viewList_length, viewCountP]
    simp only [eval_mul, eval_C, eval_pow, horP_eval, hT]
  have hvc : (viewClauseP tm sp).eval x.length
      = Fintype.card tm.Q + ((k + 2) * (T + 1) + (k + 2) * 4) := by
    simp only [viewClauseP, eval_add, eval_mul, eval_C, horP_eval, hT]
  have hcount : ((flatLayoutOf tm sp x).fullClauses
      (cfgValidC tm T x (sp.eval x.length)) (cfgBaseC tm T) (cfgAccC tm T) init).length
      = (matrixCountP tm sp).eval x.length := by
    rw [matrixCountP_eval tm sp x init, hT]
  refine matrixEmit_eq tm T sp x init hT hcard hWc hinit (fun i hi hge => ?_)
  have hpf : pairFst (pair x (List.replicate i true)) = x := pairFst_pair x _
  have hlen : (pairSnd (pair x (List.replicate i true))).length = i := by
    rw [pairSnd_pair, List.length_replicate]
  have hbv := stepEncAt_base_value tm T sp pairSnd (pair x (List.replicate i true))
    (by rw [hpf]; exact hT1) (by rw [hpf]; exact hT2)
    (by rw [hpf]; exact hhd) (by rw [hpf]; exact hviewC) (by rw [hpf]; exact hvc)
    (by
      rw [matBaseU, matRegU, pairSnd_pair, List.drop_replicate, List.drop_replicate,
        List.length_replicate])
    (by
      rw [rulerOf_length', hpf, twoWidthP]
      simp only [eval_mul, eval_C]
      have hcw : configWidth tm T = (widthP tm sp).eval x.length := by rw [widthP_eval, hT]
      omega)
    (matBaseU_step_lt tm T sp _ _ (by rw [hpf]; exact hT)
      (by rw [hlen, hpf, ← hcount]; exact hi))
  rw [hpf] at hbv
  exact hbv

open Polynomial in
theorem matrixEmit_mem_FP (sp : Polynomial ℕ) : (fun x => matrixEmit tm sp x) ∈ FP :=
  emitListAt_mem_FP (matrixEncAt_mem_FP tm sp Cobham.sndBlock_mem_FP)
    (polyRulerFn_mem_FP _ id_mem_FP) id_mem_FP

end Complexity
