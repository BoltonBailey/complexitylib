/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.PCP.Internal.Materialize

/-!
# Emitting an indexed list in polynomial time

⚠️ Unreviewed by Bolton

A list whose length is polynomial-time computable in unary and whose `i`-th entry is
polynomial-time computable from `i` in unary is polynomial-time encodable. This is the shape every
reduction that has to write down a large object takes: give a rule for one entry, get the whole
encoded list.

## Main results

- `emit_list_mem_FP`
-/

@[expose] public section

namespace Complexity

/-- **The list emitter.** An entry rule in `FP` and a unary length in `FP` give the encoded list
in `FP`. -/
theorem emit_list_mem_FP {α : Type} [DataEncode α] {E : List Bool → List Bool}
    {l : List Bool → List α} (hE : E ∈ FP)
    (hN : (fun x => List.replicate (l x).length true) ∈ FP)
    (hval : ∀ (x : List Bool) (i : ℕ) (hi : i < (l x).length),
      E (pair x (List.replicate i true)) = DataEncode.bitstringEncode ((l x)[i]'hi)) :
    (fun x => DataEncode.bitstringEncode (l x)) ∈ FP := by
  have hpair : (fun x => pair (List.replicate (l x).length true) x) ∈ FP :=
    Cobham.pairFn_mem_FP hN id_mem_FP
  have hcomp := mem_FP_comp hpair (materialize_mem_FP hE)
  refine mem_FP_of_eq hcomp fun x => ?_
  show listEncFn E (pair (List.replicate (l x).length true) x) = _
  exact materialize_eq (l x) x (hval x)

/-- An indexed family emitted as a single value: the function symbol behind
`emit_list_mem_FP`, so that a nested emission can appear inside a larger dispatch. -/
noncomputable def emitListAt (E : List Bool → List Bool) (nU z : List Bool) : List Bool :=
  listEncFn E (pair nU z)

theorem emitListAt_mem_FP {E : List Bool → List Bool} (hE : E ∈ FP)
    {nU z : List Bool → List Bool} (hn : nU ∈ FP) (hz : z ∈ FP) :
    (fun w => emitListAt E (nU w) (z w)) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp (Cobham.pairFn_mem_FP hn hz) (materialize_mem_FP hE))
    fun _ => rfl

theorem emitListAt_eq {α : Type} [DataEncode α] {E : List Bool → List Bool}
    (l : List α) (z : List Bool)
    (hval : ∀ (i : ℕ) (hi : i < l.length),
      E (pair z (List.replicate i true)) = DataEncode.bitstringEncode (l[i]'hi)) :
    emitListAt E (List.replicate l.length true) z = DataEncode.bitstringEncode l :=
  materialize_eq l z hval

/-- The same, with the count given by any list of the right length. -/
theorem emitListAt_eq' {α : Type} [DataEncode α] {E : List Bool → List Bool}
    (l : List α) (nU z : List Bool) (hn : nU.length = l.length)
    (hval : ∀ (i : ℕ) (hi : i < l.length),
      E (pair z (List.replicate i true)) = DataEncode.bitstringEncode (l[i]'hi)) :
    emitListAt E nU z = DataEncode.bitstringEncode l :=
  listEncFn_eq_bitstringEncode l (by rw [pairFst_pair, hn])
    (by rw [pairSnd_pair]; exact hval)

end Complexity
