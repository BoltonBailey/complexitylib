/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFEmitPrefix

/-!
# Emitting literals and clauses

⚠️ Unreviewed by Bolton

A literal is a sign and a variable index, so emitting one is `natEncodeFn` under the pair
bracket, with the sign read off whether a marker string is empty. Emitting a clause, or a list of
clauses, is then `emit_list_mem_FP` at `CLit` and at `List CLit` — no new machinery.

## Main results

- `litEnc_pos` / `litEnc_neg` / `litEnc_mem_FP` — one literal
- `clausesEnc_mem_FP` — a clause list presented as an indexed family
-/

@[expose] public section

namespace Complexity

open Polynomial

/-! ## One literal -/

/-- A literal: the sign is `true` exactly when the marker is non-empty, and the variable is the
length of `v`, written at width `w`. -/
noncomputable def litEnc (w sgn v : List Bool) : List Bool :=
  false :: (ifLtLen [] sgn encTrue encFalse ++ natEncodeFn (pair w (v.take w.length)))
    ++ [true]

/-- The literal an emitter writes, with no bound needed: the value is clamped to the width. -/
theorem litEnc_pos' {sgn : List Bool} (hs : sgn ≠ []) (w v : List Bool) :
    litEnc w sgn v
      = DataEncode.bitstringEncode ((true, min v.length w.length) : Bool × ℕ) := by
  have hlt : ([] : List Bool).length < sgn.length := by
    cases sgn with
    | nil => exact absurd rfl hs
    | cons a t => simp
  have hlen : (v.take w.length).length = min v.length w.length := by
    rw [List.length_take, Nat.min_comm]
  rw [litEnc, ifLtLen_pos hlt, bitstringEncode_pair,
    natEncodeFn_eq (by
      rw [pairFst_pair, pairSnd_pair, hlen]
      exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.lt_two_pow_self)),
    pairSnd_pair, hlen]
  rfl

theorem litEnc_neg' (w v : List Bool) :
    litEnc w [] v
      = DataEncode.bitstringEncode ((false, min v.length w.length) : Bool × ℕ) := by
  have hlen : (v.take w.length).length = min v.length w.length := by
    rw [List.length_take, Nat.min_comm]
  rw [litEnc, ifLtLen_neg (by simp), bitstringEncode_pair,
    natEncodeFn_eq (by
      rw [pairFst_pair, pairSnd_pair, hlen]
      exact lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.lt_two_pow_self)),
    pairSnd_pair, hlen]
  rfl

theorem litEnc_pos {sgn : List Bool} (hs : sgn ≠ []) {w v : List Bool}
    (h : v.length ≤ w.length) :
    litEnc w sgn v = DataEncode.bitstringEncode ((true, v.length) : Bool × ℕ) := by
  have hlt : ([] : List Bool).length < sgn.length := by
    cases sgn with
    | nil => exact absurd rfl hs
    | cons a t => simp
  have htake : v.take w.length = v := List.take_of_length_le h
  rw [litEnc, ifLtLen_pos hlt, bitstringEncode_pair,
    natEncodeFn_eq (by
      rw [pairFst_pair, pairSnd_pair, htake]
      exact lt_of_le_of_lt h (Nat.lt_two_pow_self)), pairSnd_pair, htake]
  rfl

theorem litEnc_neg {w v : List Bool} (h : v.length ≤ w.length) :
    litEnc w [] v = DataEncode.bitstringEncode ((false, v.length) : Bool × ℕ) := by
  have htake : v.take w.length = v := List.take_of_length_le h
  rw [litEnc, ifLtLen_neg (by simp), bitstringEncode_pair,
    natEncodeFn_eq (by
      rw [pairFst_pair, pairSnd_pair, htake]
      exact lt_of_le_of_lt h (Nat.lt_two_pow_self)), pairSnd_pair, htake]
  rfl

theorem litEnc_mem_FP {w sgn v : List Bool → List Bool} (hw : w ∈ FP) (hs : sgn ∈ FP)
    (hv : v ∈ FP) : (fun z => litEnc (w z) (sgn z) (v z)) ∈ FP := by
  have hclamp : (fun z => (v z).take (w z).length) ∈ FP := Cobham.takeLenFn_mem_FP hw hv
  have hpair : (fun z => pair (w z) ((v z).take (w z).length)) ∈ FP :=
    Cobham.pairFn_mem_FP hw hclamp
  have hnat : (fun z => natEncodeFn (pair (w z) ((v z).take (w z).length))) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hpair natEncodeFn_mem_FP) fun _ => rfl
  have hsign : (fun z => ifLtLen [] (sgn z) encTrue encFalse) ∈ FP :=
    ifLtLen_mem_FP (constFn_mem_FP []) hs (constFn_mem_FP _) (constFn_mem_FP _)
  have hbody := Cobham.appendFn_mem_FP hsign hnat
  have hcons := Cobham.appendFn_mem_FP (constFn_mem_FP [false]) hbody
  exact mem_FP_of_eq (Cobham.appendFn_mem_FP hcons (constFn_mem_FP [true])) fun z => by
    rw [litEnc]
    simp

/-! ## Short clauses, written out -/

/-- A list's encoding is its entries' encodings, bracketed. -/
theorem bitstringEncode_listAny {α : Type} [DataEncode α] (l : List α) :
    DataEncode.bitstringEncode l
      = false :: (l.map DataEncode.bitstringEncode).flatten ++ [true] := by
  rw [DataEncode.bitstringEncode_def]
  show (Data.l (l.map DataEncode.encode)).toBits = _
  rw [Data.toBits_l, List.map_map]
  rfl

/-- A one-literal clause. -/
noncomputable def clause1 (w s₀ a₀ : List Bool) : List Bool :=
  false :: litEnc w s₀ a₀ ++ [true]

/-- A two-literal clause. -/
noncomputable def clause2 (w s₀ a₀ s₁ a₁ : List Bool) : List Bool :=
  false :: (litEnc w s₀ a₀ ++ litEnc w s₁ a₁) ++ [true]

/-- A three-literal clause. -/
noncomputable def clause3 (w s₀ a₀ s₁ a₁ s₂ a₂ : List Bool) : List Bool :=
  false :: (litEnc w s₀ a₀ ++ (litEnc w s₁ a₁ ++ litEnc w s₂ a₂)) ++ [true]

theorem clause1_eq {w s₀ a₀ : List Bool} (b₀ : Bool)
    (hb₀ : litEnc w s₀ a₀ = DataEncode.bitstringEncode ((b₀, a₀.length) : Bool × ℕ)) :
    clause1 w s₀ a₀ = DataEncode.bitstringEncode [(b₀, a₀.length)] := by
  rw [clause1, hb₀, bitstringEncode_listAny]
  simp

theorem clause2_eq {w s₀ a₀ s₁ a₁ : List Bool} (b₀ b₁ : Bool)
    (hb₀ : litEnc w s₀ a₀ = DataEncode.bitstringEncode ((b₀, a₀.length) : Bool × ℕ))
    (hb₁ : litEnc w s₁ a₁ = DataEncode.bitstringEncode ((b₁, a₁.length) : Bool × ℕ)) :
    clause2 w s₀ a₀ s₁ a₁
      = DataEncode.bitstringEncode [(b₀, a₀.length), (b₁, a₁.length)] := by
  rw [clause2, hb₀, hb₁, bitstringEncode_listAny]
  simp

theorem clause3_eq {w s₀ a₀ s₁ a₁ s₂ a₂ : List Bool} (b₀ b₁ b₂ : Bool)
    (hb₀ : litEnc w s₀ a₀ = DataEncode.bitstringEncode ((b₀, a₀.length) : Bool × ℕ))
    (hb₁ : litEnc w s₁ a₁ = DataEncode.bitstringEncode ((b₁, a₁.length) : Bool × ℕ))
    (hb₂ : litEnc w s₂ a₂ = DataEncode.bitstringEncode ((b₂, a₂.length) : Bool × ℕ)) :
    clause3 w s₀ a₀ s₁ a₁ s₂ a₂
      = DataEncode.bitstringEncode [(b₀, a₀.length), (b₁, a₁.length), (b₂, a₂.length)] := by
  rw [clause3, hb₀, hb₁, hb₂, bitstringEncode_listAny]
  simp

theorem clause1_mem_FP {w s₀ a₀ : List Bool → List Bool} (hw : w ∈ FP) (hs₀ : s₀ ∈ FP)
    (ha₀ : a₀ ∈ FP) : (fun z => clause1 (w z) (s₀ z) (a₀ z)) ∈ FP := by
  have h := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false]) (litEnc_mem_FP hw hs₀ ha₀))
    (constFn_mem_FP [true])
  exact mem_FP_of_eq h fun z => by rw [clause1]; simp

theorem clause2_mem_FP {w s₀ a₀ s₁ a₁ : List Bool → List Bool} (hw : w ∈ FP) (hs₀ : s₀ ∈ FP)
    (ha₀ : a₀ ∈ FP) (hs₁ : s₁ ∈ FP) (ha₁ : a₁ ∈ FP) :
    (fun z => clause2 (w z) (s₀ z) (a₀ z) (s₁ z) (a₁ z)) ∈ FP := by
  have hbody := Cobham.appendFn_mem_FP (litEnc_mem_FP hw hs₀ ha₀) (litEnc_mem_FP hw hs₁ ha₁)
  have h := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false]) hbody) (constFn_mem_FP [true])
  exact mem_FP_of_eq h fun z => by rw [clause2]; simp

theorem clause3_mem_FP {w s₀ a₀ s₁ a₁ s₂ a₂ : List Bool → List Bool} (hw : w ∈ FP)
    (hs₀ : s₀ ∈ FP) (ha₀ : a₀ ∈ FP) (hs₁ : s₁ ∈ FP) (ha₁ : a₁ ∈ FP) (hs₂ : s₂ ∈ FP)
    (ha₂ : a₂ ∈ FP) :
    (fun z => clause3 (w z) (s₀ z) (a₀ z) (s₁ z) (a₁ z) (s₂ z) (a₂ z)) ∈ FP := by
  have hbody := Cobham.appendFn_mem_FP (litEnc_mem_FP hw hs₀ ha₀)
    (Cobham.appendFn_mem_FP (litEnc_mem_FP hw hs₁ ha₁) (litEnc_mem_FP hw hs₂ ha₂))
  have h := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false]) hbody) (constFn_mem_FP [true])
  exact mem_FP_of_eq h fun z => by rw [clause3]; simp

/-- Guard an already-encoded clause with one more literal. -/
noncomputable def consLitEnc (w s₀ a₀ cEnc : List Bool) : List Bool :=
  false :: (litEnc w s₀ a₀ ++ (cEnc.drop 1).dropLast) ++ [true]

theorem consLitEnc_eq {w s₀ a₀ : List Bool} (b₀ : Bool) (c : List CLit)
    (hb₀ : litEnc w s₀ a₀ = DataEncode.bitstringEncode ((b₀, a₀.length) : Bool × ℕ)) :
    consLitEnc w s₀ a₀ (DataEncode.bitstringEncode c)
      = DataEncode.bitstringEncode ((b₀, a₀.length) :: c) := by
  have hc : DataEncode.bitstringEncode c
      = false :: (c.map DataEncode.bitstringEncode).flatten ++ [true] :=
    bitstringEncode_listAny c
  rw [consLitEnc, hb₀, hc,
    bitstringEncode_listAny ((b₀, a₀.length) :: c), List.map_cons, List.flatten_cons]
  simp

theorem consLitEnc_mem_FP {w s₀ a₀ cEnc : List Bool → List Bool} (hw : w ∈ FP)
    (hs₀ : s₀ ∈ FP) (ha₀ : a₀ ∈ FP) (hc : cEnc ∈ FP) :
    (fun z => consLitEnc (w z) (s₀ z) (a₀ z) (cEnc z)) ∈ FP := by
  have hdrop : (fun z => (cEnc z).drop 1) ∈ FP :=
    mem_FP_of_eq (dropOneFn_mem_FP hc) fun _ => rfl
  have hlast : (fun z => ((cEnc z).drop 1).dropLast) ∈ FP := by
    refine mem_FP_of_eq (Cobham.takeLenFn_mem_FP
      (mem_FP_of_eq (dropOneFn_mem_FP hdrop) fun _ => rfl) hdrop) fun z => ?_
    rw [List.dropLast_eq_take, dropOne, List.length_drop]
  have hbody := Cobham.appendFn_mem_FP (litEnc_mem_FP hw hs₀ ha₀) hlast
  have h := Cobham.appendFn_mem_FP
    (Cobham.appendFn_mem_FP (constFn_mem_FP [false]) hbody) (constFn_mem_FP [true])
  exact mem_FP_of_eq h fun z => by rw [consLitEnc]; simp

/-! ## A clause, and a list of clauses -/

/-- **A clause is emittable from its literals.** -/
theorem clauseEnc_mem_FP {E : List Bool → List Bool} {c : List Bool → List CLit}
    (hE : E ∈ FP) (hN : (fun x => List.replicate (c x).length true) ∈ FP)
    (hval : ∀ (x : List Bool) (i : ℕ) (hi : i < (c x).length),
      E (pair x (List.replicate i true)) = DataEncode.bitstringEncode ((c x)[i]'hi)) :
    (fun x => DataEncode.bitstringEncode (c x)) ∈ FP :=
  emit_list_mem_FP hE hN hval

/-- **A clause list is emittable from its clauses.** -/
theorem clausesEnc_mem_FP {E : List Bool → List Bool} {φ : List Bool → List (List CLit)}
    (hE : E ∈ FP) (hN : (fun x => List.replicate (φ x).length true) ∈ FP)
    (hval : ∀ (x : List Bool) (i : ℕ) (hi : i < (φ x).length),
      E (pair x (List.replicate i true)) = DataEncode.bitstringEncode ((φ x)[i]'hi)) :
    (fun x => DataEncode.bitstringEncode (φ x)) ∈ FP :=
  emit_list_mem_FP hE hN hval

/-! ## Uniform families -/

theorem length_flatMap_range_const {α : Type} (c : ℕ) (f : ℕ → List α)
    (hf : ∀ i, (f i).length = c) : ∀ n : ℕ, ((List.range n).flatMap f).length = n * c
  | 0 => by simp
  | n + 1 => by
      rw [List.range_succ, List.flatMap_append, List.length_append,
        length_flatMap_range_const c f hf n]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hf]
      ring

/-- **Indexing a uniform concatenation**: block `t / c`, offset `t % c`. -/
theorem getElem?_flatMap_range_const {α : Type} (c : ℕ) (hc : 0 < c) (f : ℕ → List α)
    (hf : ∀ i, (f i).length = c) : ∀ (n t : ℕ), t < n * c →
      ((List.range n).flatMap f)[t]? = (f (t / c))[t % c]?
  | 0, t, ht => by simp at ht
  | n + 1, t, ht => by
      rw [List.range_succ, List.flatMap_append]
      have hlen : ((List.range n).flatMap f).length = n * c :=
        length_flatMap_range_const c f hf n
      by_cases hlt : t < n * c
      · rw [List.getElem?_append_left (by omega)]
        exact getElem?_flatMap_range_const c hc f hf n t hlt
      · have hexp : (n + 1) * c = n * c + c := by ring
        have h1 : n * c ≤ t := by omega
        have hr : t - n * c < c := by omega
        have ht' : t = (t - n * c) + c * n := by
          have : n * c = c * n := Nat.mul_comm n c
          omega
        have hdiv : t / c = n := by
          rw [ht', Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt hr, Nat.zero_add]
        have hmod : t % c = t - n * c := by
          conv_lhs => rw [ht']
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
        rw [List.getElem?_append_right (by omega), hlen, hdiv, hmod]
        simp

/-- **Indexing a uniform concatenation over an arbitrary list.** -/
theorem getElem?_flatMap_const {α β : Type} (c : ℕ) (hc : 0 < c) (f : α → List β)
    (hf : ∀ a, (f a).length = c) : ∀ (l : List α) (t : ℕ), t < l.length * c →
      (l.flatMap f)[t]? = (l[t / c]?).bind fun a => (f a)[t % c]?
  | [], t, ht => by simp at ht
  | a :: l, t, ht => by
      rw [List.flatMap_cons]
      by_cases hlt : t < c
      · rw [List.getElem?_append_left (by rw [hf]; exact hlt), Nat.div_eq_of_lt hlt,
          Nat.mod_eq_of_lt hlt]
        simp
      · have hge : c ≤ t := by omega
        have hsub : t - c + c = t := by omega
        have hdiv : t / c = (t - c) / c + 1 := by
          conv_lhs => rw [← hsub]
          rw [Nat.add_div_right _ hc]
        have hmod : t % c = (t - c) % c := by
          conv_lhs => rw [← hsub]
          rw [Nat.add_mod_right]
        have hlt' : t - c < l.length * c := by
          have : (a :: l).length * c = c + l.length * c := by
            rw [List.length_cons]
            ring
          omega
        rw [List.getElem?_append_right (by rw [hf]; omega), hf,
          getElem?_flatMap_const c hc f hf l (t - c) hlt', hdiv, hmod]
        simp

theorem atMostOneClauses_getElem? {A : Type} (w : A → ℕ) (l : List A) (hl : 0 < l.length)
    (p : ℕ) (hp : p < l.length * l.length) :
    (QBF.atMostOneClauses w l)[p]?
      = (l[p / l.length]?).bind fun a => (l[p % l.length]?).map fun b =>
          if w a = w b then [(false, w a), (true, w a)] else [(false, w a), (false, w b)] := by
  rw [QBF.atMostOneClauses, getElem?_flatMap_const l.length hl _ (fun a => by simp) l p hp]
  congr 1
  funext a
  rw [List.getElem?_map]

theorem oneHotClauses_getElem?_head {A : Type} (w : A → ℕ) (l allowed : List A) :
    (QBF.oneHotClauses w l allowed)[0]? = some (QBF.atLeastOneClause w allowed) := by
  rw [QBF.oneHotClauses]
  rfl

theorem oneHotClauses_getElem?_tail {A : Type} (w : A → ℕ) (l allowed : List A) (p : ℕ) :
    (QBF.oneHotClauses w l allowed)[p + 1]? = (QBF.atMostOneClauses w l)[p]? := by
  rw [QBF.oneHotClauses]
  rfl

/-! ## The equality-bit clauses, by index -/

theorem iffAuxCNF_getElem?_zero (e u v : ℕ) :
    (QBF.iffAuxCNF e u v)[0]? = some [(false, e), (false, u), (true, v)] := rfl

theorem iffAuxCNF_getElem?_one (e u v : ℕ) :
    (QBF.iffAuxCNF e u v)[1]? = some [(false, e), (true, u), (false, v)] := rfl

theorem iffAuxCNF_getElem?_two (e u v : ℕ) :
    (QBF.iffAuxCNF e u v)[2]? = some [(true, e), (false, u), (false, v)] := rfl

theorem iffAuxCNF_getElem?_three (e u v : ℕ) :
    (QBF.iffAuxCNF e u v)[3]? = some [(true, e), (true, u), (true, v)] := rfl

/-- **Indexing the equality bits**: bit `t / 4`, corner `t % 4`. -/
theorem eqAuxCNF_getElem? (W eOff u v t : ℕ) (ht : t < W * 4) :
    (QBF.eqAuxCNF W eOff u v)[t]?
      = (QBF.iffAuxCNF (eOff + t / 4) (u + t / 4) (v + t / 4))[t % 4]? := by
  rw [QBF.eqAuxCNF,
    getElem?_flatMap_range_const 4 (by omega)
      (fun i => QBF.iffAuxCNF (eOff + i) (u + i) (v + i)) (fun _ => rfl) W t ht]

/-- The clause of `eqAuxCNF` at an index, spelled out. -/
theorem eqAuxCNF_getElem?_eq (W eOff u v t : ℕ) (ht : t < W * 4) :
    (QBF.eqAuxCNF W eOff u v)[t]?
      = some (if t % 4 = 0 then
            [(false, eOff + t / 4), (false, u + t / 4), (true, v + t / 4)]
          else if t % 4 = 1 then
            [(false, eOff + t / 4), (true, u + t / 4), (false, v + t / 4)]
          else if t % 4 = 2 then
            [(true, eOff + t / 4), (false, u + t / 4), (false, v + t / 4)]
          else [(true, eOff + t / 4), (true, u + t / 4), (true, v + t / 4)]) := by
  rw [eqAuxCNF_getElem? W eOff u v t ht]
  have h4 : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3 := by omega
  rcases h4 with h | h | h | h <;> rw [h] <;> simp [iffAuxCNF_getElem?_zero,
    iffAuxCNF_getElem?_one, iffAuxCNF_getElem?_two, iffAuxCNF_getElem?_three]

/-! ## Block equality, by index -/

theorem eqClauses_length (W u v : ℕ) : (QBF.eqClauses W u v).length = W * 2 := by
  rw [QBF.eqClauses, List.length_flatMap]
  simp

/-- **Indexing block equality**: bit `t / 2`, direction `t % 2`. -/
theorem eqClauses_getElem?_eq (W u v t : ℕ) (ht : t < W * 2) :
    (QBF.eqClauses W u v)[t]?
      = some (if t % 2 = 0 then [(false, u + t / 2), (true, v + t / 2)]
          else [(true, u + t / 2), (false, v + t / 2)]) := by
  rw [QBF.eqClauses,
    getElem?_flatMap_range_const 2 (by omega)
      (fun i => [[((false, u + i) : CLit), (true, v + i)], [(true, u + i), (false, v + i)]])
      (fun _ => rfl) W t ht]
  have h2 : t % 2 = 0 ∨ t % 2 = 1 := by omega
  rcases h2 with h | h <;> rw [h] <;> rfl

end Complexity
