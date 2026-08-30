/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.OperatorChain

/-!
# Shen's protocol for quantified Boolean formulas

⚠️ Unreviewed by Bolton

The operator chain of `Complexitylib.Classes.Interactive.OperatorChain` instantiated for a
prenex quantified Boolean formula `Q₁ x₁ … Qₙ xₙ ψ` with a quantifier-free matrix `ψ`:
the chain `shenChain` strips one quantifier at a time — a product for `∀`, the Boolean-preserving
"or" for `∃` — and after each quantifier linearizes every variable bound so far, so that no
intermediate function has degree above `2` in a bound variable except at the innermost level,
where the degree is that of the arithmetized matrix (`shenDegs`).

- `applyChain_shenChain_ofBool`: at a Boolean assignment the chain computes the truth value of
  the formula, so the claim `1` at the all-zero point is exactly "the formula is true".
- `chainDeg_shenChain`: the degree bounds are valid, provided the bound variables are distinct.

Together with `OpChain.accept_honest` and `OpChain.card_accept_le_ratio` this is the abstract
interactive proof for TQBF: `tqbf_accept_honest` and `tqbf_card_accept_le_ratio`.

## Main definitions

- `Shen.toQBF` — a prenex prefix and matrix as a `QBF`
- `Shen.shenChain`, `Shen.shenDegs` — the operator chain and its degree bounds

## Main results

- `Shen.applyChain_shenChain_ofBool` — the chain computes the truth value
- `Shen.chainDeg_shenChain` — the degree bounds are valid
- `Shen.tqbf_accept_honest`, `Shen.tqbf_card_accept_le_ratio` — the protocol for TQBF
-/

@[expose] public section

namespace Complexity

namespace Shen

open OpChain

variable {F : Type} [Field F]

/-! ## Prenex formulas -/

/-- A prenex prefix is a list of quantifiers, `true` for `∀`, each on a variable. -/
abbrev Prefix := List (Bool × ℕ)

/-- The formula with the given prefix and matrix. -/
def toQBF : Prefix → QBF → QBF
  | [], ψ => ψ
  | (true, i) :: qs, ψ => .all i (toQBF qs ψ)
  | (false, i) :: qs, ψ => .ex i (toQBF qs ψ)

/-- Linearize every variable of a list, the head outermost. -/
def linOps (vs : List ℕ) : List Op := vs.map Op.lin

/-- The quantifier's operator. -/
def quantOp (q : Bool) (i : ℕ) : Op := if q then Op.prod i else Op.or i

/-- **Shen's chain** for the remaining prefix `qs`, with `vs` the variables bound so far: the
quantifier's operator, then the linearization of every variable bound so far including the
new one, then the rest. -/
def shenChain : Prefix → List ℕ → List Op
  | [], _ => []
  | (q, i) :: qs, vs => quantOp q i :: (linOps (vs ++ [i]) ++ shenChain qs (vs ++ [i]))

/-- The degree bound of a linearization round on `x_j`: two, or the matrix's degree in `x_j`
at the innermost level. -/
def linDeg (ψ : QBF) (j : ℕ) : ℕ := max 2 (QBF.varDeg j ψ)

/-- The degree bounds of `shenChain`, round by round. -/
def shenDegs (ψ : QBF) : Prefix → List ℕ → List ℕ
  | [], _ => []
  | (_, i) :: qs, vs => 2 :: ((vs ++ [i]).map (linDeg ψ) ++ shenDegs ψ qs (vs ++ [i]))

/-! ## Chains in general -/

theorem applyChain_append (l₁ l₂ : List Op) (f : (ℕ → F) → F) :
    applyChain (l₁ ++ l₂) f = applyChain l₁ (applyChain l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons o l ih => rw [List.cons_append, applyChain_cons, applyChain_cons, ih]

theorem chainDeg_append (l₁ l₂ : List Op) (d₁ d₂ : List ℕ) (f : (ℕ → F) → F)
    (hlen : d₁.length = l₁.length) (h₁ : ChainDeg l₁ d₁ (applyChain l₂ f))
    (h₂ : ChainDeg l₂ d₂ f) : ChainDeg (l₁ ++ l₂) (d₁ ++ d₂) f := by
  induction l₁ generalizing d₁ with
  | nil =>
      cases d₁ with
      | nil => exact h₂
      | cons d d₁ => simp at hlen
  | cons o l ih =>
      cases d₁ with
      | nil => simp at hlen
      | cons d d₁ =>
          refine ⟨?_, ?_⟩
          · show QBF.IsPolyIn d o.var (applyChain (l ++ l₂) f)
            rw [applyChain_append]
            exact h₁.1
          · show ChainDeg (l ++ l₂) (d₁ ++ d₂) f
            exact ih d₁ (by simpa using hlen) h₁.2

/-! ## Linearization chains -/

/-- Linearizations do nothing at Boolean points. -/
theorem applyChain_linOps_ofBool (vs : List ℕ) (h : (ℕ → F) → F) (α : ℕ → Bool) :
    applyChain (linOps vs) h (QBF.ofBool α) = h (QBF.ofBool α) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      rw [linOps, List.map_cons, applyChain_cons]
      show QBF.linearize v (applyChain (linOps vs) h) (QBF.ofBool α) = _
      rw [QBF.linearize_ofBool, ih]

/-- A linearization chain leaves the degree in a variable it does not linearize alone. -/
theorem isPolyIn_applyChain_linOps_of_notMem {d j : ℕ} (vs : List ℕ) (hj : j ∉ vs)
    {h : (ℕ → F) → F} (hh : QBF.IsPolyIn d j h) :
    QBF.IsPolyIn d j (applyChain (linOps vs) h) := by
  induction vs with
  | nil => exact hh
  | cons v vs ih =>
      rw [linOps, List.map_cons, applyChain_cons]
      show QBF.IsPolyIn d j (QBF.linearize v (applyChain (linOps vs) h))
      exact QBF.linearize_isPoly_other (fun hv => hj (by rw [hv]; exact List.mem_cons_self))
        (ih fun hm => hj (List.mem_cons_of_mem _ hm))

/-- A linearization chain makes the degree in each variable it linearizes at most one. -/
theorem isPolyIn_applyChain_linOps_of_mem {j : ℕ} (vs : List ℕ) (hj : j ∈ vs)
    (h : (ℕ → F) → F) : QBF.IsPolyIn 1 j (applyChain (linOps vs) h) := by
  induction vs with
  | nil => simp at hj
  | cons v vs ih =>
      rw [linOps, List.map_cons, applyChain_cons]
      show QBF.IsPolyIn 1 j (QBF.linearize v (applyChain (linOps vs) h))
      by_cases hv : j = v
      · subst hv
        exact QBF.linearize_isPoly_self j _
      · exact QBF.linearize_isPoly_other hv (ih (List.mem_of_ne_of_mem hv hj))

/-- The rounds of a linearization chain have the degrees of the function it starts from. -/
theorem chainDeg_linOps (vs : List ℕ) (hnd : vs.Nodup) (D : ℕ → ℕ) (h : (ℕ → F) → F)
    (hD : ∀ j ∈ vs, QBF.IsPolyIn (D j) j h) : ChainDeg (linOps vs) (vs.map D) h := by
  induction vs with
  | nil => trivial
  | cons v vs ih =>
      rw [List.nodup_cons] at hnd
      refine ⟨?_, ?_⟩
      · show QBF.IsPolyIn (D v) (Op.var (Op.lin v)) (applyChain (linOps vs) h)
        exact isPolyIn_applyChain_linOps_of_notMem vs hnd.1 (hD v List.mem_cons_self)
      · show ChainDeg (linOps vs) (vs.map D) h
        exact ih hnd.2 fun j hj => hD j (List.mem_cons_of_mem _ hj)

/-! ## Quantifier operators -/

/-- A quantifier operator on another variable at most doubles the degree. -/
theorem isPolyIn_quantOp_apply {d i j : ℕ} (hij : i ≠ j) (q : Bool) {h : (ℕ → F) → F}
    (hh : QBF.IsPolyIn d j h) : QBF.IsPolyIn (2 * d) j ((quantOp q i).apply h) := by
  have h0 := QBF.isPolyIn_update_other hij hh 0
  have h1 := QBF.isPolyIn_update_other hij hh 1
  cases q
  · show QBF.IsPolyIn (2 * d) j
      (fun a => 1 - (1 - h (Function.update a i 0)) * (1 - h (Function.update a i 1)))
    rw [two_mul]
    exact QBF.isPolyIn_one_sub (QBF.isPolyIn_mul (QBF.isPolyIn_one_sub h0)
      (QBF.isPolyIn_one_sub h1))
  · show QBF.IsPolyIn (2 * d) j (fun a => h (Function.update a i 0) * h (Function.update a i 1))
    rw [two_mul]
    exact QBF.isPolyIn_mul h0 h1

theorem quantOp_var (q : Bool) (i : ℕ) : (quantOp q i).var = i := by
  cases q <;> rfl

/-- At a Boolean point a quantifier operator computes the quantifier. -/
theorem quantOp_apply_ofBool (q : Bool) (i : ℕ) (h : (ℕ → F) → F) (α : ℕ → Bool)
    (v : (ℕ → Bool) → Bool)
    (hv : ∀ b, h (QBF.ofBool (Function.update α i b))
      = if v (Function.update α i b) then 1 else 0) :
    (quantOp q i).apply h (QBF.ofBool α)
      = if (if q then v (Function.update α i false) && v (Function.update α i true)
          else v (Function.update α i false) || v (Function.update α i true)) then 1 else 0 := by
  have h0 : Function.update (QBF.ofBool α : ℕ → F) i 0
      = QBF.ofBool (Function.update α i false) := by
    rw [QBF.ofBool_update]; simp
  have h1 : Function.update (QBF.ofBool α : ℕ → F) i 1
      = QBF.ofBool (Function.update α i true) := by
    rw [QBF.ofBool_update]; simp
  cases q
  · show 1 - (1 - h (Function.update (QBF.ofBool α) i 0))
      * (1 - h (Function.update (QBF.ofBool α) i 1)) = _
    rw [h0, h1, hv, hv]
    cases v (Function.update α i false) <;> cases v (Function.update α i true) <;> simp
  · show h (Function.update (QBF.ofBool α) i 0) * h (Function.update (QBF.ofBool α) i 1) = _
    rw [h0, h1, hv, hv]
    cases v (Function.update α i false) <;> cases v (Function.update α i true) <;> simp

/-! ## The chain computes the formula -/

/-- **At a Boolean point Shen's chain computes the truth value of the formula.** -/
theorem applyChain_shenChain_ofBool (ψ : QBF) :
    ∀ (qs : Prefix) (vs : List ℕ) (α : ℕ → Bool),
      applyChain (shenChain qs vs) (QBF.arith ψ) (QBF.ofBool α : ℕ → F)
        = if QBF.eval α (toQBF qs ψ) then 1 else 0
  | [], _, α => QBF.arith_ofBool ψ α
  | (q, i) :: qs, vs, α => by
      rw [shenChain, applyChain_cons, applyChain_append]
      rw [quantOp_apply_ofBool q i _ α (fun β => QBF.eval β (toQBF qs ψ)) fun b => by
        rw [applyChain_linOps_ofBool, applyChain_shenChain_ofBool ψ qs (vs ++ [i])]]
      cases q
      · show _ = if QBF.eval α (.ex i (toQBF qs ψ)) then 1 else 0
        rfl
      · show _ = if QBF.eval α (.all i (toQBF qs ψ)) then 1 else 0
        rfl

/-! ## The degree bounds are valid -/

/-- A variable bound so far has degree at most `linDeg` in the rest of the chain. -/
theorem isPolyIn_shenChain (ψ : QBF) :
    ∀ (qs : Prefix) (vs : List ℕ), (vs ++ qs.map Prod.snd).Nodup →
      ∀ j ∈ vs, QBF.IsPolyIn (linDeg ψ j) j
        (applyChain (shenChain qs vs) (QBF.arith ψ) : (ℕ → F) → F)
  | [], vs, _, j, _ => (QBF.arith_isPoly j ψ).mono (le_max_right _ _)
  | (q, i) :: qs, vs, hnd, j, hj => by
      rw [shenChain, applyChain_cons, applyChain_append]
      have hij : i ≠ j := by
        intro h
        subst h
        rw [List.map_cons, List.nodup_append] at hnd
        exact hnd.2.2 i hj i List.mem_cons_self rfl
      have hlin := isPolyIn_applyChain_linOps_of_mem (vs ++ [i]) (List.mem_append_left _ hj)
        (applyChain (shenChain qs (vs ++ [i])) (QBF.arith ψ) : (ℕ → F) → F)
      exact (isPolyIn_quantOp_apply hij q hlin).mono (le_max_left _ _)

/-- **The degree bounds of Shen's chain are valid.** -/
theorem chainDeg_shenChain (ψ : QBF) :
    ∀ (qs : Prefix) (vs : List ℕ), (vs ++ qs.map Prod.snd).Nodup →
      ChainDeg (shenChain qs vs) (shenDegs ψ qs vs) (QBF.arith ψ : (ℕ → F) → F)
  | [], _, _ => trivial
  | (q, i) :: qs, vs, hnd => by
      have hnd' : (vs ++ [i] ++ qs.map Prod.snd).Nodup := by
        rw [List.append_assoc, List.singleton_append]
        rw [List.map_cons] at hnd
        exact hnd
      have hvs' : (vs ++ [i]).Nodup := List.Nodup.of_append_left hnd'
      have hi : i ∈ vs ++ [i] := List.mem_append_right _ (List.mem_singleton_self i)
      refine ⟨?_, ?_⟩
      · rw [shenDegs, List.headD_cons, applyChain_append, quantOp_var]
        exact (isPolyIn_applyChain_linOps_of_mem (vs ++ [i]) hi _).mono (by norm_num)
      · rw [shenDegs, List.tail_cons]
        exact chainDeg_append _ _ _ _ _ (by rw [linOps, List.length_map, List.length_map])
          (chainDeg_linOps (vs ++ [i]) hvs' (linDeg ψ) _
            fun j hj => isPolyIn_shenChain ψ qs (vs ++ [i]) hnd' j hj)
          (chainDeg_shenChain ψ qs (vs ++ [i]) hnd')

/-! ## The protocol for TQBF -/

/-- **Completeness for TQBF.** A true closed prenex formula is proved to the verifier by the
honest prover on every challenge vector, starting from the all-`false` point. -/
theorem tqbf_accept_honest (qs : Prefix) (ψ : QBF) (hnd : (qs.map Prod.snd).Nodup)
    (htrue : QBF.IsTrue (toQBF qs ψ)) (r : Fin (shenChain qs []).length → F) :
    accept (shenChain qs []) (shenDegs ψ qs []) (QBF.arith ψ) (QBF.ofBool fun _ => false) 1
      (honest (shenChain qs []) (shenDegs ψ qs []) (QBF.arith ψ)
        (chainDeg_shenChain ψ qs [] (by simpa using hnd)) (QBF.ofBool fun _ => false)) r := by
  have := accept_honest (shenChain qs []) (shenDegs ψ qs []) (QBF.arith ψ)
    (chainDeg_shenChain ψ qs [] (by simpa using hnd)) (QBF.ofBool fun _ => false) r
  rwa [applyChain_shenChain_ofBool,
    if_pos (show QBF.eval (fun _ => false) (toQBF qs ψ) = true from htrue)] at this

variable [Fintype F] [DecidableEq F]

open Classical in
/-- **Soundness for TQBF.** A false closed prenex formula is accepted from any prover on at
most a `(Σ shenDegs) / |F|` fraction of the challenge vectors. -/
theorem tqbf_card_accept_le_ratio (qs : Prefix) (ψ : QBF) (hnd : (qs.map Prod.snd).Nodup)
    (hfalse : ¬ QBF.IsTrue (toQBF qs ψ)) (P : SumCheck.Strategy F) :
    ((Finset.univ.filter fun r : Fin (shenChain qs []).length → F =>
        accept (shenChain qs []) (shenDegs ψ qs []) (QBF.arith ψ) (QBF.ofBool fun _ => false)
          1 P r).card : ℚ)
      / (Fintype.card F : ℚ) ^ (shenChain qs []).length
      ≤ ((shenDegs ψ qs []).take (shenChain qs []).length).sum / Fintype.card F := by
  refine card_accept_le_ratio _ _ _ (chainDeg_shenChain ψ qs [] (by simpa using hnd)) _ 1 ?_ P
  rw [applyChain_shenChain_ofBool]
  split_ifs with h
  · exact absurd h hfalse
  · exact zero_ne_one

end Shen

end Complexity
