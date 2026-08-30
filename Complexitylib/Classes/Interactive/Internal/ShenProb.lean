/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenHonest

/-!
# Completeness and soundness of the protocol on an instance

⚠️ Unreviewed by Bolton

The verifier's challenges are the first `w` bits of each `W`-bit coin block, reduced mod `p`.
Restricting a coin string to those bits is a restriction along an injection, whose fibres have
size `2 ^ (T - n w)` (`card_filter_restrict_le`), so the accepting coin strings are at most
that many times the accepting challenge vectors of the abstract protocol, which
`card_accept_reduce_le` bounds. Completeness is the honest prover of `ShenHonest`.

## Main results

- `card_filter_restrict_le` — fibres of a restriction
- `ShenCtx.eventProb_honestS` — the honest prover is accepted with probability `1` on a true
  instance
- `ShenCtx.eventProb_le` — every prover is accepted with probability at most `2 n D / p` on a
  false instance
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

/-! ## Counting through a restriction -/

/-- **Fibres of a restriction.** The strings on `β` whose restriction along an injection
`ι : α → β` satisfies `Q` are at most `2 ^ (|β| - |α|)` times the strings on `α` satisfying
`Q`. -/
theorem card_filter_restrict_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (ι : α → β) (hι : Function.Injective ι) (Q : (α → Bool) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun ρ : β → Bool => Q (fun a => ρ (ι a))).card
      ≤ (Finset.univ.filter Q).card * 2 ^ (Fintype.card β - Fintype.card α) := by
  classical
  set s := Finset.univ.filter fun ρ : β → Bool => Q (fun a => ρ (ι a)) with hs
  set res : (β → Bool) → (α → Bool) := fun ρ a => ρ (ι a) with hres
  have himg : s.image res ⊆ Finset.univ.filter Q := by
    intro g hg
    rw [Finset.mem_image] at hg
    obtain ⟨ρ, hρ, rfl⟩ := hg
    rw [hs, Finset.mem_filter] at hρ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρ.2⟩
  have hfib : ∀ g ∈ s.image res,
      (s.filter fun ρ => res ρ = g).card ≤ 2 ^ (Fintype.card β - Fintype.card α) := by
    intro g _
    have h1 : (s.filter fun ρ => res ρ = g).card
        ≤ (Finset.univ : Finset ({b // b ∉ Set.range ι} → Bool)).card := by
      refine Finset.card_le_card_of_injOn (fun ρ b => ρ b.1) (fun _ _ => Finset.mem_univ _) ?_
      intro ρ hρ ρ' hρ' h
      rw [Finset.mem_coe, Finset.mem_filter] at hρ hρ'
      funext b
      by_cases hb : b ∈ Set.range ι
      · obtain ⟨a, rfl⟩ := hb
        exact congrFun (hρ.2.trans hρ'.2.symm) a
      · exact congrFun h ⟨b, hb⟩
    refine le_trans h1 ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
      Set.card_range_of_injective hι]
  calc s.card ≤ 2 ^ (Fintype.card β - Fintype.card α) * (s.image res).card :=
        Finset.card_le_mul_card_image s _ hfib
    _ ≤ 2 ^ (Fintype.card β - Fintype.card α) * (Finset.univ.filter Q).card :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)
    _ = _ := mul_comm _ _

namespace ShenCtx

variable (Γ : ShenCtx)

/-! ## The coin blocks -/

/-- The index of bit `j` of coin block `k`, in a coin string of `T ≥ n W` bits. -/
def blockIdx (W T : ℕ) (hT : Γ.n * W ≤ T) (hW : Γ.w ≤ W) (kj : Fin Γ.n × Fin Γ.w) : Fin T :=
  ⟨kj.1 * W + kj.2, by
    obtain ⟨⟨k, hk⟩, ⟨j, hj⟩⟩ := kj
    have := Nat.mul_le_mul_right W hk
    rw [Nat.succ_mul] at this
    simp only
    omega⟩

theorem blockIdx_injective (W T : ℕ) (hT : Γ.n * W ≤ T) (hW : Γ.w ≤ W) (hW0 : 0 < W) :
    Function.Injective (Γ.blockIdx W T hT hW) := by
  rintro ⟨⟨k, hk⟩, ⟨j, hj⟩⟩ ⟨⟨k', hk'⟩, ⟨j', hj'⟩⟩ h
  simp only [blockIdx, Fin.mk.injEq] at h
  have hdiv : ∀ a b : ℕ, b < Γ.w → (a * W + b) / W = a := fun a b hb => by
    rw [mul_comm, Nat.mul_add_div hW0, Nat.div_eq_of_lt (by omega), add_zero]
  have hkk : k = k' := by rw [← hdiv k j hj, ← hdiv k' j' hj', h]
  subst hkk
  have hjj : j = j' := by omega
  subst hjj
  rfl

/-- The coin block is the string of the block's bits. -/
theorem wBlock_toList (T W : ℕ) (ρ : Fin T → Bool) (k : ℕ) (hk : k * W + Γ.w ≤ T) :
    wBlock (BitString.toList ρ) (k * W) Γ.w
      = BitString.toList fun j : Fin Γ.w => ρ ⟨k * W + j, by omega⟩ := by
  refine List.ext_getElem (by rw [length_wBlock (by simpa using hk), BitString.length_toList])
    fun i h1 h2 => ?_
  simp [wBlock, BitString.toList, List.getElem_take, List.getElem_drop]

/-- The challenge vector, as the reduction of the block bits. -/
theorem coinsOf_eq_ofFn (W T : ℕ) (ρ : Fin T → Bool) (hT : Γ.n * W ≤ T) (hW : Γ.w ≤ W) :
    Γ.coinsOf W (BitString.toList ρ) Γ.n
      = List.ofFn fun k : Fin Γ.ops.length =>
          reduceBits Γ.w Γ.p fun j => ρ (Γ.blockIdx W T hT hW (k, j)) := by
  rw [coinsOf]
  refine List.ext_getElem (by simp; rfl) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have hi : i < Γ.n := by simpa using h1
  rw [Γ.wBlock_toList T W ρ i (by
      have := Nat.mul_le_mul_right W hi
      rw [Nat.succ_mul] at this
      omega), coinVal_toList]
  rfl

theorem coins_block_le (W R T : ℕ) (hT : R * W ≤ T) (hW : Γ.w ≤ W) :
    ∀ i < R, i * W + Γ.w ≤ T := fun i hi => by
  have := Nat.mul_le_mul_right W hi
  rw [Nat.succ_mul] at this
  omega

/-- The abstract run on the challenge vector is the fold. -/
theorem runFold_eq_absRun (S : ProverStrategy) (W : ℕ) (r : List Bool) :
    runFold Γ.ops Γ.ds (Γ.PS S) (Γ.coinsOf W r Γ.n) (Γ.a0, (1 : ZMod Γ.p), true)
      = Γ.absRun S (Γ.coinsOf W r Γ.n) := by
  rw [absRun, coinsOf_length]
  show runFold Γ.ops Γ.ds _ _ _ = runFold (Γ.ops.take Γ.ops.length) _ _ _ _
  rw [List.take_length]
  rfl

/-! ## Completeness -/

/-- **Completeness.** On a true instance the honest prover is accepted on every coin string. -/
theorem eventProb_honestS (P : Protocol) (x₀ : List Bool) (Wp : Polynomial ℕ)
    (hv : ∀ r τ, P.vmsg (protocolView x₀ r τ) = shenVmsg Wp (protocolView Γ.x r τ))
    (hverdict : ∀ r τ, protocolView x₀ r τ ∈ P.verdict ↔ protocolView Γ.x r τ ∈ shenVerdict)
    (W R : ℕ) (hW : Wp.eval Γ.x.length = W) (hR : P.rounds x₀.length = R) (hRn : Γ.n + 1 ≤ R)
    (hwW : Γ.w ≤ W) (hT : R * W ≤ P.coins x₀.length)
    (htrue : QBF.eval (fun _ => false) (toQBF Γ.I.1 (cnfQBF Γ.I.2)) = true) :
    eventProb (P.acceptEvent Γ.honestS x₀) = 1 := by
  classical
  rw [Protocol.acceptEvent, Finset.filter_true_of_mem, eventProb_univ]
  intro ρ _
  obtain ⟨ok, cl, -, -, -, hB, hacc⟩ := Γ.accepts_spec P x₀ Wp hv hverdict Γ.honestS
    (BitString.toList ρ) W R hW hR hRn
    (by rw [BitString.length_toList]; exact Γ.coins_block_le W R _ hT hwW)
  obtain ⟨hok, hcl⟩ := hB Γ.honestS_WF
  rw [hacc]
  have h := Γ.accept_honestS fun k : Fin Γ.ops.length =>
    Γ.coinVal (wBlock (BitString.toList ρ) (k * W) Γ.w)
  rw [applyChain_a0, if_pos htrue, accept_iff_runFold] at h
  have hofFn : (List.ofFn fun k : Fin Γ.ops.length =>
      Γ.coinVal (wBlock (BitString.toList ρ) (k * W) Γ.w))
        = Γ.coinsOf W (BitString.toList ρ) Γ.n := by
    rw [coinsOf]
    refine List.ext_getElem (by simp; rfl) fun i h1 h2 => ?_
    simp
  rw [hofFn, runFold_eq_absRun] at h
  obtain ⟨hflag, hf⟩ := h
  exact ⟨hok.trans hflag, by rw [hcl, hf]⟩

/-! ## Soundness -/

/-- **Soundness.** On a false instance every prover is accepted with probability at most
`2 n D / p`. -/
theorem eventProb_le (P : Protocol) (x₀ : List Bool) (Wp : Polynomial ℕ)
    (hv : ∀ r τ, P.vmsg (protocolView x₀ r τ) = shenVmsg Wp (protocolView Γ.x r τ))
    (hverdict : ∀ r τ, protocolView x₀ r τ ∈ P.verdict ↔ protocolView Γ.x r τ ∈ shenVerdict)
    (S : ProverStrategy) (W R : ℕ) (hW : Wp.eval Γ.x.length = W) (hR : P.rounds x₀.length = R)
    (hRn : Γ.n + 1 ≤ R) (hwW : Γ.w ≤ W) (hT : R * W ≤ P.coins x₀.length)
    (hfalse : QBF.eval (fun _ => false) (toQBF Γ.I.1 (cnfQBF Γ.I.2)) = false) :
    eventProb (P.acceptEvent S x₀) ≤ 2 * (Γ.n * Γ.D) / Γ.p := by
  classical
  set T := P.coins x₀.length with hTdef
  have hW0 : 0 < W := lt_of_lt_of_le Γ.hw0 hwW
  have hnT : Γ.n * W ≤ T := le_trans (Nat.mul_le_mul_right _ (by omega)) hT
  have hnw : Γ.n * Γ.w ≤ T := le_trans (Nat.mul_le_mul_left _ hwW) hnT
  set Q : (Fin Γ.n × Fin Γ.w → Bool) → Prop := fun g =>
    accept Γ.ops Γ.ds Γ.f Γ.a0 1 (Γ.PS S) fun k => reduceBits Γ.w Γ.p fun j => g (k, j) with hQ
  set A := Finset.univ.filter fun r : Fin Γ.ops.length → (Fin Γ.w → Bool) =>
    accept Γ.ops Γ.ds Γ.f Γ.a0 1 (Γ.PS S) fun k => reduceBits Γ.w Γ.p (r k) with hA
  have hsub : P.acceptEvent S x₀
      ⊆ Finset.univ.filter fun ρ : Fin T → Bool => Q fun a => ρ (Γ.blockIdx W T hnT hwW a) := by
    intro ρ hρ
    rw [Protocol.acceptEvent, Finset.mem_filter] at hρ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨ok, cl, -, -, hAc, -, hacc⟩ := Γ.accepts_spec P x₀ Wp hv hverdict S
      (BitString.toList ρ) W R hW hR hRn
      (by rw [BitString.length_toList]; exact Γ.coins_block_le W R _ hT hwW)
    obtain ⟨hok, hcl⟩ := hacc.mp hρ.2
    obtain ⟨hflag, hcl'⟩ := hAc hok
    have hf := encZMod_injective Γ.w Γ.hpw' (hcl.symm.trans hcl')
    show accept Γ.ops Γ.ds Γ.f Γ.a0 1 (Γ.PS S)
      fun k => reduceBits Γ.w Γ.p fun j => ρ (Γ.blockIdx W T hnT hwW (k, j))
    rw [accept_iff_runFold, ← coinsOf_eq_ofFn Γ W T ρ hnT hwW, runFold_eq_absRun]
    exact ⟨hflag, hf⟩
  have hcard1 := card_filter_restrict_le (Γ.blockIdx W T hnT hwW)
    (Γ.blockIdx_injective W T hnT hwW hW0) Q
  have hcard2 : (Finset.univ.filter Q).card ≤ A.card :=
    Finset.card_le_card_of_injOn (fun g => Function.curry g) (fun g hg => by
        rw [Finset.mem_coe, Finset.mem_filter] at hg
        rw [hA, Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hg.2⟩)
      fun _ _ _ _ h => Function.curry_injective h
  have hne : applyChain Γ.ops Γ.f Γ.a0 ≠ 1 := by
    rw [applyChain_a0, if_neg (by simp [hfalse])]
    exact zero_ne_one
  have hred := card_accept_reduce_le Γ.w Γ.hpw'.le Γ.ops Γ.ds Γ.f Γ.chainDeg_ds Γ.a0 1 hne (Γ.PS S)
  have hsum : (Γ.ds.take Γ.ops.length).sum = Γ.n * Γ.D := by
    rw [ds, List.take_replicate, List.sum_replicate, smul_eq_mul]
    show min Γ.n Γ.n * Γ.D = _
    rw [min_self]
  rw [hsum] at hred
  have hE : (P.acceptEvent S x₀).card ≤ A.card * 2 ^ (T - Γ.n * Γ.w) := by
    refine le_trans (Finset.card_le_card hsub) (le_trans hcard1 ?_)
    rw [Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    refine Nat.mul_le_mul_right _ ?_
    convert hcard2
  rw [eventProb]
  have h2T : (2 : ℚ) ^ T = 2 ^ (Γ.n * Γ.w) * 2 ^ (T - Γ.n * Γ.w) := by
    rw [← pow_add, Nat.add_sub_cancel' hnw]
  calc ((P.acceptEvent S x₀).card : ℚ) / 2 ^ T
      ≤ (A.card * 2 ^ (T - Γ.n * Γ.w) : ℚ) / 2 ^ T := by
        gcongr
        exact_mod_cast hE
    _ = (A.card : ℚ) / ((2 : ℚ) ^ Γ.w) ^ Γ.ops.length := by
        rw [h2T, ← pow_mul]
        show _ = (A.card : ℚ) / 2 ^ (Γ.w * Γ.n)
        rw [mul_comm Γ.w]
        field_simp
    _ ≤ 2 * (Γ.n * Γ.D) / Γ.p := by exact_mod_cast hred

end ShenCtx

end Complexity
