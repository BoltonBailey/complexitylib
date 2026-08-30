/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenProb

/-!
# `IP` membership through a reduction to TQBF

⚠️ Unreviewed by Bolton

Any language that reduces in polynomial time to well-formed prenex CNF QBF instances is in `IP`:
the verifier applies the reduction to its input and runs Shen's protocol on the result. The
round, coin and message polynomials come from the output-length bounds of the polynomial-time
functions involved, so no arithmetic on the parameters is needed.

## Main definitions

- `redView`, `shenProtocolOn` — Shen's protocol behind a reduction

## Main results

- `mem_IP_of_shen_reduction`
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

/-- The view with the input replaced by its reduction. -/
noncomputable def redView (red : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (pair (red (RepArgs.vx z)) (RepArgs.vr z)) (RepArgs.ve z)

theorem redView_mem_FP {red : List Bool → List Bool} (hred : red ∈ FP) : redView red ∈ FP := by
  have h1 : (fun z => red (RepArgs.vx z)) ∈ FP := by
    have := mem_FP_comp RepArgs.vx_mem_FP hred
    simpa only [Function.comp_def] using this
  exact pairFn_mem_FP (pairFn_mem_FP h1 RepArgs.vr_mem_FP) RepArgs.ve_mem_FP

theorem redView_view (red : List Bool → List Bool) (x r : List Bool) (τ : Transcript) :
    redView red (protocolView x r τ) = protocolView (red x) r τ := by
  rw [redView, RepArgs.vx_view, RepArgs.vr_view, RepArgs.ve_view]
  rfl

/-- The verifier's message behind the reduction. -/
noncomputable def shenVmsgOn (red : List Bool → List Bool) (Wp : Polynomial ℕ) (z : List Bool) :
    List Bool :=
  shenVmsg Wp (redView red z)

theorem shenVmsgOn_mem_FP {red : List Bool → List Bool} (hred : red ∈ FP) (Wp : Polynomial ℕ) :
    shenVmsgOn red Wp ∈ FP := by
  have := mem_FP_comp (redView_mem_FP hred) (shenVmsg_mem_FP Wp)
  simpa only [Function.comp_def] using this

theorem shenVmsgOn_view (red : List Bool → List Bool) (Wp : Polynomial ℕ) (x r : List Bool)
    (τ : Transcript) :
    shenVmsgOn red Wp (protocolView x r τ) = shenVmsg Wp (protocolView (red x) r τ) := by
  rw [shenVmsgOn, redView_view]

/-- The verdict behind the reduction. -/
def shenVerdictOn (red : List Bool → List Bool) : Language :=
  {z | ∃ b ∈ shenVerdictFn (redView red z), b = true}

theorem shenVerdictOn_mem_P {red : List Bool → List Bool} (hred : red ∈ FP) :
    shenVerdictOn red ∈ P :=
  mem_P_of_decisionFn (f := fun z => shenVerdictFn (redView red z)) (by
      have := mem_FP_comp (redView_mem_FP hred) shenVerdictFn_mem_FP
      simpa only [Function.comp_def] using this) fun _ => Iff.rfl

theorem mem_shenVerdictOn_iff (red : List Bool → List Bool) (z : List Bool) :
    z ∈ shenVerdictOn red ↔ redView red z ∈ shenVerdict := Iff.rfl

/-- **Shen's protocol behind a reduction**: the verifier runs on `red x`. -/
noncomputable def shenProtocolOn (red : List Bool → List Bool) (hred : red ∈ FP)
    (Wp Rp Cp Mp : Polynomial ℕ)
    (hM : ∀ (x r : List Bool) (τ : Transcript),
      (shenVmsgOn red Wp (protocolView x r τ)).length ≤ Mp.eval x.length) :
    Protocol where
  rounds n := Rp.eval n
  coins n := Cp.eval n
  msgLen n := Mp.eval n
  vmsg := shenVmsgOn red Wp
  vmsg_mem := shenVmsgOn_mem_FP hred Wp
  vmsg_len := fun x r τ => hM x r τ
  verdict := shenVerdictOn red
  verdict_mem := shenVerdictOn_mem_P hred

theorem shenProtocolOn_vmsg (red : List Bool → List Bool) (hred : red ∈ FP)
    (Wp Rp Cp Mp : Polynomial ℕ) (hM) (z : List Bool) :
    (shenProtocolOn red hred Wp Rp Cp Mp hM).vmsg z = shenVmsgOn red Wp z := by
  unfold shenProtocolOn
  with_reducible rfl

theorem shenProtocolOn_verdict (red : List Bool → List Bool) (hred : red ∈ FP)
    (Wp Rp Cp Mp : Polynomial ℕ) (hM) :
    (shenProtocolOn red hred Wp Rp Cp Mp hM).verdict = shenVerdictOn red := by
  unfold shenProtocolOn
  with_reducible rfl

theorem shenProtocolOn_rounds (red : List Bool → List Bool) (hred : red ∈ FP)
    (Wp Rp Cp Mp : Polynomial ℕ) (hM) (n : ℕ) :
    (shenProtocolOn red hred Wp Rp Cp Mp hM).rounds n = Rp.eval n := by
  unfold shenProtocolOn
  with_reducible rfl

theorem shenProtocolOn_coins (red : List Bool → List Bool) (hred : red ∈ FP)
    (Wp Rp Cp Mp : Polynomial ℕ) (hM) (n : ℕ) :
    (shenProtocolOn red hred Wp Rp Cp Mp hM).coins n = Cp.eval n := by
  unfold shenProtocolOn
  with_reducible rfl

theorem shenProtocolOn_msgLen (red : List Bool → List Bool) (hred : red ∈ FP)
    (Wp Rp Cp Mp : Polynomial ℕ) (hM) (n : ℕ) :
    (shenProtocolOn red hred Wp Rp Cp Mp hM).msgLen n = Mp.eval n := by
  unfold shenProtocolOn
  with_reducible rfl

/-- **`IP` membership through a reduction to TQBF.** If a polynomial-time `red` maps every input
to the encoding of a well-formed instance whose formula is true exactly for inputs in `L`, then
`L ∈ IP`. -/
theorem mem_IP_of_shen_reduction (L : Language) (red : List Bool → List Bool) (hred : red ∈ FP)
    (inst : List Bool → Instance) (hinst : ∀ x, red x = DataEncode.bitstringEncode (inst x))
    (hwf : ∀ x, WellFormed (inst x))
    (hL : ∀ x, x ∈ L ↔ QBF.eval (fun _ => false) (toQBF (inst x).1 (cnfQBF (inst x).2)) = true) :
    L ∈ IP := by
  classical
  obtain ⟨Wp, hWp⟩ := Cobham.output_length_poly_of_mem_FP qStr_mem_FP
  obtain ⟨Pw, hPw⟩ := Cobham.output_length_poly_of_mem_FP (polyRulerFn_mem_FP Wp hred)
  obtain ⟨Pn, hPn⟩ := Cobham.output_length_poly_of_mem_FP (posCount_mem_FP (codesE_comp hred))
  have hDU : (fun x => DU (red x) ++ [true]) ∈ FP :=
    Cobham.appendFn_mem_FP (DU_comp hred) (constFn_mem_FP _)
  obtain ⟨Pm, hPm⟩ := Cobham.output_length_poly_of_mem_FP (mulLen_mem_FP hDU (qStr_comp hred))
  obtain ⟨Pc, hPc⟩ := Cobham.output_length_poly_of_mem_FP (codesE_comp hred)
  obtain ⟨Pp, hPp⟩ := Cobham.output_length_poly_of_mem_FP (pt0_comp hred)
  obtain ⟨Pq, hPq⟩ := Cobham.output_length_poly_of_mem_FP (qStr_comp hred)
  obtain ⟨Pcl, hPcl⟩ := Cobham.output_length_poly_of_mem_FP (cl0_comp hred)
  obtain ⟨Rp, hRp⟩ : ∃ Rp : Polynomial ℕ, Rp = Pn + 1 := ⟨_, rfl⟩
  obtain ⟨Cp, hCp⟩ : ∃ Cp : Polynomial ℕ, Cp = Rp * Pw := ⟨_, rfl⟩
  obtain ⟨Mp, hMp⟩ : ∃ Mp : Polynomial ℕ,
    Mp = 2 * Pc + 2 * Pp + Pq + Pcl + Polynomial.C 8 + Pm := ⟨_, rfl⟩
  have hMp' : ∀ n, Mp.eval n = 2 * Pc.eval n + 2 * Pp.eval n + Pq.eval n + Pcl.eval n + 8
      + Pm.eval n := fun n => by
    rw [hMp]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_C]
  have hM : ∀ (x r : List Bool) (τ : Transcript),
      (shenVmsgOn red Wp (protocolView x r τ)).length ≤ Mp.eval x.length := by
    intro x r τ
    rw [shenVmsgOn_view]
    have h := shenVmsg_length_le Wp (protocolView (red x) r τ)
    rw [RepArgs.vx_view] at h
    have h1 := hPc x
    have h2 := hPp x
    have h3 := hPq x
    have h4 := hPcl x
    rw [hMp']
    omega
  -- the per-input context and the hypotheses of the protocol lemmas
  have key : ∀ x, ∃ Γ : ShenCtx, Γ.I = inst x ∧ Γ.x = red x := fun x => by
    obtain ⟨Γ, hΓ⟩ := exists_shenCtx (inst x) (hwf x)
    exact ⟨Γ, hΓ, by rw [ShenCtx.x, hΓ, hinst]⟩
  have hv : ∀ (x : List Bool) (Γ : ShenCtx), Γ.x = red x → ∀ r τ,
      (shenProtocolOn red hred Wp Rp Cp Mp hM).vmsg (protocolView x r τ)
        = shenVmsg Wp (protocolView Γ.x r τ) := fun x Γ hΓx r τ => by
    rw [shenProtocolOn_vmsg, shenVmsgOn_view, hΓx]
  have hverdict : ∀ (x : List Bool) (Γ : ShenCtx), Γ.x = red x → ∀ r τ,
      protocolView x r τ ∈ (shenProtocolOn red hred Wp Rp Cp Mp hM).verdict
        ↔ protocolView Γ.x r τ ∈ shenVerdict := fun x Γ hΓx r τ => by
    rw [shenProtocolOn_verdict, mem_shenVerdictOn_iff, redView_view, hΓx]
  have hR : ∀ x : List Bool, (shenProtocolOn red hred Wp Rp Cp Mp hM).rounds x.length
      = Pn.eval x.length + 1 := fun x => by
    rw [shenProtocolOn_rounds, hRp, Polynomial.eval_add, Polynomial.eval_one]
  have hRn : ∀ (x : List Bool) (Γ : ShenCtx), Γ.x = red x → Γ.n + 1 ≤ Pn.eval x.length + 1 :=
    fun x Γ hΓx => by
      have h := hPn x
      rw [← hΓx, Γ.codesE_eq', posCount_eq, List.length_replicate, Γ.codes_length] at h
      omega
  have hwW : ∀ (Γ : ShenCtx), Γ.w ≤ Wp.eval Γ.x.length := fun Γ => by
    have h := hWp Γ.x
    rwa [Γ.qStr_length] at h
  have hT : ∀ (x : List Bool) (Γ : ShenCtx), Γ.x = red x →
      (Pn.eval x.length + 1) * Wp.eval Γ.x.length
        ≤ (shenProtocolOn red hred Wp Rp Cp Mp hM).coins x.length := fun x Γ hΓx => by
    rw [shenProtocolOn_coins, hCp, Polynomial.eval_mul, hRp, Polynomial.eval_add,
      Polynomial.eval_one]
    refine Nat.mul_le_mul_left _ ?_
    have h := hPw x
    rwa [polyRuler_length, ← hΓx] at h
  refine ⟨shenProtocolOn red hred Wp Rp Cp Mp hM, Rp, Cp, Mp, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, ?_, ?_⟩
  · intro x hx
    obtain ⟨Γ, hΓI, hΓx⟩ := key x
    refine ⟨Γ.honestS, ?_, ?_⟩
    · intro σ
      rw [shenProtocolOn_msgLen, ShenCtx.honestS, coeffBlocks_flatten_length]
      have h := hPm x
      rw [length_mulLen, List.length_append, ← hΓx, Γ.DU_len, Γ.qStr_length] at h
      rw [hMp']
      simp only [List.length_singleton] at h
      omega
    · rw [Γ.eventProb_honestS _ x Wp (hv x Γ hΓx) (hverdict x Γ hΓx) _ _ rfl (hR x)
        (hRn x Γ hΓx) (hwW Γ) (hT x Γ hΓx) (by rw [hΓI]; exact (hL x).mp hx)]
      norm_num
  · intro x hx S _
    obtain ⟨Γ, hΓI, hΓx⟩ := key x
    have hfalse : QBF.eval (fun _ => false) (toQBF Γ.I.1 (cnfQBF Γ.I.2)) = false := by
      rw [hΓI]
      exact Bool.eq_false_iff.mpr fun h => hx ((hL x).mpr h)
    refine le_trans (Γ.eventProb_le _ x Wp (hv x Γ hΓx) (hverdict x Γ hΓx) S _ _ rfl (hR x)
      (hRn x Γ hΓx) (hwW Γ) (hT x Γ hΓx) hfalse) ?_
    have hp : (0 : ℚ) < Γ.p := by exact_mod_cast Γ.hp.pos
    have h6 : 6 * (Γ.n * Γ.D) + 1 ≤ Γ.p := by
      have h := Γ.hN
      have h2 := Γ.NU_length'
      change (NU Γ.x).length < Γ.p at h
      rw [mul_assoc] at h2
      omega
    rw [div_le_iff₀ hp]
    have : ((6 * (Γ.n * Γ.D) + 1 : ℕ) : ℚ) ≤ Γ.p := by exact_mod_cast h6
    push_cast at this
    linarith

end Complexity
