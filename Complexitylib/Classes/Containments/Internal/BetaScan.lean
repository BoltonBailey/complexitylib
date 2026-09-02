/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.FamStep

/-!
# Forcing the guessed choice bit

⚠️ Unreviewed by Bolton

A configuration has two successors, one per nondeterministic choice, and a certificate that a code
is *not* a successor has to rule out both. The successor check verifies the guessed parameters
against the machine's own transition table, so the successor is determined by the choice bit — but
the guess picks that bit, and a lying guess would offer the same successor twice.

`Complexity.betaScanner` closes that: it reads the one cell of the parameter block that carries
`Complexity.SuccParams.beta` and demands a given value. Run once with `false` and once with `true`,
the two checks name the two successors.

## Main definitions

- `betaScanner` — the check that the guessed choice bit is a given value

## Main results

- `enc_beta` — where the choice bit sits in a parameter block
- `betaScanner_run`, `beta_eq_of_holdsBits`, `holdsBits_beta_cell`
-/

@[expose] public section

namespace Complexity

/-- **Where the choice bit sits**: the parameter block starts with the input symbol's two bits,
and the choice is the next one. -/
theorem enc_beta {Q : Type} [Fintype Q] [Nonempty Q] {k : ℕ} (P : SuccParams Q k) :
    ((succParamsCodec Q k).enc P)[2]? = some P.beta := by
  show ((BitCodec.gamma.enc P.inSym) ++
    (BitCodec.bool.prod ((qCodec Q).prod ((BitCodec.fn k BitCodec.gamma).prod
      BitCodec.gamma))).enc (P.beta, P.q, P.wSym, P.oSym))[2]? = _
  rw [gamma_enc_eq]
  rfl

/-- **The cell of the scan that carries the choice bit.** -/
theorem holdsBits_beta_cell {Q : Type} [Fintype Q] [Nonempty Q] {k jj : ℕ}
    (cols : ℕ → Fin (jj + 1) → Γ) (par : Fin (jj + 1)) (P : SuccParams Q k)
    (hP : HoldsBits cols 0 par ((succParamsCodec Q k).enc P)) :
    cols 3 par = Γ.ofBool P.beta := by
  have hw : 2 < ((succParamsCodec Q k).enc P).length := by
    rw [(succParamsCodec Q k).enc_length, succParamsCodec_width]
    omega
  have h := hP 2 hw
  rw [show (0 : ℕ) + 2 + 1 = 3 from rfl] at h
  rw [h]
  refine congrArg Γ.ofBool ?_
  have he := enc_beta P
  rw [List.getElem?_eq_getElem hw] at he
  exact Option.some_injective _ he

/-- **The check that the guessed choice bit is `b`.** -/
noncomputable def betaScanner (jj : ℕ) (par : Fin (jj + 1)) (b : Bool) : Scanner jj :=
  ((Scanner.isConst jj par (Γ.ofBool b)).after 2).upTo 3

/-- **What it decides.** -/
theorem betaScanner_run (jj : ℕ) (par : Fin (jj + 1)) (b : Bool)
    (cols : ℕ → Fin (jj + 1) → Γ) (len : ℕ) (hlen : 3 ≤ len) :
    (betaScanner jj par b).emit ((betaScanner jj par b).run cols len) = true ↔
      cols 3 par = Γ.ofBool b := by
  rw [betaScanner, Scanner.isConst_range_run jj par (Γ.ofBool b) cols 2 3 len hlen]
  exact ⟨fun h => h 3 (by omega) (by omega), fun h q h1 h2 => by
    rw [show q = 3 by omega]; exact h⟩

/-- **An accepting check pins the guessed choice bit.** -/
theorem beta_eq_of_holdsBits {Q : Type} [Fintype Q] [Nonempty Q] {k jj : ℕ}
    (cols : ℕ → Fin (jj + 1) → Γ) (par : Fin (jj + 1)) (P : SuccParams Q k) (b : Bool)
    (hP : HoldsBits cols 0 par ((succParamsCodec Q k).enc P))
    (hv : cols 3 par = Γ.ofBool b) : P.beta = b :=
  ofBool_injective ((holdsBits_beta_cell cols par P hP).symm.trans hv)

/-- **The decoder reads the choice bit off the same cell.** A guessed parameter block need not be
canonical, so what a check pins is the *cell*; this is what that says about the parameters the
scan decodes. -/
theorem beta_dec_eq {Q : Type} [Fintype Q] [Nonempty Q] {k jj : ℕ}
    (cols : ℕ → Fin (jj + 1) → Γ) (par : Fin (jj + 1)) (bitsPar : List Bool)
    (hlen : bitsPar.length = (succParamsCodec Q k).width)
    (hpar : HoldsBits cols 0 par bitsPar) (β : Bool) (hv : cols 3 par = Γ.ofBool β) :
    ((succParamsCodec Q k).dec bitsPar).beta = β := by
  have h3 : 2 < bitsPar.length := by
    rw [hlen, succParamsCodec_width]
    omega
  have hb := hpar 2 h3
  rw [show (0 : ℕ) + 2 + 1 = 3 from rfl, hv] at hb
  have hbit : bitsPar[2] = β := (ofBool_injective hb).symm
  have hd : bitsPar.drop 2 = bitsPar[2] :: bitsPar.drop 3 := List.drop_eq_getElem_cons h3
  show ((bitsPar.drop 2).take 1).headI = β
  rw [hd]
  exact hbit

/-- **The check that the new tuple is *the* `β`-successor of the old one.** The walk's successor
branch, with the choice bit pinned. -/
noncomputable def succCertScanner {kk jj : ℕ} (tm : NTM kk) (nn S : ℕ)
    (par mv dr res : Fin (jj + 1)) (dc : DirCodec) (j j' : ℕ → Fin (jj + 1)) (β : Bool) :
    Scanner jj :=
  Scanner.all 5 (fun p =>
    if p.val = 0 then succScanner tm nn S par (codeRegsOf j) (codeRegsOf j')
    else if p.val = 1 then dirCheckScanner tm nn S par mv dr (codeRegsOf (kk := kk) j).hd
      (codeRegsOf (kk := kk) j').hd dc
    else if p.val = 2 then inSymScanner tm nn S par (codeRegsOf (kk := kk) j).hd res
    else if p.val = 3 then tailZeroScanner tm nn S j'
    else betaScanner jj par β)

/-- **An accepting successor certificate names the successor.** -/
theorem succCertScanner_sound {kk jj : ℕ} (tm : NTM kk) (x : List Bool) (S : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (par mv dr res : Fin (jj + 1)) (dc : DirCodec)
    (j j' : ℕ → Fin (jj + 1)) (a : Code tm.Q kk x.length S) (P : SuccParams tm.Q kk) (g : Γ)
    (bitsPar : List Bool) (hlenPar : bitsPar.length = (succParamsCodec tm.Q kk).width)
    (hpar : HoldsBits cols 0 par bitsPar)
    (hPdec : (succParamsCodec tm.Q kk).dec bitsPar = P)
    (ha : HoldsCodeTail tm x S cols j a)
    (bits : ℕ → List Bool)
    (hbitsLen : ∀ p, p < kk + 3 → (bits p).length = blockLen tm x.length S p)
    (hbits : ∀ p, p < kk + 3 → HoldsBits cols 0 (j' p) (bits p))
    (hclampIn : a.1 ≠ tm.qhalt → a.1 = P.q → P.inSym = inSymOf tm x S a →
      (∀ i, (a.2.2.1 i).2 (a.2.2.1 i).1 = P.wSym i) → a.2.2.2.2 a.2.2.2.1 = P.oSym →
      movedIdx (succTrans tm P).2.2.2.1 a.2.1.val ≤ x.length + S + 1)
    (hres : cols 1 res = Γ.ofBool (TM.inMatchVerdict gammaBits g (cols 1 par) (cols 2 par)))
    (hg : a.2.1.val ≠ 0 → g = inSymOf tm x S a) (β : Bool)
    (hv : (succCertScanner tm x.length S par mv dr res dc j j' β).emit
      ((succCertScanner tm x.length S par mv dr res dc j j' β).run cols
        (walkScanLen tm x.length S)) = true) :
    ∃ b : Code tm.Q kk x.length S, HoldsCodeTail tm x S cols j' b ∧ a.1 ≠ tm.qhalt ∧
      b = succCode tm x S β a := by
  rw [succCertScanner, Scanner.all_emit_run] at hv
  have h0 := hv ⟨0, by omega⟩
  have h1 := hv ⟨1, by omega⟩
  have h2 := hv ⟨2, by omega⟩
  have h3 := hv ⟨3, by omega⟩
  have h4 := hv ⟨4, by omega⟩
  rw [if_pos (rfl : (0 : ℕ) = 0)] at h0
  rw [if_neg (by exact (by omega : (1 : ℕ) ≠ 0)), if_pos (rfl : (1 : ℕ) = 1)] at h1
  rw [if_neg (by exact (by omega : (2 : ℕ) ≠ 0)),
    if_neg (by exact (by omega : (2 : ℕ) ≠ 1)), if_pos (rfl : (2 : ℕ) = 2)] at h2
  rw [if_neg (by exact (by omega : (3 : ℕ) ≠ 0)),
    if_neg (by exact (by omega : (3 : ℕ) ≠ 1)),
    if_neg (by exact (by omega : (3 : ℕ) ≠ 2)), if_pos (rfl : (3 : ℕ) = 3)] at h3
  rw [if_neg (by exact (by omega : (4 : ℕ) ≠ 0)),
    if_neg (by exact (by omega : (4 : ℕ) ≠ 1)),
    if_neg (by exact (by omega : (4 : ℕ) ≠ 2)),
    if_neg (by exact (by omega : (4 : ℕ) ≠ 3))] at h4
  obtain ⟨b, hbTail, hne, hbSucc, -, -, -⟩ :=
    succBranch_sound tm x S cols par mv dr res dc j j' a P g bitsPar hlenPar hpar hPdec ha
      bits hbitsLen hbits hclampIn hres hg h0 h1 h2 h3
  have hbeta : P.beta = β := by
    rw [← hPdec]
    exact beta_dec_eq cols par bitsPar hlenPar hpar β
      ((betaScanner_run jj par β cols (walkScanLen tm x.length S)
        (by rw [walkScanLen, succParamsCodec_width]; omega)).mp h4)
  exact ⟨b, hbTail, hne, by rw [hbSucc, hbeta]⟩

end Complexity
