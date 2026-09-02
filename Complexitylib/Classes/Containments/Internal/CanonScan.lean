/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.OddInner

/-!
# Certifying that a guessed tuple spells out a code

⚠️ Unreviewed by Bolton

The counting split lists non-members of a round, and a non-member is *guessed* — nothing pins
its tuple to a named code the way a walk pins its endpoints. For the count to mean anything the
guessed tuple must spell out *some* code, and this file is that check: every `BitCodec` has a
total decoder inverting the encoder, so a register's bits lie in the encoder's range exactly
when re-encoding their decoded value reproduces them. One generic scanner does this for every
block — the state field, the input-head field, and the windows alike — and the padding and tail
cells are pinned by the existing `Complexity.padZeroScanner` and `Complexity.tailZeroScanner`.

## Main definitions

- `roundtripScanner` — accumulate a field's bits, accept iff re-encoding their decode gives
  them back
- `canonScanner` — every block of a tuple is a code's block

## Main results

- `canonScanner_sound` — accepted means the tuple's bits are `codeBlockScan` of some code
- `canonScanner_accepts` — and an honest tuple is accepted
-/

@[expose] public section

namespace Complexity

variable {kk jj r : ℕ} {tm : NTM kk} {S wc : ℕ}

/-! ## The generic roundtrip check -/

/-- The bit a register holds where a cell spells a bit. -/
theorem bitAt_ofBool {j : ℕ} (cols : ℕ → Fin (j + 1) → Γ) (r : Fin (j + 1)) (p : ℕ) (b : Bool)
    (h : cols p r = Γ.ofBool b) : Scanner.bitAt cols r p = b := by
  rw [Scanner.bitAt, h]
  cases b <;> simp [Γ.ofBool]

/-- Reading a list inside its length is reading the element. -/
theorem getD_of_lt (l : List Bool) (d : Bool) (n : ℕ) (h : n < l.length) :
    l.getD n d = l[n]'h := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- **The roundtrip check**: read a field's bits into a table, and accept exactly when
re-encoding their decoded value reproduces them — that is, when the field lies in the encoder's
range. -/
noncomputable def roundtripScanner {α : Type} (c : BitCodec α) (r : Fin (jj + 1)) :
    Scanner jj :=
  Scanner.ofRight (Fin (c.width + 1) × (Fin 1 → Fin c.width → Bool))
    (⟨0, Nat.zero_lt_succ _⟩, fun _ _ => false)
    (Scanner.bitsStep 1 c.width (fun _ => r))
    (fun s => decide (c.enc (c.ofTable (s.2 0)) = List.ofFn (s.2 0)))

theorem rightOnly_roundtripScanner {α : Type} (c : BitCodec α) (r : Fin (jj + 1)) :
    Scanner.RightOnly (roundtripScanner c r) :=
  Scanner.rightOnly_ofRight _ _ _ _

/-- A scanner with an idle leftward pass runs its rightward automaton. -/
theorem ofRight_runR_eq_auxRun {τ : Type} [DecidableEq τ] [Fintype τ] (start : τ)
    (step : τ → (Fin (jj + 1) → Γ) → τ) (emit : τ → Bool) (cols : ℕ → Fin (jj + 1) → Γ)
    (p : ℕ) :
    (Scanner.ofRight τ start step emit).runR cols p = Scanner.auxRun start step cols p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [Scanner.runR, Scanner.auxRun, ih]; rfl

/-- **The field reader freezes at the field's end**: past `w` cells the table stops changing. -/
theorem auxRun_bitsStep_freeze {s w : ℕ} (regs : Fin s → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (x₀ : Fin s → Fin w → Bool) (len : ℕ) (hlen : w ≤ len) :
    Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs) cols len
      = Scanner.auxRun (⟨0, Nat.zero_lt_succ w⟩, x₀) (Scanner.bitsStep s w regs) cols w := by
  induction len with
  | zero =>
      have h0 : w = 0 := by omega
      subst h0
      rfl
  | succ len ih =>
      rcases Nat.lt_or_ge len w with h | h
      · have h1 : w = len + 1 := by omega
        subst h1
        rfl
      · rw [Scanner.auxRun, ih h, Scanner.bitsStep,
          dif_neg (by
            rw [(Scanner.bitsStep_run s w regs cols x₀ w le_rfl).1]
            omega)]

/-- **What the roundtrip check reports**: the verdict of re-encoding the field it read. -/
theorem roundtripScanner_emit {α : Type} (c : BitCodec α) (r : Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (len : ℕ) (hlen : c.width ≤ len) :
    (roundtripScanner c r).emit ((roundtripScanner c r).run cols len)
      = decide (c.enc (c.ofTable (fun i => Scanner.bitAt cols r (i.val + 1)))
        = List.ofFn (fun i : Fin c.width => Scanner.bitAt cols r (i.val + 1))) := by
  have htab : (Scanner.auxRun (⟨0, Nat.zero_lt_succ c.width⟩, fun _ _ => false)
      (Scanner.bitsStep 1 c.width (fun _ => r)) cols c.width).2 0
      = fun i => Scanner.bitAt cols r (i.val + 1) := by
    funext i
    exact (Scanner.bitsStep_run 1 c.width (fun _ => r) cols (fun _ _ => false)
      c.width le_rfl).2 0 i i.isLt
  rw [roundtripScanner, Scanner.ofRight_run, ofRight_runR_eq_auxRun,
    auxRun_bitsStep_freeze _ cols _ len hlen]
  show decide _ = decide _
  rw [htab]

/-- **What an offset roundtrip check forces.** Given the register's bits, acceptance means the
field slice is the encoding of its own decode. -/
theorem roundtrip_after_forces {α : Type} (c : BitCodec α) (r : Fin (jj + 1)) (w : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (len : ℕ) (hlen : w + c.width ≤ len)
    (b : List Bool) (hb : ∀ q, (hq : q < b.length) → cols (q + 1) r = Γ.ofBool (b[q]'hq))
    (hblen : w + c.width ≤ b.length)
    (hacc : ((roundtripScanner c r).after w).emit
      (((roundtripScanner c r).after w).run cols len) = true) :
    c.enc (c.ofTable (fun i => b.getD (w + i.val) false))
      = List.ofFn (fun i : Fin c.width => b.getD (w + i.val) false) := by
  rw [Scanner.after_emit_run _ (rightOnly_roundtripScanner c r),
    roundtripScanner_emit c r _ (len - w) (by omega)] at hacc
  have htab : (fun i : Fin c.width => Scanner.bitAt (fun q => cols (w + q)) r (i.val + 1))
      = fun i : Fin c.width => b.getD (w + i.val) false := by
    funext i
    have hq : w + i.val < b.length := by omega
    have := hb (w + i.val) hq
    rw [getD_of_lt b false _ hq]
    exact bitAt_ofBool _ r _ _ (by rw [show w + (i.val + 1) = w + i.val + 1 by omega]; exact this)
  rw [htab] at hacc
  exact of_decide_eq_true hacc

/-- **An honest field is accepted**: a register spelling out an encoding passes the roundtrip. -/
theorem roundtrip_after_accepts {α : Type} (c : BitCodec α) (r : Fin (jj + 1)) (w : ℕ)
    (cols : ℕ → Fin (jj + 1) → Γ) (len : ℕ) (hlen : w + c.width ≤ len) (a : α)
    (hcols : ∀ i, (h : i < c.width) → cols (w + i + 1) r
      = Γ.ofBool ((c.enc a)[i]'(by rw [c.enc_length]; exact h))) :
    ((roundtripScanner c r).after w).emit
      (((roundtripScanner c r).after w).run cols len) = true := by
  rw [Scanner.after_emit_run _ (rightOnly_roundtripScanner c r),
    roundtripScanner_emit c r _ (len - w) (by omega)]
  have htab : (fun i : Fin c.width => Scanner.bitAt (fun q => cols (w + q)) r (i.val + 1))
      = fun i : Fin c.width => (c.enc a)[i.val]'(by rw [c.enc_length]; exact i.isLt) := by
    funext i
    exact bitAt_ofBool _ r _ _ (by
      rw [show w + (i.val + 1) = w + i.val + 1 by omega]
      exact hcols i.val i.isLt)
  have hofn : List.ofFn (fun i : Fin c.width =>
      (c.enc a)[i.val]'(by rw [c.enc_length]; exact i.isLt)) = c.enc a := by
    refine List.ext_getElem (by simp [c.enc_length]) ?_
    intro q h1 h2
    simp
  rw [htab, hofn, show c.ofTable (fun i => (c.enc a)[i.val]'(by rw [c.enc_length]; exact i.isLt))
      = a from BitCodec.ofTable_eq c a _ (fun i => rfl)]
  exact decide_eq_true rfl

/-! ## The blocks of a code tuple -/

/-- A cell in a block's padding is a zero bit. -/
theorem codeBlockScan_getElem_pad (x : List Bool) (a : Code tm.Q kk x.length S) (p : ℕ)
    (hp : p ≠ 0) (q : ℕ) (hq : q < (succParamsCodec tm.Q kk).width)
    (h : q < (codeBlockScan tm x S a p).length) : (codeBlockScan tm x S a p)[q]'h = false := by
  have hstruct : codeBlockScan tm x S a p
      = List.replicate (succParamsCodec tm.Q kk).width false
        ++ (codeBlock tm x S a p ++ [false]) := by
    rw [codeBlockScan, if_neg hp]
  rw [List.getElem_of_eq hstruct h,
    List.getElem_append_left (by rwa [List.length_replicate]), List.getElem_replicate]

/-- A cell in a block's field is the corresponding cell of the code's block. -/
theorem codeBlockScan_getElem_field (x : List Bool) (a : Code tm.Q kk x.length S) (p : ℕ)
    (hp : p ≠ 0) (i : ℕ) (hi : i < codeWidthRaw tm x.length S p)
    (h : (succParamsCodec tm.Q kk).width + i < (codeBlockScan tm x S a p).length) :
    (codeBlockScan tm x S a p)[(succParamsCodec tm.Q kk).width + i]'h
      = (codeBlock tm x S a p)[i]'(by rw [codeBlock_length]; exact hi) := by
  have hstruct : codeBlockScan tm x S a p
      = List.replicate (succParamsCodec tm.Q kk).width false
        ++ (codeBlock tm x S a p ++ [false]) := by
    rw [codeBlockScan, if_neg hp]
  have hcb : (codeBlock tm x S a p).length = codeWidthRaw tm x.length S p :=
    codeBlock_length tm x S a p
  rw [List.getElem_of_eq hstruct h,
    List.getElem_append_right (by rw [List.length_replicate]; omega)]
  rw [List.getElem_append_left (by rw [List.length_replicate]; omega)]
  congr 1
  rw [List.length_replicate]
  omega

/-- **One block's canonicity check**: the field decodes and re-encodes to itself. -/
noncomputable def blockRoundtrip (tm : NTM kk) (nn S : ℕ) (cT : ℕ → Fin (jj + 1)) (p : ℕ) :
    Scanner jj :=
  if p = 0 then (roundtripScanner (qCodec tm.Q) (cT 0)).after 0
  else if p = 1 then
    (roundtripScanner (finCodec (nn + S + 2)) (cT 1)).after (succParamsCodec tm.Q kk).width
  else if p < kk + 2 then
    (roundtripScanner (tapeCodec (S + 1)) (cT p)).after (succParamsCodec tm.Q kk).width
  else (roundtripScanner (tapeCodec (S + 2)) (cT p)).after (succParamsCodec tm.Q kk).width

/-- **The whole tuple's canonicity check**: every block's field is in its encoder's range, the
padding is zero, and the cell past each field is zero. -/
noncomputable def canonScanner (tm : NTM kk) (nn S : ℕ) (cT : ℕ → Fin (jj + 1)) : Scanner jj :=
  Scanner.all 3 (fun t =>
    if t.val = 0 then Scanner.all (kk + 3) (fun p => blockRoundtrip tm nn S cT p.val)
    else if t.val = 1 then padZeroScanner tm cT
    else tailZeroScanner tm nn S cT)

/-- **Accepted means canonical.** Given the bits every block holds — which the guessing stage
supplies — acceptance of the canonicity check produces the code the tuple spells out. -/
theorem canonScanner_sound (x : List Bool) (cT : ℕ → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (bits : ℕ → List Bool)
    (hlen : ∀ p, p < kk + 3 → (bits p).length = blockLen tm x.length S p)
    (hbits : ∀ p, p < kk + 3 → HoldsBits cols 0 (cT p) (bits p))
    (hacc : (canonScanner tm x.length S cT).emit
      ((canonScanner tm x.length S cT).run cols (walkScanLen tm x.length S)) = true) :
    ∃ u : Code tm.Q kk x.length S,
      ∀ p, p < kk + 3 → bits p = codeBlockScan tm x S u p := by
  classical
  rw [canonScanner, Scanner.all_emit_run] at hacc
  have hrt := hacc ⟨0, by omega⟩
  rw [if_pos rfl, Scanner.all_emit_run] at hrt
  have hpad := hacc ⟨1, by omega⟩
  rw [if_neg (by omega : (1 : ℕ) ≠ 0), if_pos rfl, padZeroScanner_decides tm x.length S] at hpad
  have htail := hacc ⟨2, by omega⟩
  rw [if_neg (by omega : (2 : ℕ) ≠ 0), if_neg (by omega : (2 : ℕ) ≠ 1),
    tailZeroScanner_decides tm x.length S] at htail
  set pw := (succParamsCodec tm.Q kk).width with hpw
  -- the bits each block holds, as a function the codecs can read
  have hb : ∀ p, p < kk + 3 → ∀ q, (hq : q < (bits p).length) →
      cols (q + 1) (cT p) = Γ.ofBool ((bits p)[q]'hq) := by
    intro p hp q hq
    have := hbits p hp q hq
    rwa [Nat.zero_add] at this
  -- padding and tail of every nonzero block, read back into the bits
  have hbpad : ∀ p, 0 < p → p < kk + 3 → ∀ q, (hq : q < pw) →
      (h : q < (bits p).length) → (bits p)[q]'h = false := by
    intro p hp0 hp q hq h
    have hcell := hpad ⟨p - 1, by omega⟩ (q + 1) (by omega) (by omega)
    rw [show p - 1 + 1 = p by omega] at hcell
    have := hb p hp q h
    rw [hcell] at this
    exact ofBool_injective this.symm
  have hbtail : ∀ p, 0 < p → p < kk + 3 →
      (h : blockLen tm x.length S p - 1 < (bits p).length) →
      (bits p)[blockLen tm x.length S p - 1]'h = false := by
    intro p hp0 hp h
    have hone : 1 ≤ blockLen tm x.length S p := one_le_blockLen tm x.length S p (by omega)
    have hcell := htail ⟨p - 1, by omega⟩
    rw [show p - 1 + 1 = p by omega] at hcell
    have := hb p hp (blockLen tm x.length S p - 1) h
    rw [show blockLen tm x.length S p - 1 + 1 = blockLen tm x.length S p by omega,
      hcell] at this
    exact ofBool_injective this.symm
  -- the roundtrip verdict of each block, in `forces` form
  have hforce : ∀ (p : ℕ) (hp : p < kk + 3) {α : Type} (c : BitCodec α) (w : ℕ)
      (hw : w + c.width ≤ blockLen tm x.length S p)
      (heq : blockRoundtrip tm x.length S cT p = (roundtripScanner c (cT p)).after w),
      c.enc (c.ofTable (fun i => (bits p).getD (w + i.val) false))
        = List.ofFn (fun i : Fin c.width => (bits p).getD (w + i.val) false) := by
    intro p hp α c w hw heq
    have h := hrt ⟨p, hp⟩
    rw [heq] at h
    exact roundtrip_after_forces c (cT p) w cols (walkScanLen tm x.length S)
      (le_trans hw (blockLen_le tm x.length S p)) (bits p) (hb p hp)
      (by rw [hlen p hp]; exact hw) h
  -- widths per block
  have hw0 : blockLen tm x.length S 0 = (qCodec tm.Q).width := by
    rw [blockLen, if_pos rfl, codeWidthRaw, if_pos rfl]
  have hwblock : ∀ p, 0 < p → p < kk + 3 →
      blockLen tm x.length S p = pw + codeWidthRaw tm x.length S p + 1 := by
    intro p hp0 hp
    rw [blockLen, if_neg (by omega)]
    omega
  -- the code the tuple spells out
  set u : Code tm.Q kk x.length S :=
    ((qCodec tm.Q).ofTable (fun i => (bits 0).getD (0 + i.val) false),
      (finCodec (x.length + S + 2)).ofTable (fun i => (bits 1).getD (pw + i.val) false),
      fun w : Fin kk => (tapeCodec (S + 1)).ofTable
        (fun i => (bits (w.val + 2)).getD (pw + i.val) false),
      (tapeCodec (S + 2)).ofTable (fun i => (bits (kk + 2)).getD (pw + i.val) false)) with hu
  refine ⟨u, ?_⟩
  intro p hp
  -- per block: the bits are the pad, the encoded field, and the tail zero
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · -- the state block: no pad, no tail
    have henc := hforce 0 (by omega) (qCodec tm.Q) 0 (by omega) (by
      rw [blockRoundtrip, if_pos rfl])
    rw [codeBlockScan, if_pos rfl, codeBlock_st,
      show u.1 = (qCodec tm.Q).ofTable (fun i => (bits 0).getD (0 + i.val) false) from rfl,
      henc]
    refine List.ext_getElem (by rw [List.length_ofFn, hlen 0 (by omega), hw0]) ?_
    intro q h1 h2
    rw [List.getElem_ofFn]
    show (bits 0)[q]'h1 = (bits 0).getD (0 + q) false
    rw [Nat.zero_add, getD_of_lt (bits 0) false q h1]
  · -- a padded block: identify the codec by the branch
    have hwr : codeWidthRaw tm x.length S p =
        (if p = 1 then (finCodec (x.length + S + 2)).width
          else if p < kk + 2 then (tapeCodec (S + 1)).width
          else (tapeCodec (S + 2)).width) := by
      rw [codeWidthRaw, if_neg (by omega)]
      split_ifs with h1 h2 <;> rfl
    -- one uniform argument over the three branches
    have hcore : ∀ {α : Type} (c : BitCodec α) (a : α)
        (heq : blockRoundtrip tm x.length S cT p = (roundtripScanner c (cT p)).after pw)
        (hwidth : codeWidthRaw tm x.length S p = c.width)
        (hval : c.ofTable (fun i => (bits p).getD (pw + i.val) false) = a)
        (hblock : codeBlock tm x S u p = c.enc a),
        bits p = codeBlockScan tm x S u p := by
      intro α c a heq hwidth hval hblock
      have henc := hforce p hp c pw (by rw [hwblock p hp0 hp, hwidth]; omega) heq
      have hlenbp := hlen p hp
      have hscanlen : (codeBlockScan tm x S u p).length = blockLen tm x.length S p :=
        codeBlockScan_length tm x S u p
      refine List.ext_getElem (by rw [hlenbp, hscanlen]) ?_
      intro q h1 h2
      have hqb : q < blockLen tm x.length S p := by rwa [hlenbp] at h1
      rcases Nat.lt_or_ge q pw with hqpad | hqfield
      · rw [codeBlockScan_getElem_pad x u p (by omega) q hqpad h2]
        exact hbpad p hp0 hp q hqpad h1
      · rcases Nat.lt_or_ge q (pw + c.width) with hqf | hqtail
        · have hi : q - pw < codeWidthRaw tm x.length S p := by rw [hwidth]; omega
          have hcw : q - pw < c.width := by omega
          have hencl : q - pw < (c.enc a).length := by rw [c.enc_length]; exact hcw
          have hofn : q - pw < (List.ofFn (fun i : Fin c.width =>
              (bits p).getD (pw + i.val) false)).length := by
            rw [List.length_ofFn]; exact hcw
          have hfield2 : (codeBlockScan tm x S u p)[q]'h2 = (c.enc a)[q - pw]'hencl := by
            have h2' : pw + (q - pw) < (codeBlockScan tm x S u p).length := by
              rw [show pw + (q - pw) = q by omega]; exact h2
            calc (codeBlockScan tm x S u p)[q]'h2
                = (codeBlockScan tm x S u p)[pw + (q - pw)]'h2' := by congr 1; omega
              _ = (codeBlock tm x S u p)[q - pw]'(by rw [codeBlock_length]; exact hi) :=
                  codeBlockScan_getElem_field x u p (by omega) (q - pw) hi h2'
              _ = (c.enc a)[q - pw]'hencl := List.getElem_of_eq hblock _
          rw [hfield2]
          calc (bits p)[q]'h1
              = (bits p).getD (pw + (q - pw)) false := by
                rw [show pw + (q - pw) = q by omega, getD_of_lt (bits p) false q h1]
            _ = (List.ofFn (fun i : Fin c.width => (bits p).getD (pw + i.val) false))[q - pw]'
                  hofn := by rw [List.getElem_ofFn]
            _ = (c.enc (c.ofTable (fun i => (bits p).getD (pw + i.val) false)))[q - pw]'(by
                  rw [henc]; exact hofn) := (List.getElem_of_eq henc.symm _)
            _ = (c.enc a)[q - pw]'hencl := List.getElem_of_eq (by rw [hval]) _
        · -- the tail cell
          have hqeq : q = blockLen tm x.length S p - 1 := by
            rw [hwblock p hp0 hp, hwidth] at hqb ⊢
            omega
          subst hqeq
          rw [codeBlockScan_tail tm x S u p (by omega) h2]
          exact hbtail p hp0 hp h1
    rcases Nat.lt_or_ge p (kk + 2) with hplt | hpge
    · rcases Nat.eq_or_lt_of_le hp0 with hp1 | hp2
      · -- the input-head block
        refine hcore (finCodec (x.length + S + 2)) _ ?_ ?_ rfl ?_
        · rw [blockRoundtrip, if_neg (by omega), if_pos hp1.symm, ← hp1]
        · rw [hwr, if_pos hp1.symm]
        · rw [← hp1, codeBlock_hd]
      · -- a work window
        have hpi : p = (⟨p - 2, by omega⟩ : Fin kk).val + 2 := by simp; omega
        refine hcore (tapeCodec (S + 1)) _ ?_ ?_ rfl ?_
        · rw [blockRoundtrip, if_neg (by omega), if_neg (by omega), if_pos hplt]
        · rw [hwr, if_neg (by omega), if_pos hplt]
        · rw [hpi, codeBlock_wk]
    · -- the output window
      have hpeq : p = kk + 2 := by omega
      refine hcore (tapeCodec (S + 2)) _ ?_ ?_ rfl ?_
      · rw [blockRoundtrip, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [hwr, if_neg (by omega), if_neg (by omega)]
      · rw [hpeq, codeBlock_ot]

/-- **An honest tuple is accepted**: a tuple holding a code's blocks passes the canonicity
check. -/
theorem canonScanner_accepts (x : List Bool) (cT : ℕ → Fin (jj + 1))
    (cols : ℕ → Fin (jj + 1) → Γ) (u : Code tm.Q kk x.length S)
    (hbits : ∀ p, p < kk + 3 → HoldsBits cols 0 (cT p) (codeBlockScan tm x S u p)) :
    (canonScanner tm x.length S cT).emit
      ((canonScanner tm x.length S cT).run cols (walkScanLen tm x.length S)) = true := by
  classical
  set pw := (succParamsCodec tm.Q kk).width with hpw
  have hb : ∀ p, p < kk + 3 → ∀ q, (hq : q < (codeBlockScan tm x S u p).length) →
      cols (q + 1) (cT p) = Γ.ofBool ((codeBlockScan tm x S u p)[q]'hq) := by
    intro p hp q hq
    have := hbits p hp q hq
    rwa [Nat.zero_add] at this
  have hlenp : ∀ p, (codeBlockScan tm x S u p).length = blockLen tm x.length S p :=
    fun p => codeBlockScan_length tm x S u p
  rw [canonScanner, Scanner.all_emit_run]
  intro t
  rcases Nat.lt_or_ge t.val 1 with ht0 | ht1
  · -- the roundtrips
    have ht : t.val = 0 := by omega
    rw [if_pos ht, Scanner.all_emit_run]
    intro p
    -- a uniform argument over the four branches
    have hcore : ∀ {α : Type} (c : BitCodec α) (a : α) (w : ℕ)
        (heq : blockRoundtrip tm x.length S cT p.val = (roundtripScanner c (cT p.val)).after w)
        (hwlen : w + c.width ≤ blockLen tm x.length S p.val)
        (hblock : ∀ i, (h : i < c.width) →
          (codeBlockScan tm x S u p.val)[w + i]'(by rw [hlenp]; omega)
            = (c.enc a)[i]'(by rw [c.enc_length]; exact h)),
        (blockRoundtrip tm x.length S cT p.val).emit
          ((blockRoundtrip tm x.length S cT p.val).run cols (walkScanLen tm x.length S))
          = true := by
      intro α c a w heq hwlen hblock
      rw [heq]
      refine roundtrip_after_accepts c (cT p.val) w cols (walkScanLen tm x.length S)
        (le_trans hwlen (blockLen_le tm x.length S p.val)) a ?_
      intro i h
      have hq : w + i < (codeBlockScan tm x S u p.val).length := by
        rw [hlenp]
        omega
      have := hb p.val p.isLt (w + i) hq
      rw [hblock i h] at this
      exact this
    rcases Nat.eq_zero_or_pos p.val with hp0 | hppos
    · refine hcore (qCodec tm.Q) u.1 0 ?_ ?_ ?_
      · rw [blockRoundtrip, if_pos hp0, hp0]
      · rw [hp0, blockLen, if_pos rfl, codeWidthRaw, if_pos rfl]
        omega
      · intro i h
        have hcs : codeBlockScan tm x S u p.val = (qCodec tm.Q).enc u.1 := by
          rw [hp0, codeBlockScan, if_pos rfl, codeBlock_st]
        rw [List.getElem_of_eq hcs]
        simp only [Nat.zero_add]
    · have hwb : blockLen tm x.length S p.val = pw + codeWidthRaw tm x.length S p.val + 1 := by
        rw [blockLen, if_neg (by omega)]
        omega
      have hfield : ∀ {α : Type} (c : BitCodec α) (a : α)
          (hwidth : codeWidthRaw tm x.length S p.val = c.width)
          (hblock : codeBlock tm x S u p.val = c.enc a),
          ∀ i, (h : i < c.width) → (codeBlockScan tm x S u p.val)[pw + i]'(by
              rw [hlenp, hwb, hwidth]; omega)
            = (c.enc a)[i]'(by rw [c.enc_length]; exact h) := by
        intro α c a hwidth hblock i h
        rw [codeBlockScan_getElem_field x u p.val (by omega) i (by rw [hwidth]; exact h)
          (by rw [hlenp, hwb, hwidth]; omega)]
        simp only [hblock]
      rcases Nat.lt_or_ge p.val (kk + 2) with hplt | hpge
      · rcases Nat.eq_or_lt_of_le hppos with hp1 | hp2
        · refine hcore (finCodec (x.length + S + 2)) u.2.1 pw ?_ ?_ ?_
          · rw [blockRoundtrip, if_neg (by omega), if_pos hp1.symm, ← hp1]
          · rw [hwb, codeWidthRaw, if_neg (by omega), if_pos hp1.symm]
            omega
          · exact hfield (finCodec (x.length + S + 2)) u.2.1
              (by rw [codeWidthRaw, if_neg (by omega), if_pos hp1.symm])
              (by rw [← hp1, codeBlock_hd])
        · have hpi : p.val = (⟨p.val - 2, by omega⟩ : Fin kk).val + 2 := by simp; omega
          refine hcore (tapeCodec (S + 1)) (u.2.2.1 ⟨p.val - 2, by omega⟩) pw ?_ ?_ ?_
          · rw [blockRoundtrip, if_neg (by omega), if_neg (by omega), if_pos hplt]
          · rw [hwb, codeWidthRaw, if_neg (by omega), if_neg (by omega), if_pos hplt]
            have hr : (tapeCodec (S + 1)).width = (S + 1) * 3 := rfl
            omega
          · refine hfield (tapeCodec (S + 1)) _
              (by rw [codeWidthRaw, if_neg (by omega), if_neg (by omega), if_pos hplt]
                  rfl) ?_
            conv_lhs => rw [hpi]
            rw [codeBlock_wk]
      · have hpeq : p.val = kk + 2 := by omega
        refine hcore (tapeCodec (S + 2)) u.2.2.2 pw ?_ ?_ ?_
        · rw [blockRoundtrip, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [hwb, codeWidthRaw, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          have hr : (tapeCodec (S + 2)).width = (S + 2) * 3 := rfl
          omega
        · exact hfield (tapeCodec (S + 2)) u.2.2.2
            (by rw [codeWidthRaw, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
                rfl)
            (by rw [hpeq, codeBlock_ot])
  · rcases Nat.lt_or_ge t.val 2 with ht1' | ht2
    · -- the padding
      have ht : t.val = 1 := by omega
      rw [if_neg (by omega), if_pos ht, padZeroScanner_decides tm x.length S]
      intro i q h1 h2
      have hq : q - 1 < (codeBlockScan tm x S u (i.val + 1)).length := by
        rw [hlenp, blockLen, if_neg (by omega)]
        omega
      have := hb (i.val + 1) (by omega) (q - 1) hq
      rw [codeBlockScan_getElem_pad x u (i.val + 1) (by omega) (q - 1) (by omega) hq] at this
      rw [show q = q - 1 + 1 by omega]
      exact this
    · -- the tails
      have ht : t.val = 2 := by omega
      rw [if_neg (by omega), if_neg (by omega), tailZeroScanner_decides tm x.length S]
      intro i
      have hone : 1 ≤ blockLen tm x.length S (i.val + 1) :=
        one_le_blockLen tm x.length S (i.val + 1) (by omega)
      have hq : blockLen tm x.length S (i.val + 1) - 1
          < (codeBlockScan tm x S u (i.val + 1)).length := by
        rw [hlenp]
        omega
      have := hb (i.val + 1) (by omega) (blockLen tm x.length S (i.val + 1) - 1) hq
      rw [codeBlockScan_tail tm x S u (i.val + 1) (by omega) hq] at this
      rw [show blockLen tm x.length S (i.val + 1)
        = blockLen tm x.length S (i.val + 1) - 1 + 1 by omega]
      exact this

/-! ## The candidate stage -/

/-- **The candidate stage.** Guess the spare-zero tuple and check it spells out a code: after
the stage, the accumulator survives only if some code sits in `codeT`, cell for cell. This is
what lets a loop list *guessed* codes — the walk pins its tuples to named codes, but a
non-member of a round can only be guessed, and the count of non-members is a count of codes
only because of this check. -/
theorem canonStep_run (x : List Bool) (L : WalkWidths kk jj tm x.length S wc)
    (hsp : 0 < L.toWalkLayout.spares) (g : ℕ → Bool) (s : ℕ)
    (cc : Fin r) (B : ℕ) (hB1 : 1 ≤ B)
    (hB : ∀ p, p < L.toWalkLayout.stepBlocks → stepWidth L p + 2 ≤ B)
    (Wa : Fin r → Tape) (Wt : ℕ → ℕ → Γ) (inp₀ out₀ : Tape)
    (W₀ : Fin (jj + 2 + r + 1) → Tape)
    (htapes : WalkTapes (r := r) x L g s cc Wa Wt inp₀ W₀ out₀) :
    ∃ (c' : Cfg (jj + 2 + r + 1) (famStepTM L (TM.twoPassTM (canonScanner tm x.length S
        (L.toWalkLayout.famReg 2))) 2 cc).Q) (t : ℕ),
      t ≤ famTime x L r B ∧
      (famStepTM L (TM.twoPassTM (canonScanner tm x.length S
          (L.toWalkLayout.famReg 2))) 2 cc).reachesIn t
        ⟨(famStepTM L (TM.twoPassTM (canonScanner tm x.length S
          (L.toWalkLayout.famReg 2))) 2 cc).qstart, inp₀, W₀, out₀⟩ c' ∧
      (famStepTM L (TM.twoPassTM (canonScanner tm x.length S
          (L.toWalkLayout.famReg 2))) 2 cc).halted c' ∧
      WalkTapes (r := r) x L g (s + 1) cc Wa
        (fun p q => (c'.work (walkReg (L.toWalkLayout.codeT p))).cells q)
        c'.input c'.work c'.output ∧
      c'.input = TM.parkTape inp₀ ∧
      ((c'.work (auxIdx jj cc)).read = Γ.one →
        (W₀ (auxIdx jj cc)).read = Γ.one ∧
        ∃ u : Code tm.Q kk x.length S, ∀ p, p < kk + 3 →
          HoldsBits (fun q i => (c'.work (walkReg i)).cells q) 0
            (L.toWalkLayout.codeT p) (codeBlockScan tm x S u p)) ∧
      (∀ n, n < L.toWalkLayout.spares → n ≠ 0 → ∀ p, p < kk + 3 → ∀ q,
        (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
          = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q) := by
  classical
  have hf : (2 : ℕ) < 2 + L.toWalkLayout.spares := by omega
  obtain ⟨c', t, htle, hreach, hhalt, htapes', hinp', hreg, hacc, -⟩ :=
    famStep_run x L (canonScanner tm x.length S (L.toWalkLayout.famReg 2)) 2 hf g s cc B hB1
      hB Wa Wt inp₀ out₀ W₀ htapes
  have hWt : WalkTapes (r := r) x L g (s + 1) cc Wa
      (fun p q => (c'.work (walkReg (L.toWalkLayout.codeT p))).cells q)
      c'.input c'.work c'.output :=
    ⟨htapes'.1, htapes'.2.1, htapes'.2.2.1, htapes'.2.2.2.1, htapes'.2.2.2.2.1,
      htapes'.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.1,
      htapes'.2.2.2.2.2.2.2.2.1, htapes'.2.2.2.2.2.2.2.2.2.1, fun p hp q => rfl⟩
  have hspare : ∀ n, n < L.toWalkLayout.spares → n ≠ 0 → ∀ p, p < kk + 3 → ∀ q,
      (c'.work (walkReg (L.toWalkLayout.spareReg n p))).cells q
        = (W₀ (walkReg (L.toWalkLayout.spareReg n p))).cells q := by
    intro n hn hne p hp q
    rw [hreg (L.toWalkLayout.spareReg n p)]
    exact congrFun (stepCellsF_spare L 2 hf n hn (by omega) W₀
      htapes.2.1 htapes.2.2.1 p hp) q
  refine ⟨c', t, htle, hreach, hhalt, hWt, hinp', ⟨fun hone => ?_, hspare⟩⟩
  obtain ⟨hold, hverd⟩ := hacc hone
  obtain ⟨bitsG, hlenG, hbitsG⟩ :=
    exists_bits_guessedF x L 2 hf g s W₀ htapes.2.1 htapes.2.2.1
      (fun p _ => htapes.2.2.2.1 (L.toWalkLayout.reg (L.toWalkLayout.stepIdxF 2 p)).castSucc)
      htapes.2.2.2.2.2.2.2.2.2.1
  obtain ⟨u, hu⟩ := canonScanner_sound x (L.toWalkLayout.famReg 2)
    (TM.scanCol (stepCellsF L 2 W₀)) bitsG hlenG (fun p hp => hbitsG p hp) hverd
  refine ⟨hold, u, fun p hp => ?_⟩
  have hreg2 : L.toWalkLayout.famReg 2 p = L.toWalkLayout.codeT p := by
    have h := L.toWalkLayout.famReg_spare 0 p hsp hp
    rwa [L.toWalkLayout.spareReg_zero] at h
  have hbp := hbitsG p hp
  rw [hu p hp, hreg2] at hbp
  intro q hq
  show (c'.work (walkReg (L.toWalkLayout.codeT p))).cells (0 + q + 1) = _
  rw [hreg (L.toWalkLayout.codeT p)]
  exact hbp q hq

end Complexity
