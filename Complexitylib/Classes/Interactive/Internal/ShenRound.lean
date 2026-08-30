/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenParams
public import Complexitylib.Classes.Interactive.Internal.ShenWF
public import Complexitylib.Classes.Interactive.Internal.CNFArith
public import Complexitylib.Classes.Interactive
public import Complexitylib.Classes.Interactive.Internal.RepeatDefs

/-!
# The concrete verifier's round

⚠️ Unreviewed by Bolton

The verifier of Shen's protocol keeps its state in its own messages: a flag (all checks so far
passed), the remaining schedule, the current point and the current claim. `roundStep` is one
round on that state — check the prover's coefficient string against the claim for the head
operator, reduce the coin block to a challenge, move the point and the claim — and `shenVmsg`
computes the next message from a view: the initial state at round `0`, and otherwise the step on
the previous state read off the transcript. `shenVerdict` is the final check. Every component is
clamped to lengths derived from the input, which is what bounds the message length.

## Main definitions

- `stFlag`, `stOps`, `stPt`, `stCl`, `shSt`, `clampSt` — the state
- `roundStep`, `st0`, `shenVmsg`, `shenVerdict`

## Main results

- `shenVmsg_mem_FP`, `shenVerdict_mem_P`
- `shenVmsg_length_le` — the message-length bound
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

/-! ## The state -/

/-- The state: `pair flag (pair ops (pair pt cl))`. -/
def shSt (flag ops pt cl : List Bool) : List Bool := pair flag (pair ops (pair pt cl))

/-- The flag. -/
def stFlag (st : List Bool) : List Bool := pairFst st
/-- The remaining schedule. -/
def stOps (st : List Bool) : List Bool := pairFst (pairSnd st)
/-- The point. -/
def stPt (st : List Bool) : List Bool := pairFst (pairSnd (pairSnd st))
/-- The claim. -/
def stCl (st : List Bool) : List Bool := pairSnd (pairSnd (pairSnd st))

@[simp] theorem stFlag_mkSt (f o p c : List Bool) : stFlag (shSt f o p c) = f := by
  simp [stFlag, shSt]
@[simp] theorem stOps_mkSt (f o p c : List Bool) : stOps (shSt f o p c) = o := by simp [stOps, shSt]
@[simp] theorem stPt_mkSt (f o p c : List Bool) : stPt (shSt f o p c) = p := by simp [stPt, shSt]
@[simp] theorem stCl_mkSt (f o p c : List Bool) : stCl (shSt f o p c) = c := by simp [stCl, shSt]

theorem shSt_length (f o p c : List Bool) :
    (shSt f o p c).length = 2 * f.length + 2 * o.length + 2 * p.length + c.length + 6 := by
  rw [shSt, pair_length, pair_length, pair_length]
  omega

theorem shStFn_mem_FP {f o p c : List Bool → List Bool} (hf : f ∈ FP) (ho : o ∈ FP)
    (hp : p ∈ FP) (hc : c ∈ FP) : (fun z => shSt (f z) (o z) (p z) (c z)) ∈ FP :=
  Cobham.pairFn_mem_FP hf (Cobham.pairFn_mem_FP ho (Cobham.pairFn_mem_FP hp hc))

theorem stFlag_mem_FP : stFlag ∈ FP := Cobham.fstBlock_mem_FP
theorem stOps_mem_FP : stOps ∈ FP := comp_fst Cobham.sndBlock_mem_FP
theorem stPt_mem_FP : stPt ∈ FP := comp_fst (comp_snd Cobham.sndBlock_mem_FP)
theorem stCl_mem_FP : stCl ∈ FP := comp_snd (comp_snd Cobham.sndBlock_mem_FP)

/-- Clamp a state to the lengths the input allows. -/
noncomputable def clampSt (x st : List Bool) : List Bool :=
  shSt ((stFlag st).take 1) ((stOps st).take (codesE x).length) ((stPt st).take (pt0 x).length)
    ((stCl st).take (qStr x).length)

theorem clampSt_length (x st : List Bool) :
    (clampSt x st).length ≤ 2 * (codesE x).length + 2 * (pt0 x).length + (qStr x).length + 8 := by
  rw [clampSt, shSt_length]
  have h1 := List.length_take_le 1 (stFlag st)
  have h2 := List.length_take_le (codesE x).length (stOps st)
  have h3 := List.length_take_le (pt0 x).length (stPt st)
  have h4 := List.length_take_le (qStr x).length (stCl st)
  omega

theorem clampStFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => clampSt (a z) (b z)) ∈ FP := by
  have hflag : (fun z => stFlag (b z)) ∈ FP := comp_fst hb
  have hops : (fun z => stOps (b z)) ∈ FP := comp_fst (comp_snd hb)
  have hpt : (fun z => stPt (b z)) ∈ FP := comp_fst (comp_snd (comp_snd hb))
  have hcl : (fun z => stCl (b z)) ∈ FP := comp_snd (comp_snd (comp_snd hb))
  refine shStFn_mem_FP ?_ ?_ ?_ ?_
  · simpa using Cobham.takeLenFn_mem_FP (constFn_mem_FP [false]) hflag
  · exact Cobham.takeLenFn_mem_FP (codesE_comp ha) hops
  · exact Cobham.takeLenFn_mem_FP (pt0_comp ha) hpt
  · exact Cobham.takeLenFn_mem_FP (qStr_comp ha) hcl

/-! ## The round -/

/-- The variable of the head operator, in unary, on `pair st ops` (the state supplies the length
the unary conversion is clamped by). -/
noncomputable def headVarU (st ops : List Bool) : List Bool :=
  unaryVal clampPoly (pair st (decOne (sndEnc (posAt ops 0))))

theorem headVarU_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => headVarU (a z) (b z)) ∈ FP := by
  have hhead : (fun z => posAt (b z) 0) ∈ FP := by simpa using posAt_mem_FP (constFn_mem_FP []) hb
  have hbits : (fun z => decOne (sndEnc (posAt (b z) 0))) ∈ FP := by
    have := mem_FP_comp (sndEnc_mem_FP hhead) decOne_mem_FP
    simpa only [Function.comp_def] using this
  have := mem_FP_comp (Cobham.pairFn_mem_FP ha hbits) (unaryVal_mem_FP clampPoly)
  simpa only [Function.comp_def] using this

/-- A mark when the `j`-th block of the message is not below the modulus, on
`pair (pair q msg) (unary j)`. -/
noncomputable def badBlock (z : List Bool) : List Bool :=
  let q := pairFst (pairFst z)
  let msg := pairSnd (pairFst z)
  let blk := wBlock msg (mulLen (pairSnd z) q).length q.length
  selectHead (ltFlag blk q) [] [true]

theorem badBlock_mem_FP : badBlock ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hX := comp_fst hid
  have hq := comp_fst hX
  have hmsg := comp_snd hX
  have hj := comp_snd hid
  exact Cobham.selectHeadFn_mem_FP
    (ltFlagFn_mem_FP (wBlock_mem_FP hmsg (mulLen_mem_FP hj hq) hq) hq)
    (constFn_mem_FP _) (constFn_mem_FP _)

/-- Every block of the message is below the modulus. -/
noncomputable def blocksOK (q msg : List Bool) : List Bool :=
  emptyFlag (countOver badBlock (pair (divFn2 (pair q msg)) (pair q msg)))

theorem blocksOK_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => blocksOK (a z) (b z)) ∈ FP := by
  have hpair : (fun z => pair (a z) (b z)) ∈ FP := Cobham.pairFn_mem_FP ha hb
  have hdiv : (fun z => divFn2 (pair (a z) (b z))) ∈ FP := by
    have h := mem_FP_comp hpair divFn2_mem_FP
    simpa only [Function.comp_def] using h
  have hcount : (fun z => countOver badBlock (pair (divFn2 (pair (a z) (b z)))
      (pair (a z) (b z)))) ∈ FP := by
    have h := mem_FP_comp (Cobham.pairFn_mem_FP hdiv hpair) (countOver_mem_FP badBlock_mem_FP)
    simpa only [Function.comp_def] using h
  exact emptyFlagFn_mem_FP hcount

/-- One round on the state `st`, with the prover's coefficient string `msg` and the coin block
`coin`; the identity (up to clamping) once the schedule is exhausted. -/
noncomputable def roundStep (x st msg coin : List Bool) : List Bool :=
  let q := qStr x
  let ops := stOps st
  let pt := stPt st
  let iU := headVarU st ops
  let av := wBlock pt (mulLen iU q).length q.length
  let degOK := andBit (lenEqFlag msg (mulLen (DU x ++ [true]) q)) (blocksOK q msg)
  let chk := eqFlag (opCheckVal q (decOne (fstEnc (posAt ops 0))) av msg) (stCl st)
  let t := reduceMod q coin
  selectHead (emptyFlag (posCount ops)) (clampSt x st)
    (clampSt x (shSt (andBit (stFlag st) (andBit degOK chk)) (dropChild ops)
      (replaceBlock pt q iU t) (hornerEval q t msg)))

theorem lenEqFlagFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => lenEqFlag (a z) (b z)) ∈ FP :=
  binFn_mem_FP (g := lenEqFlag) (Cobham.lenEqFlag_mem (Cobham.proj 0) (Cobham.proj 1)) ha hb

theorem roundStepFn_mem_FP {x st msg coin : List Bool → List Bool} (hx : x ∈ FP)
    (hst : st ∈ FP) (hmsg : msg ∈ FP) (hcoin : coin ∈ FP) :
    (fun z => roundStep (x z) (st z) (msg z) (coin z)) ∈ FP := by
  have hq : (fun z => qStr (x z)) ∈ FP := qStr_comp hx
  have hops : (fun z => stOps (st z)) ∈ FP := comp_fst (comp_snd hst)
  have hpt : (fun z => stPt (st z)) ∈ FP := comp_fst (comp_snd (comp_snd hst))
  have hcl : (fun z => stCl (st z)) ∈ FP := comp_snd (comp_snd (comp_snd hst))
  have hflag : (fun z => stFlag (st z)) ∈ FP := comp_fst hst
  have hiU : (fun z => headVarU (st z) (stOps (st z))) ∈ FP := headVarU_mem_FP hst hops
  have hav : (fun z => wBlock (stPt (st z))
      (mulLen (headVarU (st z) (stOps (st z))) (qStr (x z))).length (qStr (x z)).length) ∈ FP :=
    wBlock_mem_FP hpt (mulLen_mem_FP hiU hq) hq
  have hDU : (fun z => DU (x z) ++ [true]) ∈ FP :=
    Cobham.appendFn_mem_FP (DU_comp hx) (constFn_mem_FP _)
  have hdeg : (fun z => andBit (lenEqFlag (msg z) (mulLen (DU (x z) ++ [true]) (qStr (x z))))
      (blocksOK (qStr (x z)) (msg z))) ∈ FP :=
    andBitFn_mem_FP (lenEqFlagFn_mem_FP hmsg (mulLen_mem_FP hDU hq)) (blocksOK_mem_FP hq hmsg)
  have hhead : (fun z => posAt (stOps (st z)) 0) ∈ FP := by
    simpa using posAt_mem_FP (constFn_mem_FP []) hops
  have hkind : (fun z => decOne (fstEnc (posAt (stOps (st z)) 0))) ∈ FP := by
    have h := mem_FP_comp (fstEnc_mem_FP hhead) decOne_mem_FP
    simpa only [Function.comp_def] using h
  have hchk : (fun z => eqFlag (opCheckVal (qStr (x z)) (decOne (fstEnc (posAt (stOps (st z)) 0)))
      (wBlock (stPt (st z)) (mulLen (headVarU (st z) (stOps (st z))) (qStr (x z))).length
        (qStr (x z)).length) (msg z)) (stCl (st z))) ∈ FP :=
    eqFlagFn_mem_FP (opCheckVal_mem_FP hq hkind hav hmsg) hcl
  have ht : (fun z => reduceMod (qStr (x z)) (coin z)) ∈ FP := reduceMod_mem_FP hq hcoin
  have hnew : (fun z => shSt (andBit (stFlag (st z)) (andBit
      (andBit (lenEqFlag (msg z) (mulLen (DU (x z) ++ [true]) (qStr (x z))))
        (blocksOK (qStr (x z)) (msg z)))
      (eqFlag (opCheckVal (qStr (x z)) (decOne (fstEnc (posAt (stOps (st z)) 0)))
        (wBlock (stPt (st z)) (mulLen (headVarU (st z) (stOps (st z))) (qStr (x z))).length
          (qStr (x z)).length) (msg z)) (stCl (st z)))))
      (dropChild (stOps (st z)))
      (replaceBlock (stPt (st z)) (qStr (x z)) (headVarU (st z) (stOps (st z)))
        (reduceMod (qStr (x z)) (coin z)))
      (hornerEval (qStr (x z)) (reduceMod (qStr (x z)) (coin z)) (msg z))) ∈ FP :=
    shStFn_mem_FP (andBitFn_mem_FP hflag (andBitFn_mem_FP hdeg hchk)) (dropChild_mem_FP hops)
      (replaceBlock_mem_FP hpt hq hiU ht) (hornerEvalFn_mem_FP hq ht hmsg)
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP (posCount_mem_FP hops))
    (clampStFn_mem_FP hx hst) (clampStFn_mem_FP hx hnew)

theorem roundStep_length_le (x st msg coin : List Bool) :
    (roundStep x st msg coin).length
      ≤ 2 * (codesE x).length + 2 * (pt0 x).length + (qStr x).length + 8 := by
  simp only [roundStep]
  refine le_trans (selectHead_length_le _ _ _) (max_le (clampSt_length _ _) (clampSt_length _ _))

/-! ## Rounds on a view -/

/-- The initial state: the well-formedness flag, the schedule, the zero point and the claim
`1`. -/
noncomputable def st0 (x : List Bool) : List Bool := shSt (wfFlag x) (codesE x) (pt0 x) (cl0 x)

theorem st0_mem_FP : st0 ∈ FP :=
  shStFn_mem_FP wfFlag_mem_FP codesE_mem_FP pt0_mem_FP cl0_mem_FP

theorem st0_length (x : List Bool) :
    (st0 x).length ≤ 2 * (codesE x).length + 2 * (pt0 x).length + (cl0 x).length + 8 := by
  rw [st0, shSt_length]
  have : (wfFlag x).length = 1 := by
    rcases wfFlag_flag x with h | h <;> rw [h] <;> rfl
  omega

/-- The width of a coin block, as a unary ruler from a polynomial. -/
noncomputable def coinWidth (Wp : Polynomial ℕ) (x : List Bool) : List Bool := polyRuler Wp x

/-- The last verifier state recorded in the encoded transcript `e` of `2 k` messages, and the
prover's last message: positions `2 (k - 1)` and `2 k - 1`. -/
noncomputable def prevSt (e : List Bool) : List Bool :=
  decOne (posAt e (mulC 2 (dropOne (divC 2 (posCount e)))).length)

/-- The prover's last message. -/
noncomputable def lastMsg (e : List Bool) : List Bool :=
  decOne (posAt e (dropOne (mulC 2 (divC 2 (posCount e)))).length)

theorem prevSt_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => prevSt (a z)) ∈ FP := by
  have hidx : (fun z => mulC 2 (dropOne (divC 2 (posCount (a z))))) ∈ FP :=
    mulC_mem_FP (dropOneFn_mem_FP (divC_mem_FP (posCount_mem_FP ha) 2)) 2
  have h := mem_FP_comp (posAt_mem_FP hidx ha) decOne_mem_FP
  simpa only [Function.comp_def] using h

theorem lastMsg_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => lastMsg (a z)) ∈ FP := by
  have hidx : (fun z => dropOne (mulC 2 (divC 2 (posCount (a z))))) ∈ FP :=
    dropOneFn_mem_FP (mulC_mem_FP (divC_mem_FP (posCount_mem_FP ha) 2) 2)
  have h := mem_FP_comp (posAt_mem_FP hidx ha) decOne_mem_FP
  simpa only [Function.comp_def] using h

/-- The coin block of the current round: block `k - 1` of width `Wp |x|`, cut to the modulus
width. -/
noncomputable def roundCoin (Wp : Polynomial ℕ) (x r e : List Bool) : List Bool :=
  wBlock r (mulLen (dropOne (divC 2 (posCount e))) (coinWidth Wp x)).length (qStr x).length

theorem roundCoin_mem_FP (Wp : Polynomial ℕ) {x r e : List Bool → List Bool} (hx : x ∈ FP)
    (hr : r ∈ FP) (he : e ∈ FP) : (fun z => roundCoin Wp (x z) (r z) (e z)) ∈ FP :=
  wBlock_mem_FP hr (mulLen_mem_FP (dropOneFn_mem_FP (divC_mem_FP (posCount_mem_FP he) 2))
    (polyRulerFn_mem_FP Wp hx)) (qStr_comp hx)

/-- The message the verifier sends on the view `z`: the initial state at round `0`, and
otherwise the round on the state and prover message read off the transcript, with the round's
coin block. The round index is half the transcript length. -/
noncomputable def shenVmsg (Wp : Polynomial ℕ) (z : List Bool) : List Bool :=
  selectHead (emptyFlag (divC 2 (posCount (RepArgs.ve z)))) (st0 (RepArgs.vx z))
    (roundStep (RepArgs.vx z) (prevSt (RepArgs.ve z)) (lastMsg (RepArgs.ve z))
      (roundCoin Wp (RepArgs.vx z) (RepArgs.vr z) (RepArgs.ve z)))

theorem shenVmsg_mem_FP (Wp : Polynomial ℕ) : shenVmsg Wp ∈ FP := by
  have hx := RepArgs.vx_mem_FP
  have hr := RepArgs.vr_mem_FP
  have he := RepArgs.ve_mem_FP
  have hst0 : (fun z => st0 (RepArgs.vx z)) ∈ FP := by
    have h := mem_FP_comp hx st0_mem_FP
    simpa only [Function.comp_def] using h
  exact Cobham.selectHeadFn_mem_FP (emptyFlagFn_mem_FP (divC_mem_FP (posCount_mem_FP he) 2)) hst0
    (roundStepFn_mem_FP hx (prevSt_mem_FP he) (lastMsg_mem_FP he) (roundCoin_mem_FP Wp hx hr he))

/-- **The message-length bound**, in terms of the input's parameters. -/
theorem shenVmsg_length_le (Wp : Polynomial ℕ) (z : List Bool) :
    (shenVmsg Wp z).length
      ≤ 2 * (codesE (RepArgs.vx z)).length + 2 * (pt0 (RepArgs.vx z)).length
        + (qStr (RepArgs.vx z)).length + (cl0 (RepArgs.vx z)).length + 8 := by
  rw [shenVmsg]
  refine le_trans (selectHead_length_le _ _ _) (max_le ?_ ?_)
  · have := st0_length (RepArgs.vx z)
    omega
  · have := roundStep_length_le (RepArgs.vx z) (prevSt (RepArgs.ve z)) (lastMsg (RepArgs.ve z))
      (roundCoin Wp (RepArgs.vx z) (RepArgs.vr z) (RepArgs.ve z))
    omega

/-! ## The verdict -/

/-- The last state: position `2 k - 2` of a transcript of `2 k` messages. -/
noncomputable def lastSt (e : List Bool) : List Bool :=
  decOne (posAt e (dropOne (dropOne (mulC 2 (divC 2 (posCount e))))).length)

theorem lastSt_mem_FP {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => lastSt (a z)) ∈ FP := by
  have hidx : (fun z => dropOne (dropOne (mulC 2 (divC 2 (posCount (a z)))))) ∈ FP :=
    dropOneFn_mem_FP (dropOneFn_mem_FP (mulC_mem_FP (divC_mem_FP (posCount_mem_FP ha) 2) 2))
  have h := mem_FP_comp (posAt_mem_FP hidx ha) decOne_mem_FP
  simpa only [Function.comp_def] using h

/-- The verdict flag on a view: the flag is up, the schedule is exhausted, and the claim is the
matrix's value at the point. -/
noncomputable def shenVerdictFn (z : List Bool) : List Bool :=
  let x := RepArgs.vx z
  let st := lastSt (RepArgs.ve z)
  andBit (eqFlag (stFlag st) [true])
    (andBit (emptyFlag (posCount (stOps st)))
      (eqFlag (stCl st) (cnfEval (qStr x) (stPt st) (φE x))))

theorem shenVerdictFn_mem_FP : shenVerdictFn ∈ FP := by
  have hx := RepArgs.vx_mem_FP
  have he := RepArgs.ve_mem_FP
  have hst : (fun z => lastSt (RepArgs.ve z)) ∈ FP := lastSt_mem_FP he
  have hflag : (fun z => stFlag (lastSt (RepArgs.ve z))) ∈ FP := comp_fst hst
  have hops : (fun z => stOps (lastSt (RepArgs.ve z))) ∈ FP := comp_fst (comp_snd hst)
  have hpt : (fun z => stPt (lastSt (RepArgs.ve z))) ∈ FP := comp_fst (comp_snd (comp_snd hst))
  have hcl : (fun z => stCl (lastSt (RepArgs.ve z))) ∈ FP := comp_snd (comp_snd (comp_snd hst))
  exact andBitFn_mem_FP (eqFlagFn_mem_FP hflag (constFn_mem_FP _))
    (andBitFn_mem_FP (emptyFlagFn_mem_FP (posCount_mem_FP hops))
      (eqFlagFn_mem_FP hcl (cnfEvalFn_mem_FP (qStr_comp hx) hpt (φE_comp hx))))

/-- The verdict language. -/
def shenVerdict : Language := {z | ∃ b ∈ shenVerdictFn z, b = true}

theorem shenVerdict_mem_P : shenVerdict ∈ P :=
  mem_P_of_decisionFn shenVerdictFn_mem_FP fun _ => Iff.rfl

theorem shenVerdictFn_flag (z : List Bool) :
    shenVerdictFn z = [true] ∨ shenVerdictFn z = [false] := by
  simp only [shenVerdictFn]
  exact andBit_flag _ _

theorem mem_shenVerdict_iff (z : List Bool) : z ∈ shenVerdict ↔ shenVerdictFn z = [true] := by
  rw [shenVerdict, Set.mem_setOf_eq]
  rcases shenVerdictFn_flag z with h | h <;> simp [h]

end Complexity
