/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive
public import Complexitylib.Classes.PH.SigmaOne
public import Complexitylib.Classes.Containments.Internal.TranscriptEnc
public import Complexitylib.Classes.Containments.IPSubsetPSPACE
public import Complexitylib.Classes.Containments.PSPACESubsetEXP
public import Complexitylib.Classes.PCP.Internal.PosScan

/-!
# `NP ⊆ MA`, `MA ⊆ IP`, `AM ⊆ IP` and `IP ⊆ EXP`

⚠️ Unreviewed by Bolton

`NP ⊆ MA`: by `SigmaP_one_eq_NP` an `NP` language is a bounded existential
over a `P` language, so Merlin sends the certificate and Arthur ignores his
coins.

`MA ⊆ IP`: a Merlin–Arthur verifier is a one-round protocol whose verifier
message is empty. The only work is that the interactive verifier receives the
transcript *encoded* (`DataEncode.bitstringEncode`), so Merlin's message has to
be decoded again in polynomial time: `decMsg` is a scan reading the per-bit
encodings of `Complexity.encBit` off the front of the string.

`AM ⊆ IP`: an Arthur–Merlin verifier is a one-round protocol whose verifier
message is its coins, and Merlin's reply is decoded from its own serialization
by `decOne`.

## Main definitions

- `decStep`, `decStepP`, `decMsg`, `decOne` — the decoding scan and its packed form
- `maProtocol`, `amProtocol` — the one-round protocols of `MA` and `AM` verifiers

## Main results

- `decMsg_encode`, `decOne_encode` — the decoders invert the encodings
- `NP_subset_MA`, `MA_subset_IP`, `NP_subset_IP`, `AM_subset_IP`, `IP_subset_EXP`
-/

@[expose] public section

namespace Complexity

open Cobham

/-! ## Decoding one message -/

/-- One step of the decoding scan: read one encoded bit off the front of the
remaining string and append the bit to the accumulator. Anything else is left
alone. -/
def decStep : List Bool × List Bool → List Bool × List Bool
  | (acc, false :: true :: t) => (acc ++ [false], t)
  | (acc, false :: false :: true :: true :: t) => (acc ++ [true], t)
  | (acc, rest) => (acc, rest)

theorem decStep_encBit (acc : List Bool) (b : Bool) (t : List Bool) :
    decStep (acc, encBit b ++ t) = (acc ++ [b], t) := by
  cases b <;> rfl

@[simp] theorem decStep_true_true (acc : List Bool) :
    decStep (acc, [true, true]) = (acc, [true, true]) := rfl

/-- **The scan reads back the message.** -/
theorem decStep_iterate_run (acc v s : List Bool) :
    decStep^[v.length] (acc, (v.map encBit).flatten ++ s) = (acc ++ v, s) := by
  induction v generalizing acc with
  | nil => simp
  | cons b t ih =>
      rw [List.length_cons, Function.iterate_succ_apply, List.map_cons, List.flatten_cons,
        List.append_assoc, decStep_encBit, ih]
      simp

theorem decStep_iterate_true_true (acc : List Bool) (n : ℕ) :
    decStep^[n] (acc, [true, true]) = (acc, [true, true]) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, decStep_true_true, ih]

theorem decStep_length (acc rest : List Bool) :
    (decStep (acc, rest)).1.length + (decStep (acc, rest)).2.length
      ≤ acc.length + rest.length := by
  rcases rest with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, t⟩⟩⟩⟩ <;>
    simp [decStep] <;> omega

theorem decStep_iterate_length (acc rest : List Bool) (n : ℕ) :
    (decStep^[n] (acc, rest)).1.length + (decStep^[n] (acc, rest)).2.length
      ≤ acc.length + rest.length := by
  induction n generalizing acc rest with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact le_trans (ih _ _) (decStep_length acc rest)

/-! ## The packed scan -/

theorem eqFlag_eq_ite (a b : List Bool) : eqFlag a b = if a = b then [true] else [false] := by
  split_ifs with h
  · exact (eqFlag_eq_true_iff a b).mpr h
  · rcases eqFlag_flag a b with h' | h'
    · exact absurd ((eqFlag_eq_true_iff a b).mp h') h
    · exact h'

/-- One step of the packed scan, on `pair acc rest`. -/
def decStepP (z : List Bool) : List Bool :=
  selectHead (eqFlag ((pairSnd z).take 2) [false, true])
    (pair (pairFst z ++ [false]) ((pairSnd z).drop 2))
    (selectHead (eqFlag ((pairSnd z).take 4) [false, false, true, true])
      (pair (pairFst z ++ [true]) ((pairSnd z).drop 4)) z)

theorem decStepP_pack (acc rest : List Bool) :
    decStepP (pair acc rest) = pair (decStep (acc, rest)).1 (decStep (acc, rest)).2 := by
  rw [decStepP]
  simp only [pairFst_pair, pairSnd_pair]
  rcases rest with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, t⟩⟩⟩⟩ <;>
    simp [decStep, eqFlag_eq_ite, selectHead]

theorem decStepP_iterate (acc rest : List Bool) (n : ℕ) :
    decStepP^[n] (pair acc rest)
      = pair (decStep^[n] (acc, rest)).1 (decStep^[n] (acc, rest)).2 := by
  induction n generalizing acc rest with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, decStepP_pack, ih, Function.iterate_succ_apply]

theorem decStepP_mem_FP : decStepP ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfst : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
  have hsnd : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
  have htwo : (fun _ : List Bool => ([false, false] : List Bool)) ∈ FP :=
    constFn_mem_FP [false, false]
  have hfour : (fun _ : List Bool => ([false, false, false, false] : List Bool)) ∈ FP :=
    constFn_mem_FP [false, false, false, false]
  have htake2 : (fun z => (pairSnd z).take 2) ∈ FP := by
    simpa using Cobham.takeLenFn_mem_FP htwo hsnd
  have htake4 : (fun z => (pairSnd z).take 4) ∈ FP := by
    simpa using Cobham.takeLenFn_mem_FP hfour hsnd
  have hdrop2 : (fun z => (pairSnd z).drop 2) ∈ FP := by
    simpa using dropLenFn_mem_FP htwo hsnd
  have hdrop4 : (fun z => (pairSnd z).drop 4) ∈ FP := by
    simpa using dropLenFn_mem_FP hfour hsnd
  exact Cobham.selectHeadFn_mem_FP (eqFlagFn_mem_FP htake2 (constFn_mem_FP [false, true]))
    (Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hfst (constFn_mem_FP [false])) hdrop2)
    (Cobham.selectHeadFn_mem_FP
      (eqFlagFn_mem_FP htake4 (constFn_mem_FP [false, false, true, true]))
      (Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hfst (constFn_mem_FP [true])) hdrop4) hid)

/-- Decode Merlin's message from the encoding of the one-round transcript
`[[], w]`: skip the four bits of the outer bracket and the empty verifier
message, then run the scan for as many steps as the string is long. -/
def decMsg (s : List Bool) : List Bool :=
  pairFst (decStepP^[s.length] (pair [] (s.drop 4)))

theorem decMsg_mem_FP : decMsg ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hfour : (fun _ : List Bool => ([false, false, false, false] : List Bool)) ∈ FP :=
    constFn_mem_FP [false, false, false, false]
  have hdrop4 : (fun z : List Bool => z.drop 4) ∈ FP := by
    simpa using dropLenFn_mem_FP hfour hid
  have hinit : (fun z : List Bool => pair [] (z.drop 4)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) hdrop4
  have hwidth : (fun z : List Bool => pair (z ++ z) z) ∈ FP :=
    Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hid hid) hid
  have hbound : ∀ z : List Bool, ∀ n ≤ z.length,
      (decStepP^[n] (pair [] (z.drop 4))).length ≤ (pair (z ++ z) z).length := by
    intro z n _
    rw [decStepP_iterate, pair_length, pair_length]
    have := decStep_iterate_length [] (z.drop 4) n
    simp only [List.length_nil, List.length_append, List.length_drop] at this ⊢
    omega
  have h := Cobham.iterate_mem_FP decStepP_mem_FP hinit hid hwidth hbound
  have h1 := mem_FP_comp h Cobham.fstBlock_mem_FP
  simpa [Function.comp, decMsg] using h1

/-- A message is no longer than its flattened per-bit encoding. -/
theorem length_le_flatten_encBit (v : List Bool) :
    v.length ≤ ((v.map encBit).flatten).length := by
  induction v with
  | nil => simp
  | cons b t ih =>
      rw [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have hb : 1 ≤ (encBit b).length := by cases b <;> simp [encBit]
      omega

/-- **The decoder inverts the encoding** of a one-round transcript with an
empty verifier message. -/
theorem decMsg_encode (w : List Bool) :
    decMsg (DataEncode.bitstringEncode ([[], w] : Transcript)) = w := by
  rw [decMsg, bitstringEncode_transcript]
  set F := (w.map encBit).flatten with hF
  have hbody : encBody [[], w] = [false, true] ++ (false :: (F ++ [true])) := by
    simp [encBody, encMsg, hF]
  rw [hbody]
  have hdrop : (false :: ([false, true] ++ (false :: (F ++ [true])) ++ [true])).drop 4
      = F ++ [true, true] := by
    simp
  rw [hdrop]
  have hlen : w.length
      ≤ (false :: ([false, true] ++ (false :: (F ++ [true])) ++ [true])).length := by
    have := length_le_flatten_encBit w
    rw [← hF] at this
    simp only [List.length_cons, List.length_append]
    omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hlen
  rw [hm, add_comm, Function.iterate_add_apply, decStepP_iterate, decStep_iterate_run,
    List.nil_append, decStepP_iterate, decStep_iterate_true_true, pairFst_pair]

/-- Decode a message from its own serialization `false :: flat ++ [true]`: skip the opening
bracket and run the scan for as many steps as the string is long. -/
def decOne (s : List Bool) : List Bool :=
  pairFst (decStepP^[s.length] (pair [] (s.drop 1)))

theorem decOne_mem_FP : decOne ∈ FP := by
  have hid : (fun z : List Bool => z) ∈ FP := CobhamFP_subset_FP (Cobham.proj 0)
  have hone : (fun _ : List Bool => ([false] : List Bool)) ∈ FP := constFn_mem_FP [false]
  have hdrop1 : (fun z : List Bool => z.drop 1) ∈ FP := by
    simpa using dropLenFn_mem_FP hone hid
  have hinit : (fun z : List Bool => pair [] (z.drop 1)) ∈ FP :=
    Cobham.pairFn_mem_FP (constFn_mem_FP []) hdrop1
  have hwidth : (fun z : List Bool => pair (z ++ z) z) ∈ FP :=
    Cobham.pairFn_mem_FP (Cobham.appendFn_mem_FP hid hid) hid
  have hbound : ∀ z : List Bool, ∀ n ≤ z.length,
      (decStepP^[n] (pair [] (z.drop 1))).length ≤ (pair (z ++ z) z).length := by
    intro z n _
    rw [decStepP_iterate, pair_length, pair_length]
    have := decStep_iterate_length [] (z.drop 1) n
    simp only [List.length_nil, List.length_append, List.length_drop] at this ⊢
    omega
  have h := Cobham.iterate_mem_FP decStepP_mem_FP hinit hid hwidth hbound
  exact mem_FP_comp h Cobham.fstBlock_mem_FP

@[simp] theorem decStep_true (acc : List Bool) : decStep (acc, [true]) = (acc, [true]) := rfl

theorem decStep_iterate_true (acc : List Bool) (n : ℕ) :
    decStep^[n] (acc, [true]) = (acc, [true]) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, decStep_true, ih]

/-- **`decOne` inverts the encoding of a message.** -/
theorem decOne_encode (w : List Bool) : decOne (DataEncode.bitstringEncode w) = w := by
  rw [decOne, DataEncode.bitstringEncode_def, encMsg_eq, encMsg]
  set F := (w.map encBit).flatten with hF
  have hL : (false :: (F ++ [true])).length = F.length + 2 := by simp
  rw [hL, List.drop_succ_cons, List.drop_zero]
  have hlen : w.length ≤ F.length + 2 := by
    have := length_le_flatten_encBit w
    rw [← hF] at this
    omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hlen
  rw [hm, add_comm, Function.iterate_add_apply, decStepP_iterate, decStep_iterate_run,
    List.nil_append, decStepP_iterate, decStep_iterate_true, pairFst_pair]

/-! ## `NP ⊆ MA` -/

/-- **`NP ⊆ MA`.** Merlin sends the certificate of `SigmaP_one_eq_NP`; Arthur
ignores his coins. -/
theorem NP_subset_MA : NP ⊆ MA := by
  intro L hL
  obtain ⟨p, L', hL', rfl⟩ := NP_subset_polyExistsClass_P hL
  refine ⟨p, pairFst ⁻¹' L', mem_P_preimage pairFst_mem_FP hL', ?_, ?_⟩
  · rintro x ⟨w, hw, hmem⟩
    refine ⟨w, hw, ?_⟩
    have hev : merlinEvent (pairFst ⁻¹' L') (p.eval x.length) x w = Finset.univ := by
      ext r
      simp [merlinEvent, hmem]
    rw [hev, eventProb_univ]
    norm_num
  · intro x hx w hw
    have hev : merlinEvent (pairFst ⁻¹' L') (p.eval x.length) x w = ∅ := by
      ext r
      simp only [merlinEvent, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage,
        pairFst_pair, Finset.notMem_empty, iff_false]
      exact fun h => hx ⟨w, hw, h⟩
    rw [hev, eventProb_empty]
    norm_num

/-! ## `MA ⊆ IP` -/

/-- The one-round protocol of an `MA` verifier: the verifier says nothing,
Merlin answers, and the verdict decodes Merlin's message and runs the `MA`
verifier on it. -/
noncomputable def maProtocol (p : Polynomial ℕ) (V : Language) (hV : V ∈ P) : Protocol where
  rounds _ := 1
  coins n := p.eval n
  msgLen n := p.eval n
  vmsg _ := []
  vmsg_mem := constFn_mem_FP []
  vmsg_len := by intros; simp
  verdict := (fun z => pair (pair (pairFst (pairFst z)) (decMsg (pairSnd z)))
    (pairSnd (pairFst z))) ⁻¹' V
  verdict_mem := by
    refine mem_P_preimage ?_ hV
    have hfst : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
    have hsnd : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
    have h1 : (fun z : List Bool => pairFst (pairFst z)) ∈ FP := mem_FP_comp hfst hfst
    have h2 : (fun z : List Bool => decMsg (pairSnd z)) ∈ FP :=
      mem_FP_comp (g := decMsg) hsnd decMsg_mem_FP
    have h3 : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP := mem_FP_comp hfst hsnd
    exact Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP h1 h2) h3

theorem maProtocol_transcript (p : Polynomial ℕ) (V : Language) (hV : V ∈ P)
    (S : ProverStrategy) (x r : List Bool) :
    (maProtocol p V hV).transcript S x r 1 = [[], S [[]]] := by
  simp [Protocol.transcript, maProtocol]

/-- The accepting coins of the one-round protocol are the accepting coins of
the `MA` verifier on Merlin's opening message. -/
theorem maProtocol_acceptEvent (p : Polynomial ℕ) (V : Language) (hV : V ∈ P)
    (S : ProverStrategy) (x : List Bool) :
    (maProtocol p V hV).acceptEvent S x = merlinEvent V (p.eval x.length) x (S [[]]) := by
  simp only [Protocol.acceptEvent, merlinEvent]
  congr 1
  funext r
  apply propext
  show Protocol.view x _ ((maProtocol p V hV).transcript S _ _ 1) ∈ _ ↔ _
  rw [maProtocol_transcript]
  simp only [maProtocol, Protocol.view, protocolView, Set.mem_preimage, pairFst_pair,
    pairSnd_pair, decMsg_encode]

/-- **`MA ⊆ IP`.** -/
theorem MA_subset_IP : MA ⊆ IP := by
  rintro L ⟨p, V, hV, hyes, hno⟩
  refine ⟨maProtocol p V hV, 1, p, p, fun n => by simp [maProtocol], fun n => rfl, fun n => rfl,
    ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw, hprob⟩ := hyes x hx
    refine ⟨fun _ => w, fun _ => hw, ?_⟩
    rw [maProtocol_acceptEvent]
    exact hprob
  · intro x hx S hS
    rw [maProtocol_acceptEvent]
    exact hno x hx (S [[]]) (hS _)

/-- **`NP ⊆ IP`.** -/
theorem NP_subset_IP : NP ⊆ IP := NP_subset_MA.trans MA_subset_IP

/-! ## `AM ⊆ IP` -/

/-- The one-round protocol of an `AM` verifier: the verifier sends its coins, Merlin answers,
and the verdict decodes Merlin's message and runs the `AM` verifier on it. The coins are
truncated to the coin count so that the message bound holds on every input. -/
noncomputable def amProtocol (p : Polynomial ℕ) (V : Language) (hV : V ∈ P) : Protocol where
  rounds _ := 1
  coins n := p.eval n
  msgLen n := p.eval n
  vmsg z := (pairSnd (pairFst z)).take (polyRuler p (pairFst (pairFst z))).length
  vmsg_mem := by
    have hfst : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
    have hsnd : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
    have hx : (fun z : List Bool => pairFst (pairFst z)) ∈ FP := mem_FP_comp hfst hfst
    have hr : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP := mem_FP_comp hfst hsnd
    exact Cobham.takeLenFn_mem_FP (polyRulerFn_mem_FP p hx) hr
  vmsg_len := by
    intro x r τ
    simp only [protocolView, pairFst_pair, pairSnd_pair, List.length_take, polyRuler_length]
    exact min_le_left _ _
  verdict := (fun z => pair (pair (pairFst (pairFst z)) (pairSnd (pairFst z)))
    (decOne (posAt (pairSnd z) 1))) ⁻¹' V
  verdict_mem := by
    refine mem_P_preimage ?_ hV
    have hfst : (fun z : List Bool => pairFst z) ∈ FP := Cobham.fstBlock_mem_FP
    have hsnd : (fun z : List Bool => pairSnd z) ∈ FP := Cobham.sndBlock_mem_FP
    have h1 : (fun z : List Bool => pairFst (pairFst z)) ∈ FP := mem_FP_comp hfst hfst
    have h2 : (fun z : List Bool => pairSnd (pairFst z)) ∈ FP := mem_FP_comp hfst hsnd
    have hpos : (fun z : List Bool => posAt (pairSnd z) 1) ∈ FP := by
      simpa using posAt_mem_FP (constFn_mem_FP [true]) hsnd
    have h3 : (fun z : List Bool => decOne (posAt (pairSnd z) 1)) ∈ FP :=
      mem_FP_comp (g := decOne) hpos decOne_mem_FP
    exact Cobham.pairFn_mem_FP (Cobham.pairFn_mem_FP h1 h2) h3

theorem amProtocol_transcript (p : Polynomial ℕ) (V : Language) (hV : V ∈ P)
    (S : ProverStrategy) (x r : List Bool) (hr : r.length = p.eval x.length) :
    (amProtocol p V hV).transcript S x r 1 = [r, S [r]] := by
  simp only [Protocol.transcript, amProtocol, Protocol.view, protocolView, pairFst_pair,
    pairSnd_pair, polyRuler_length, List.nil_append]
  rw [List.take_of_length_le (by rw [hr])]

open Classical in
/-- The accepting coins of the one-round protocol against `S`: those on which the `AM`
verifier accepts Merlin's reply to the coins. -/
theorem amProtocol_acceptEvent (p : Polynomial ℕ) (V : Language) (hV : V ∈ P)
    (S : ProverStrategy) (x : List Bool) :
    (amProtocol p V hV).acceptEvent S x
      = Finset.univ.filter fun r : Fin (p.eval x.length) → Bool =>
          pair (pair x (BitString.toList r)) (S [BitString.toList r]) ∈ V := by
  simp only [Protocol.acceptEvent]
  congr 1
  funext r
  apply propext
  show Protocol.view x _ ((amProtocol p V hV).transcript S _ _ 1) ∈ _ ↔ _
  rw [amProtocol_transcript p V hV S x _ (BitString.length_toList r)]
  simp only [amProtocol, Protocol.view, protocolView, Set.mem_preimage, pairFst_pair,
    pairSnd_pair]
  erw [posAt_eq_of_lt (l := [BitString.toList r, S [BitString.toList r]]) (i := 1) (by simp),
    decOne_encode]
  rfl

open Classical in
/-- **`AM ⊆ IP`.** -/
theorem AM_subset_IP : AM ⊆ IP := by
  rintro L ⟨p, V, hV, hyes, hno⟩
  refine ⟨amProtocol p V hV, 1, p, p, fun n => by simp [amProtocol], fun n => rfl, fun n => rfl,
    ?_, ?_⟩
  · intro x hx
    refine ⟨fun τ =>
      if h : ∃ w : List Bool, w.length ≤ p.eval x.length ∧ pair (pair x (τ.headD [])) w ∈ V
        then Classical.choose h else [], fun τ => ?_, ?_⟩
    · dsimp only
      split_ifs with h
      · exact (Classical.choose_spec h).1
      · simp
    · rw [amProtocol_acceptEvent]
      refine le_trans (hyes x hx) (le_of_eq ?_)
      congr 1
      ext r
      simp only [arthurEvent, Finset.mem_filter, Finset.mem_univ, true_and, List.headD_cons]
      constructor
      · intro h
        rw [dif_pos h]
        exact (Classical.choose_spec h).2
      · intro h
        by_cases h' : ∃ w : List Bool, w.length ≤ p.eval x.length ∧
            pair (pair x (BitString.toList r)) w ∈ V
        · exact h'
        · rw [dif_neg h'] at h
          exact ⟨[], by simp, h⟩
  · intro x hx S hS
    rw [amProtocol_acceptEvent]
    refine le_trans (eventProb_mono ?_) (hno x hx)
    intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S [BitString.toList r], hS _, hr'⟩

/-- **`IP ⊆ EXP`**, through `PSPACE`. -/
theorem IP_subset_EXP : IP ⊆ EXP := IP_subset_PSPACE.trans PSPACE_subset_EXP

end Complexity
