/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Subroutines.BinaryAdd
import Complexitylib.Models.TuringMachine.Subroutines.BinaryCopy.Defs
import Complexitylib.Models.TuringMachine.Subroutines.ClearWork

/-!
# Copying canonical binary naturals -- proof internals

The copy machine first clears its destination and then invokes canonical
binary addition from the preserved source. These proofs compose the public
literal-frame and all-prefix resource contracts of those two phases.
-/

namespace Complexity

namespace TM

variable {n : ℕ}

private def binaryCopyNatTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private theorem binaryCopyNatTape_hasBinaryNat (value : ℕ) :
    (binaryCopyNatTape value).HasBinaryNat value :=
  Tape.init_move_right_hasBinaryNat value

private theorem binaryCopyHasBinaryNat_parked {t : Tape} {value : ℕ}
    (h : t.HasBinaryNat value) : Parked t := by
  refine ⟨by rw [h.2.1], ?_⟩
  exact Tape.HasBinaryContent.cells_ne_start h.2.2

private theorem binaryCopyNatTape_parked (value : ℕ) :
    Parked (binaryCopyNatTape value) :=
  binaryCopyHasBinaryNat_parked (binaryCopyNatTape_hasBinaryNat value)

private theorem binaryCopyInitialWork_parked
    (srcIdx dstIdx counterIdx : Fin n) (srcValue dstValue : ℕ)
    (work₀ : Fin n → Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i)) :
    ∀ i, Parked (work₀ i) := by
  intro i
  by_cases hsrcIdx : i = srcIdx
  · subst i
    exact binaryCopyHasBinaryNat_parked hsrc
  by_cases hdstIdx : i = dstIdx
  · subst i
    exact binaryCopyHasBinaryNat_parked hdst
  by_cases hcounterIdx : i = counterIdx
  · subst i
    exact binaryCopyHasBinaryNat_parked hcounter
  exact hother i hsrcIdx hdstIdx hcounterIdx

private def binaryCopyMidWork (work₀ : Fin n → Tape) (dstIdx : Fin n) :
    Fin n → Tape :=
  Function.update work₀ dstIdx (binaryCopyNatTape 0)

private theorem binaryCopyMidWork_parked
    (work₀ : Fin n → Tape) (dstIdx : Fin n)
    (hwork : ∀ i, Parked (work₀ i)) :
    ∀ i, Parked (binaryCopyMidWork work₀ dstIdx i) := by
  intro i
  by_cases hi : i = dstIdx
  · subst i
    simp only [binaryCopyMidWork, Function.update_self]
    exact binaryCopyNatTape_parked 0
  · rw [binaryCopyMidWork, Function.update_of_ne hi]
    exact hwork i

private theorem binaryCopyFrame_transition
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hwork : ∀ i, Parked (work₀ i))
    (hout : Parked out₀) :
    ∀ inp work out,
      (inp = inp₀ ∧ work = work₀ ∧ out = out₀) →
      transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = work₀ ∧
        transitionTape out = out₀ := by
  rintro _ _ _ ⟨rfl, rfl, rfl⟩
  refine ⟨hinp.transitionInput_eq_self, ?_, hout.transitionTape_eq_self⟩
  funext i
  exact (hwork i).transitionTape_eq_self

theorem binaryCopyIntoTM_hoareTime_frame_internal
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dstIdx (binaryCopyNatTape srcValue) ∧
        out = out₀)
      (binaryCopyTime srcValue dstValue) := by
  let midWork := binaryCopyMidWork work₀ dstIdx
  have hwork := binaryCopyInitialWork_parked srcIdx dstIdx counterIdx
    srcValue dstValue work₀ hsrc hdst hcounter hother
  have hmidWork : ∀ i, Parked (midWork i) := by
    exact binaryCopyMidWork_parked work₀ dstIdx hwork
  have hclear := clearWorkTM_hoareTime_frame dstIdx dstValue.bits
    inp₀ work₀ out₀ hdst.eq_init_move_right hinp
    (fun i _ => hwork i) hout
  have hclear' : (clearWorkTM dstIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = midWork ∧ out = out₀)
      (clearWorkTimeBound dstValue.size) := by
    simpa [midWork, binaryCopyMidWork, binaryCopyNatTape,
      Nat.size_eq_bits_len] using hclear
  have hmidSrc : (midWork srcIdx).HasBinaryNat srcValue := by
    simpa [midWork, binaryCopyMidWork, hsrcDst] using hsrc
  have hmidDst : (midWork dstIdx).HasBinaryNat 0 := by
    simpa [midWork, binaryCopyMidWork] using
      binaryCopyNatTape_hasBinaryNat 0
  have hmidCounter : (midWork counterIdx).HasBinaryNat 0 := by
    simpa [midWork, binaryCopyMidWork, hdstCounter.symm] using hcounter
  have hadd := binaryAddIntoTM_hoareTime_frame srcIdx dstIdx counterIdx
    hsrcDst hsrcCounter hdstCounter srcValue 0 inp₀ midWork out₀
    hmidSrc hmidDst hmidCounter hinp
    (fun i hiSrc hiDst hiCounter => hmidWork i) hout
  have hseq := seqTM_hoareTime (clearWorkTM dstIdx)
    (binaryAddIntoTM srcIdx dstIdx counterIdx) hclear'
    (binaryCopyFrame_transition inp₀ midWork out₀ hinp hmidWork hout)
    hadd
  simpa [binaryCopyIntoTM, binaryCopyTime, midWork, binaryCopyMidWork,
    binaryCopyNatTape, Nat.size_eq_bits_len] using hseq

theorem binaryCopyIntoTM_hoareTimeSpace_frame_internal
    (srcIdx dstIdx counterIdx : Fin n)
    (hsrcDst : srcIdx ≠ dstIdx) (hsrcCounter : srcIdx ≠ counterIdx)
    (hdstCounter : dstIdx ≠ counterIdx)
    (srcValue dstValue inputLength initialSpace : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrc : (work₀ srcIdx).HasBinaryNat srcValue)
    (hdst : (work₀ dstIdx).HasBinaryNat dstValue)
    (hcounter : (work₀ counterIdx).HasBinaryNat 0)
    (hinp : Parked inp₀)
    (hother : ∀ i, i ≠ srcIdx → i ≠ dstIdx → i ≠ counterIdx →
      Parked (work₀ i))
    (hout : Parked out₀)
    (hworkSpace : ∀ i, (work₀ i).head ≤ initialSpace)
    (hinputSpace : inp₀.head ≤ inputLength + initialSpace + 1) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out =>
        inp = inp₀ ∧
        work = Function.update work₀ dstIdx (binaryCopyNatTape srcValue) ∧
        out = out₀)
      (binaryCopyTime srcValue dstValue) inputLength
      (binaryCopySpace initialSpace srcValue dstValue) := by
  let midWork := binaryCopyMidWork work₀ dstIdx
  have hwork := binaryCopyInitialWork_parked srcIdx dstIdx counterIdx
    srcValue dstValue work₀ hsrc hdst hcounter hother
  have hmidWork : ∀ i, Parked (midWork i) := by
    exact binaryCopyMidWork_parked work₀ dstIdx hwork
  have hinitial :
      ({ state := (clearWorkTM dstIdx).qstart
         input := inp₀
         work := work₀
         output := out₀ } :
        Cfg n (clearWorkTM dstIdx).Q).WithinAuxSpace
          inputLength initialSpace :=
    ⟨hworkSpace, hinputSpace⟩
  have hclear := clearWorkTM_hoareTimeSpace_frame dstIdx dstValue.bits
    inputLength initialSpace inp₀ work₀ out₀
    hdst.eq_init_move_right hinp (fun i _ => hwork i) hout hinitial
  have hclear' : (clearWorkTM dstIdx).HoareTimeSpace
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = midWork ∧ out = out₀)
      (clearWorkTimeBound dstValue.size) inputLength
      (initialSpace + clearWorkTimeBound dstValue.size) := by
    simpa [midWork, binaryCopyMidWork, binaryCopyNatTape,
      Nat.size_eq_bits_len] using hclear
  have hmidSrc : (midWork srcIdx).HasBinaryNat srcValue := by
    simpa [midWork, binaryCopyMidWork, hsrcDst] using hsrc
  have hmidDst : (midWork dstIdx).HasBinaryNat 0 := by
    simpa [midWork, binaryCopyMidWork] using
      binaryCopyNatTape_hasBinaryNat 0
  have hmidCounter : (midWork counterIdx).HasBinaryNat 0 := by
    simpa [midWork, binaryCopyMidWork, hdstCounter.symm] using hcounter
  have hone : 1 ≤ initialSpace := by
    have h := hworkSpace srcIdx
    rw [hsrc.2.1] at h
    exact h
  have hmidWorkSpace : ∀ i, (midWork i).head ≤ initialSpace := by
    intro i
    by_cases hi : i = dstIdx
    · subst i
      simpa [midWork, binaryCopyMidWork, binaryCopyNatTape, Tape.move]
        using hone
    · simpa [midWork, binaryCopyMidWork, hi] using hworkSpace i
  have hadd := binaryAddIntoTM_hoareTimeSpace_frame
    srcIdx dstIdx counterIdx hsrcDst hsrcCounter hdstCounter srcValue 0
    inputLength initialSpace inp₀ midWork out₀ hmidSrc hmidDst
    hmidCounter hinp (fun i _ _ _ => hmidWork i) hout hmidWorkSpace
    hinputSpace
  have hseq := seqTM_hoareTimeSpace (clearWorkTM dstIdx)
    (binaryAddIntoTM srcIdx dstIdx counterIdx) hclear'
    (binaryCopyFrame_transition inp₀ midWork out₀ hinp hmidWork hout)
    hadd
  simpa [binaryCopyIntoTM, binaryCopyTime, binaryCopySpace, midWork,
    binaryCopyMidWork, binaryCopyNatTape, Nat.size_eq_bits_len] using hseq

theorem binaryCopyIntoTM_isTransducer_internal
    (srcIdx dstIdx counterIdx : Fin n) :
    (binaryCopyIntoTM srcIdx dstIdx counterIdx).IsTransducer := by
  exact (clearWorkTM_isTransducer dstIdx).seqTM
    (binaryAddIntoTM_isTransducer srcIdx dstIdx counterIdx)

end TM

end Complexity
