/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Asymptotics
import Complexitylib.Mathlib.NatBits
import Complexitylib.Models.TuringMachine.Combinators.ForInput.Internal
import Complexitylib.Models.TuringMachine.Hoare.Space
import Complexitylib.Models.TuringMachine.Subroutines.BinaryLength.Defs
import Complexitylib.Models.TuringMachine.Subroutines.BinarySucc

/-!
# Binary input-length counter — proof internals

The exact run proof scans the read-only input and lifts one proved
`binarySuccTM` run per symbol. The space proof separately tracks every
reachable driver/body phase so input length is never charged as work space.
-/

namespace Complexity

namespace TM

variable {n : ℕ} {counterIdx : Fin n}

private def binaryLengthStartedBlank : Tape :=
  (Tape.init []).move Dir3.right

private def binaryLengthInput (x : List Bool) (head : ℕ) : Tape :=
  { head := head
    cells := (Tape.init (x.map Γ.ofBool)).cells }

private def binaryLengthCounterTape (value : ℕ) : Tape :=
  (Tape.init (value.bits.map Γ.ofBool)).move Dir3.right

private def binaryLengthWork (counterIdx : Fin n) (value : ℕ) : Fin n → Tape :=
  Function.update (fun _ => binaryLengthStartedBlank) counterIdx
    (binaryLengthCounterTape value)

private def binaryLengthScanCfg (x : List Bool) (counterIdx : Fin n)
    (value : ℕ) : Cfg n (binaryLengthTM counterIdx).Q :=
  { state := .inl .scan
    input := binaryLengthInput x (value + 1)
    work := binaryLengthWork counterIdx value
    output := binaryLengthStartedBlank }

private def binaryLengthBodyStartCfg (x : List Bool) (counterIdx : Fin n)
    (value : ℕ) : Cfg n (binarySuccTM counterIdx).Q :=
  { state := (binarySuccTM counterIdx).qstart
    input := binaryLengthInput x (value + 2)
    work := binaryLengthWork counterIdx value
    output := binaryLengthStartedBlank }

private def binaryLengthBodyDoneCfg (x : List Bool) (counterIdx : Fin n)
    (value : ℕ) : Cfg n (binarySuccTM counterIdx).Q :=
  { state := (binarySuccTM counterIdx).qhalt
    input := binaryLengthInput x (value + 2)
    work := binaryLengthWork counterIdx (value + 1)
    output := binaryLengthStartedBlank }

private def binaryLengthDoneCfg (x : List Bool) (counterIdx : Fin n) :
    Cfg n (binaryLengthTM counterIdx).Q :=
  { state := .inl .done
    input := binaryLengthInput x (x.length + 1)
    work := binaryLengthWork counterIdx x.length
    output := binaryLengthStartedBlank }

private theorem binaryLengthCounterTape_hasBinaryNat (value : ℕ) :
    (binaryLengthCounterTape value).HasBinaryNat value := by
  exact Tape.init_move_right_hasBinaryNat value

private theorem binaryLengthWork_counter (counterIdx : Fin n) (value : ℕ) :
    binaryLengthWork counterIdx value counterIdx =
      binaryLengthCounterTape value := by
  simp [binaryLengthWork]

private theorem binaryLengthWork_other (counterIdx : Fin n) (value : ℕ)
    (i : Fin n) (hi : i ≠ counterIdx) :
    binaryLengthWork counterIdx value i = binaryLengthStartedBlank := by
  simp [binaryLengthWork, hi]

private theorem binaryLengthInput_read_ne_start (x : List Bool) (head : ℕ)
    (hhead : 1 ≤ head) : (binaryLengthInput x head).read ≠ Γ.start := by
  exact Tape.init_ofBool_cells_ne_start x head hhead

private theorem binaryLengthWork_read_ne_start (counterIdx : Fin n)
    (value : ℕ) (i : Fin n) :
    (binaryLengthWork counterIdx value i).read ≠ Γ.start := by
  by_cases hi : i = counterIdx
  · subst i
    rw [binaryLengthWork_counter]
    exact Tape.init_ofBool_move_right_read_ne_start value.bits
  · rw [binaryLengthWork_other counterIdx value i hi]
    exact Tape.init_ofBool_move_right_read_ne_start []

private theorem binaryLengthStartedBlank_read_ne_start :
    binaryLengthStartedBlank.read ≠ Γ.start := by
  exact Tape.init_ofBool_move_right_read_ne_start []

private theorem binaryLengthInput_read_bit (x : List Bool) (value : ℕ)
    (hvalue : value < x.length) :
    (binaryLengthInput x (value + 1)).read = Γ.ofBool (x[value]'hvalue) := by
  exact Tape.init_ofBool_cells_lt x value hvalue

private theorem binaryLengthInput_read_blank (x : List Bool) :
    (binaryLengthInput x (x.length + 1)).read = Γ.blank := by
  exact Tape.init_ofBool_cells_ge x x.length le_rfl

private theorem binaryLengthTM_start_step (x : List Bool) (counterIdx : Fin n) :
    (binaryLengthTM counterIdx).step ((binaryLengthTM counterIdx).initCfg x) =
      some (binaryLengthScanCfg x counterIdx 0) := by
  simp [binaryLengthTM, TM.step, forInputTM, binaryLengthScanCfg,
    binaryLengthInput, binaryLengthWork, binaryLengthCounterTape,
    binaryLengthStartedBlank, Tape.read, Tape.init, readBackWrite, idleDir,
    Tape.writeAndMove, Tape.write, Tape.move]

private theorem binaryLengthTM_scan_bit_step (x : List Bool)
    (counterIdx : Fin n) (value : ℕ) (hvalue : value < x.length) :
    (binaryLengthTM counterIdx).step (binaryLengthScanCfg x counterIdx value) =
      some (forInputBodyWrap (binarySuccTM counterIdx)
        (binaryLengthBodyStartCfg x counterIdx value)) := by
  have hread := binaryLengthInput_read_bit x value hvalue
  have hstep := forInputTM_step_scan_bit_internal (binarySuccTM counterIdx)
    (binaryLengthScanCfg x counterIdx value) rfl
    (by
      show (binaryLengthInput x (value + 1)).read ≠ Γ.start
      rw [hread]
      exact Γ.ofBool_ne_start _)
    (by
      show (binaryLengthInput x (value + 1)).read ≠ Γ.blank
      rw [hread]
      exact Γ.ofBool_ne_blank _)
    (fun i => binaryLengthWork_read_ne_start counterIdx value i)
    binaryLengthStartedBlank_read_ne_start
  simpa [binaryLengthTM, binaryLengthScanCfg, binaryLengthBodyStartCfg,
    forInputBodyWrap, binaryLengthInput, Tape.move] using hstep

private theorem binaryLengthTM_scan_blank_step (x : List Bool)
    (counterIdx : Fin n) :
    (binaryLengthTM counterIdx).step
      (binaryLengthScanCfg x counterIdx x.length) =
      some (binaryLengthDoneCfg x counterIdx) := by
  have hstep := forInputTM_step_scan_blank_internal (binarySuccTM counterIdx)
    (binaryLengthScanCfg x counterIdx x.length) rfl
    (by
      show (binaryLengthInput x (x.length + 1)).read = Γ.blank
      exact binaryLengthInput_read_blank x)
    (fun i => binaryLengthWork_read_ne_start counterIdx x.length i)
    binaryLengthStartedBlank_read_ne_start
  simpa [binaryLengthTM, binaryLengthScanCfg, binaryLengthDoneCfg] using hstep

private theorem binaryLengthTM_body_run (x : List Bool)
    (counterIdx : Fin n) (value : ℕ) :
    (binarySuccTM counterIdx).reachesIn (binarySuccTime value)
      (binaryLengthBodyStartCfg x counterIdx value)
      (binaryLengthBodyDoneCfg x counterIdx value) := by
  obtain ⟨c', hreach, hhalt, hinput, hwork, hvalue, houtput⟩ :=
    binarySuccTM_reachesIn_frame counterIdx value
      (binaryLengthInput x (value + 2)) (binaryLengthWork counterIdx value)
      binaryLengthStartedBlank
      (by
        rw [binaryLengthWork_counter]
        exact binaryLengthCounterTape_hasBinaryNat value)
      (binaryLengthInput_read_ne_start x (value + 2) (by omega))
      (fun i _ => binaryLengthWork_read_ne_start counterIdx value i)
      binaryLengthStartedBlank_read_ne_start
  have hc' : c' = binaryLengthBodyDoneCfg x counterIdx value := by
    refine Cfg.ext hhalt hinput ?_ houtput
    funext i
    by_cases hi : i = counterIdx
    · subst i
      change c'.work counterIdx = binaryLengthWork counterIdx (value + 1) counterIdx
      rw [binaryLengthWork_counter]
      exact hvalue.eq_init_move_right
    · change c'.work i = binaryLengthWork counterIdx (value + 1) i
      rw [hwork i hi, binaryLengthWork_other counterIdx value i hi,
        binaryLengthWork_other counterIdx (value + 1) i hi]
  rw [← hc']
  simpa [binaryLengthBodyStartCfg] using hreach

private theorem binaryLengthTM_loopback_step (x : List Bool)
    (counterIdx : Fin n) (value : ℕ) :
    (binaryLengthTM counterIdx).step
      (forInputBodyWrap (binarySuccTM counterIdx)
        (binaryLengthBodyDoneCfg x counterIdx value)) =
      some (binaryLengthScanCfg x counterIdx (value + 1)) := by
  have hstep := forInputTM_step_body_halt_internal (binarySuccTM counterIdx)
    (binaryLengthBodyDoneCfg x counterIdx value) rfl
    (binaryLengthInput_read_ne_start x (value + 2) (by omega))
    (fun i => binaryLengthWork_read_ne_start counterIdx (value + 1) i)
    binaryLengthStartedBlank_read_ne_start
  simpa [binaryLengthTM, binaryLengthBodyDoneCfg, binaryLengthScanCfg,
    forInputBodyWrap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

private theorem binaryLengthTM_init_withinAuxSpace (x : List Bool)
    (counterIdx : Fin n) :
    ((binaryLengthTM counterIdx).initCfg x).WithinAuxSpace x.length
      (binaryLengthSpace x.length) := by
  constructor
  · intro i
    simp [binaryLengthSpace, Tape.init]
  · simp [binaryLengthSpace, Tape.init]

private theorem binaryLengthScanCfg_withinAuxSpace (x : List Bool)
    (counterIdx : Fin n) (value : ℕ) (hvalue : value ≤ x.length) :
    (binaryLengthScanCfg x counterIdx value).WithinAuxSpace x.length
      (binaryLengthSpace x.length) := by
  constructor
  · intro i
    by_cases hi : i = counterIdx
    · subst i
      simp [binaryLengthScanCfg, binaryLengthWork, binaryLengthCounterTape,
        binaryLengthSpace, Tape.init, Tape.move]
    · simp [binaryLengthScanCfg, binaryLengthWork, binaryLengthStartedBlank,
        binaryLengthSpace, Tape.init, Tape.move, hi]
  · simp [binaryLengthScanCfg, binaryLengthInput, binaryLengthSpace]
    omega

private theorem binaryLengthDoneCfg_withinAuxSpace (x : List Bool)
    (counterIdx : Fin n) :
    (binaryLengthDoneCfg x counterIdx).WithinAuxSpace x.length
      (binaryLengthSpace x.length) := by
  simpa [binaryLengthDoneCfg, binaryLengthScanCfg] using
    binaryLengthScanCfg_withinAuxSpace x counterIdx x.length le_rfl

private theorem binaryLengthBodyStartCfg_withinAuxSpace (x : List Bool)
    (counterIdx : Fin n) (value : ℕ) (hvalue : value < x.length) :
    (binaryLengthBodyStartCfg x counterIdx value).WithinAuxSpace x.length 1 := by
  constructor
  · intro i
    by_cases hi : i = counterIdx
    · subst i
      simp [binaryLengthBodyStartCfg, binaryLengthWork,
        binaryLengthCounterTape, Tape.init, Tape.move]
    · simp [binaryLengthBodyStartCfg, binaryLengthWork,
        binaryLengthStartedBlank, Tape.init, Tape.move, hi]
  · simp [binaryLengthBodyStartCfg, binaryLengthInput]
    omega

private theorem binaryLengthBodyPrefix_withinAuxSpace (x : List Bool)
    (counterIdx : Fin n) (value t : ℕ)
    (d : Cfg n (binarySuccTM counterIdx).Q) (hvalue : value < x.length)
    (hreach : (binarySuccTM counterIdx).reachesIn t
      (binaryLengthBodyStartCfg x counterIdx value) d) :
    d.WithinAuxSpace x.length (binaryLengthSpace x.length) := by
  have hcontract := binarySuccTM_hoareTimeSpace_frame counterIdx value
    x.length 1 (binaryLengthInput x (value + 2))
    (binaryLengthWork counterIdx value) binaryLengthStartedBlank
    (by
      rw [binaryLengthWork_counter]
      exact binaryLengthCounterTape_hasBinaryNat value)
    (binaryLengthInput_read_ne_start x (value + 2) (by omega))
    (fun i _ => binaryLengthWork_read_ne_start counterIdx value i)
    binaryLengthStartedBlank_read_ne_start
    (binaryLengthBodyStartCfg_withinAuxSpace x counterIdx value hvalue)
  have hd := hcontract.2 _ _ _ ⟨rfl, rfl, rfl⟩ d
    (TM.reaches_of_reachesIn hreach)
  apply hd.mono le_rfl
  calc
    1 + binarySuccTime value ≤ 1 + (2 * value.size + 2) :=
      Nat.add_le_add_left (binarySuccTime_le value) 1
    _ ≤ 2 * x.length.size + 3 := by
      have hsize := Nat.size_le_size (Nat.le_of_lt hvalue)
      omega
    _ = binaryLengthSpace x.length := by
      simp [binaryLengthSpace]

private theorem binaryLengthTM_loop (x : List Bool) (counterIdx : Fin n) :
    ∀ count value, value + count = x.length →
      (binaryLengthTM counterIdx).reachesIn
        (binaryLengthLoopTime value count)
        (binaryLengthScanCfg x counterIdx value)
        (binaryLengthDoneCfg x counterIdx) := by
  intro count
  induction count with
  | zero =>
      intro value hlength
      have hvalue : value = x.length := by omega
      subst value
      exact .step (binaryLengthTM_scan_blank_step x counterIdx) .zero
  | succ count ih =>
      intro value hlength
      have hvalue : value < x.length := by omega
      have hscan : (binaryLengthTM counterIdx).reachesIn 1
          (binaryLengthScanCfg x counterIdx value)
          (forInputBodyWrap (binarySuccTM counterIdx)
            (binaryLengthBodyStartCfg x counterIdx value)) :=
        .step (binaryLengthTM_scan_bit_step x counterIdx value hvalue) .zero
      have hbody : (binaryLengthTM counterIdx).reachesIn
          (binarySuccTime value)
          (forInputBodyWrap (binarySuccTM counterIdx)
            (binaryLengthBodyStartCfg x counterIdx value))
          (forInputBodyWrap (binarySuccTM counterIdx)
            (binaryLengthBodyDoneCfg x counterIdx value)) := by
        simpa [binaryLengthTM] using
          forInputTM_body_reachesIn_internal (binarySuccTM counterIdx)
            (binaryLengthTM_body_run x counterIdx value)
      have hloopback : (binaryLengthTM counterIdx).reachesIn 1
          (forInputBodyWrap (binarySuccTM counterIdx)
            (binaryLengthBodyDoneCfg x counterIdx value))
          (binaryLengthScanCfg x counterIdx (value + 1)) :=
        .step (binaryLengthTM_loopback_step x counterIdx value) .zero
      have htail := ih (value + 1) (by omega)
      have hreach := reachesIn_trans (binaryLengthTM counterIdx) hscan
        (reachesIn_trans (binaryLengthTM counterIdx) hbody
          (reachesIn_trans (binaryLengthTM counterIdx) hloopback htail))
      simpa [binaryLengthLoopTime, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hreach

private theorem binaryLengthTM_loop_withinAuxSpace (x : List Bool)
    (counterIdx : Fin n) :
    ∀ count value t (c : Cfg n (binaryLengthTM counterIdx).Q),
      value + count = x.length →
      (binaryLengthTM counterIdx).reachesIn t
        (binaryLengthScanCfg x counterIdx value) c →
      t ≤ binaryLengthLoopTime value count →
      c.WithinAuxSpace x.length (binaryLengthSpace x.length) := by
  intro count
  induction count with
  | zero =>
      intro value t c hlength hreach ht
      have hvalue : value = x.length := by omega
      subst value
      simp only [binaryLengthLoopTime] at ht
      have ht' : t = 0 ∨ t = 1 := by omega
      rcases ht' with rfl | rfl
      · cases hreach
        exact binaryLengthScanCfg_withinAuxSpace x counterIdx x.length le_rfl
      · have hdone : (binaryLengthTM counterIdx).reachesIn 1
            (binaryLengthScanCfg x counterIdx x.length)
            (binaryLengthDoneCfg x counterIdx) :=
          .step (binaryLengthTM_scan_blank_step x counterIdx) .zero
        have hc := (binaryLengthTM counterIdx).reachesIn_right_unique
          hreach hdone
        rw [hc]
        exact binaryLengthDoneCfg_withinAuxSpace x counterIdx
  | succ count ih =>
      intro value t c hlength hreach ht
      have hvalue : value < x.length := by omega
      by_cases htzero : t = 0
      · subst t
        cases hreach
        exact binaryLengthScanCfg_withinAuxSpace x counterIdx value
          (Nat.le_of_lt hvalue)
      · let u := t - 1
        have htu : 1 + u = t := by
          dsimp only [u]
          omega
        by_cases hubody : u ≤ binarySuccTime value
        · obtain ⟨d, hprefix, _hsuffix⟩ := reachesIn_prefix_internal
            (binaryLengthTM_body_run x counterIdx value) hubody
          have hlift : (binaryLengthTM counterIdx).reachesIn u
              (forInputBodyWrap (binarySuccTM counterIdx)
                (binaryLengthBodyStartCfg x counterIdx value))
              (forInputBodyWrap (binarySuccTM counterIdx) d) := by
            simpa [binaryLengthTM] using
              forInputTM_body_reachesIn_internal
                (binarySuccTM counterIdx) hprefix
          have hcanonical : (binaryLengthTM counterIdx).reachesIn t
              (binaryLengthScanCfg x counterIdx value)
              (forInputBodyWrap (binarySuccTM counterIdx) d) := by
            have hscan : (binaryLengthTM counterIdx).reachesIn 1
                (binaryLengthScanCfg x counterIdx value)
                (forInputBodyWrap (binarySuccTM counterIdx)
                  (binaryLengthBodyStartCfg x counterIdx value)) :=
              .step (binaryLengthTM_scan_bit_step x counterIdx value hvalue) .zero
            have htotal := reachesIn_trans (binaryLengthTM counterIdx)
              hscan hlift
            simpa [htu] using htotal
          have hc := (binaryLengthTM counterIdx).reachesIn_right_unique
            hreach hcanonical
          rw [hc]
          simpa [forInputBodyWrap] using
            binaryLengthBodyPrefix_withinAuxSpace x counterIdx value u d
              hvalue hprefix
        · let prefixTime := 1 + binarySuccTime value + 1
          have hprefixTime : prefixTime ≤ t := by
            dsimp only [prefixTime, u] at ⊢ hubody
            omega
          let tailTime := t - prefixTime
          have htailEq : prefixTime + tailTime = t := by
            dsimp only [tailTime]
            exact Nat.add_sub_of_le hprefixTime
          have htailBound :
              tailTime ≤ binaryLengthLoopTime (value + 1) count := by
            rw [binaryLengthLoopTime] at ht
            dsimp only [prefixTime, tailTime] at ⊢
            omega
          have htailFull := binaryLengthTM_loop x counterIdx count (value + 1)
            (by omega)
          obtain ⟨d, htail, _hsuffix⟩ := reachesIn_prefix_internal
            htailFull htailBound
          have hscan : (binaryLengthTM counterIdx).reachesIn 1
              (binaryLengthScanCfg x counterIdx value)
              (forInputBodyWrap (binarySuccTM counterIdx)
                (binaryLengthBodyStartCfg x counterIdx value)) :=
            .step (binaryLengthTM_scan_bit_step x counterIdx value hvalue) .zero
          have hbody : (binaryLengthTM counterIdx).reachesIn
              (binarySuccTime value)
              (forInputBodyWrap (binarySuccTM counterIdx)
                (binaryLengthBodyStartCfg x counterIdx value))
              (forInputBodyWrap (binarySuccTM counterIdx)
                (binaryLengthBodyDoneCfg x counterIdx value)) := by
            simpa [binaryLengthTM] using
              forInputTM_body_reachesIn_internal (binarySuccTM counterIdx)
                (binaryLengthTM_body_run x counterIdx value)
          have hloopback : (binaryLengthTM counterIdx).reachesIn 1
              (forInputBodyWrap (binarySuccTM counterIdx)
                (binaryLengthBodyDoneCfg x counterIdx value))
              (binaryLengthScanCfg x counterIdx (value + 1)) :=
            .step (binaryLengthTM_loopback_step x counterIdx value) .zero
          have hcanonical := reachesIn_trans (binaryLengthTM counterIdx) hscan
            (reachesIn_trans (binaryLengthTM counterIdx) hbody
              (reachesIn_trans (binaryLengthTM counterIdx) hloopback htail))
          have hcanonical' : (binaryLengthTM counterIdx).reachesIn t
              (binaryLengthScanCfg x counterIdx value) d := by
            convert hcanonical using 1
            all_goals
              dsimp only [prefixTime] at htailEq ⊢
              omega
          have hc := (binaryLengthTM counterIdx).reachesIn_right_unique
            hreach hcanonical'
          rw [hc]
          exact ih (value + 1) tailTime d (by omega) htail htailBound

/-! ## Public-theorem internals -/

theorem binaryLengthTime_le_internal (length : ℕ) :
    binaryLengthTime length ≤ 2 + length * (2 * length.size + 4) := by
  have loopBound : ∀ count value, value + count ≤ length →
      binaryLengthLoopTime value count ≤
        1 + count * (2 * length.size + 4) := by
    intro count
    induction count with
    | zero =>
        intro value _
        simp [binaryLengthLoopTime]
    | succ count ih =>
        intro value hlength
        have hvalue : value ≤ length := by omega
        have hsize : value.size ≤ length.size := Nat.size_le_size hvalue
        have hsucc : binarySuccTime value ≤ 2 * length.size + 2 :=
          le_trans (binarySuccTime_le value) (by omega)
        have htail := ih (value + 1) (by omega)
        rw [binaryLengthLoopTime]
        calc
          1 + binarySuccTime value + 1 + binaryLengthLoopTime (value + 1) count
              ≤ 1 + (2 * length.size + 2) + 1 +
                  (1 + count * (2 * length.size + 4)) := by omega
          _ = 1 + (count + 1) * (2 * length.size + 4) := by ring
  have hloop := loopBound length 0 (by omega)
  rw [binaryLengthTime]
  omega

theorem binaryLengthSpace_bigO_log_internal :
    binaryLengthSpace =O (fun length => Nat.log 2 length) := by
  rw [BigO]
  apply Asymptotics.IsBigO.of_bound 7
  filter_upwards [Filter.eventually_ge_atTop 2] with length hlength
  simp only [Real.norm_natCast]
  have hlog : 1 ≤ Nat.log 2 length :=
    Nat.log_pos (by omega) hlength
  have hsize := Nat.size_le_log_two_add_one length
  have hbound : binaryLengthSpace length ≤ 7 * Nat.log 2 length := by
    rw [binaryLengthSpace]
    omega
  exact_mod_cast hbound

theorem binaryLengthTM_reachesIn_internal (counterIdx : Fin n)
    (x : List Bool) :
    (binaryLengthTM counterIdx).reachesIn (binaryLengthTime x.length)
      ((binaryLengthTM counterIdx).initCfg x)
      (binaryLengthDoneCfg x counterIdx) := by
  have hstart : (binaryLengthTM counterIdx).reachesIn 1
      ((binaryLengthTM counterIdx).initCfg x)
      (binaryLengthScanCfg x counterIdx 0) :=
    .step (binaryLengthTM_start_step x counterIdx) .zero
  have hloop := binaryLengthTM_loop x counterIdx x.length 0 (by omega)
  have hreach := reachesIn_trans (binaryLengthTM counterIdx) hstart hloop
  simpa [binaryLengthTime] using hreach

theorem binaryLengthTM_reachesIn_frame_internal (counterIdx : Fin n)
    (x : List Bool) :
    ∃ c',
      (binaryLengthTM counterIdx).reachesIn (binaryLengthTime x.length)
        ((binaryLengthTM counterIdx).initCfg x) c' ∧
      (binaryLengthTM counterIdx).halted c' ∧
      c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      c'.input.head = x.length + 1 ∧
      (c'.work counterIdx).HasBinaryNat x.length ∧
      (∀ i, i ≠ counterIdx →
        c'.work i = (Tape.init []).move Dir3.right) ∧
      c'.output = (Tape.init []).move Dir3.right := by
  refine ⟨binaryLengthDoneCfg x counterIdx,
    binaryLengthTM_reachesIn_internal counterIdx x, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · change (binaryLengthWork counterIdx x.length counterIdx).HasBinaryNat x.length
    rw [binaryLengthWork_counter]
    exact binaryLengthCounterTape_hasBinaryNat x.length
  · intro i hi
    simpa [binaryLengthStartedBlank] using
      binaryLengthWork_other counterIdx x.length i hi

theorem binaryLengthTM_hoareTime_internal (counterIdx : Fin n)
    (x : List Bool) :
    (binaryLengthTM counterIdx).HoareTime
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        inp.head = x.length + 1 ∧
        (work counterIdx).HasBinaryNat x.length ∧
        (∀ i, i ≠ counterIdx →
          work i = (Tape.init []).move Dir3.right) ∧
        out = (Tape.init []).move Dir3.right)
      (binaryLengthTime x.length) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨binaryLengthDoneCfg x counterIdx, binaryLengthTime x.length,
    le_rfl, binaryLengthTM_reachesIn_internal counterIdx x, rfl, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩
  · change (binaryLengthWork counterIdx x.length counterIdx).HasBinaryNat x.length
    rw [binaryLengthWork_counter]
    exact binaryLengthCounterTape_hasBinaryNat x.length
  · intro i hi
    simpa [binaryLengthStartedBlank] using
      binaryLengthWork_other counterIdx x.length i hi

theorem binaryLengthTM_hoareTimeSpace_internal (counterIdx : Fin n)
    (x : List Bool) :
    (binaryLengthTM counterIdx).HoareTimeSpace
      (fun inp work out =>
        inp = Tape.init (x.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧
        out = Tape.init [])
      (fun inp work out =>
        inp.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        inp.head = x.length + 1 ∧
        (work counterIdx).HasBinaryNat x.length ∧
        (∀ i, i ≠ counterIdx →
          work i = (Tape.init []).move Dir3.right) ∧
        out = (Tape.init []).move Dir3.right)
      (binaryLengthTime x.length) x.length (binaryLengthSpace x.length) := by
  refine ⟨binaryLengthTM_hoareTime_internal counterIdx x, ?_⟩
  rintro inp work out ⟨rfl, rfl, rfl⟩ c hreach
  obtain ⟨t, hreachIn⟩ :=
    (binaryLengthTM counterIdx).reaches_to_reachesIn hreach
  have hfull := binaryLengthTM_reachesIn_internal counterIdx x
  have ht : t ≤ binaryLengthTime x.length :=
    (binaryLengthTM counterIdx).reachesIn_le_halt hreachIn hfull rfl
  by_cases htzero : t = 0
  · subst t
    cases hreachIn
    exact binaryLengthTM_init_withinAuxSpace x counterIdx
  · let tailTime := t - 1
    have htime : 1 + tailTime = t := by
      dsimp only [tailTime]
      omega
    have htailBound :
        tailTime ≤ binaryLengthLoopTime 0 x.length := by
      rw [binaryLengthTime] at ht
      dsimp only [tailTime]
      omega
    have hloopFull := binaryLengthTM_loop x counterIdx x.length 0 (by omega)
    obtain ⟨d, htail, _hsuffix⟩ := reachesIn_prefix_internal
      hloopFull htailBound
    have hstart : (binaryLengthTM counterIdx).reachesIn 1
        ((binaryLengthTM counterIdx).initCfg x)
        (binaryLengthScanCfg x counterIdx 0) :=
      .step (binaryLengthTM_start_step x counterIdx) .zero
    have hcanonical := reachesIn_trans (binaryLengthTM counterIdx) hstart htail
    have hcanonical' : (binaryLengthTM counterIdx).reachesIn t
        ((binaryLengthTM counterIdx).initCfg x) d := by
      simpa [htime] using hcanonical
    have hc := (binaryLengthTM counterIdx).reachesIn_right_unique
      hreachIn hcanonical'
    rw [hc]
    exact binaryLengthTM_loop_withinAuxSpace x counterIdx x.length 0
      tailTime d (by omega) htail htailBound

theorem binaryLengthTM_isTransducer_internal (counterIdx : Fin n) :
    (binaryLengthTM counterIdx).IsTransducer := by
  exact binarySuccTM_isTransducer counterIdx |>.forInputTM_internal

end TM

end Complexity
