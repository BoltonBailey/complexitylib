import Complexitylib.Models.TuringMachine.Subroutines
import Complexitylib.Models.TuringMachine.CounterSubroutines
import Complexitylib.Models.TuringMachine.Hoare

/-!
# Output-emission subroutines

Building blocks for machines that *compute string functions* (`ComputesInTime`):
the output tape is treated as an append-only accumulator, written left to
right. The central predicate `outAcc ys out` says the output tape holds
exactly the bits `ys` (after the `▷` at cell 0) with the head parked on the
first blank, ready to append; emitters have Hoare specs of the shape

    {outAcc ys ∧ …} emit {outAcc (ys ++ w) ∧ …}

which compose by `seqTM` along `List.append` associativity. The final bridge
to `ComputesInTime` is `outAcc.hasOutput`.

This layer is the foundation for the Cook–Levin reduction emitter
(`docs/A5-ReductionEmitter.md`).

## Main definitions

- `TM.outAcc` — the output-accumulator predicate
- `TM.Parked` — a tape whose head is off `▷` and which has no spurious `▷`s
- `TM.emitBitsTM` — append a fixed word to the output

## Main results

- `TM.outAcc.hasOutput` — accumulated output is `hasOutput`
- `TM.outAcc_append_bit` — one `writeAndMove _ .right` extends the accumulator
- `TM.emitBitsTM_hoareTime` — `emitBitsTM w` appends `w` in `|w|` steps,
  preserving the input and work tapes
-/

namespace TM

variable {n : ℕ}

-- ════════════════════════════════════════════════════════════════════════
-- Parked tapes
-- ════════════════════════════════════════════════════════════════════════

/-- A tape parked for preservation: head off `▷` (so `idleDir` stays put and
    `δ_right_of_start` is moot) and no `▷` outside cell 0 (so `readBackWrite`
    writes back the read symbol verbatim). Machines that do not use a tape
    keep it parked and literally unchanged. -/
def Parked (t : Tape) : Prop :=
  1 ≤ t.head ∧ ∀ j, 1 ≤ j → t.cells j ≠ Γ.start

theorem Parked.read_ne_start {t : Tape} (h : Parked t) : t.read ≠ Γ.start :=
  h.2 t.head h.1

/-- A parked tape is untouched by the no-op action `writeAndMove (readBackWrite
    read) (idleDir read)`. -/
theorem Parked.writeAndMove_readBack_idle {t : Tape} (h : Parked t) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t :=
  Tape.writeAndMove_readBack_idle_of_ne_start t h.read_ne_start

/-- A parked tape's head does not move under `idleDir`. -/
theorem Parked.move_idle {t : Tape} (h : Parked t) :
    t.move (idleDir t.read) = t := by
  rw [idleDir, if_neg h.read_ne_start]
  rfl

-- ════════════════════════════════════════════════════════════════════════
-- The output accumulator
-- ════════════════════════════════════════════════════════════════════════

/-- **Output accumulator.** The output tape holds exactly the bits `ys`
    (cells `1..|ys|`, after the `▷` at cell 0), all cells beyond are blank,
    and the head is parked on the first blank — ready to append. -/
def outAcc (ys : List Bool) (out : Tape) : Prop :=
  out.head = ys.length + 1 ∧
  out.cells 0 = Γ.start ∧
  (∀ i, (h : i < ys.length) → out.cells (i + 1) = Γ.ofBool ys[i]) ∧
  (∀ j, ys.length + 1 ≤ j → out.cells j = Γ.blank)

namespace outAcc

theorem head_eq {ys : List Bool} {out : Tape} (h : outAcc ys out) :
    out.head = ys.length + 1 := h.1

/-- The accumulator reads the first blank. -/
theorem read_blank {ys : List Bool} {out : Tape} (h : outAcc ys out) :
    out.read = Γ.blank := by
  rw [Tape.read, h.1]; exact h.2.2.2 _ (le_refl _)

/-- An accumulator tape is parked (bits and blanks are never `▷`). -/
theorem parked {ys : List Bool} {out : Tape} (h : outAcc ys out) : Parked out := by
  refine ⟨by rw [h.1]; omega, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j (ys.length + 1) with hlt | hge
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [h.2.2.1 i (by omega)]
    cases ys[i] <;> decide
  · rw [h.2.2.2 j hge]; decide

/-- The bridge to `ComputesInTime`: an accumulated output `hasOutput` its bits. -/
theorem hasOutput {ys : List Bool} {out : Tape} (h : outAcc ys out) :
    out.hasOutput ys :=
  ⟨fun i hi => h.2.2.1 i hi, h.2.2.2 _ (le_refl _)⟩

end outAcc

/-- The empty accumulator: a blank output tape with the head bumped to cell 1. -/
theorem outAcc_nil_init : outAcc [] { head := 1, cells := (initTape []).cells } := by
  refine ⟨rfl, by simp [initTape], fun i hi => absurd hi (by simp), fun j hj => ?_⟩
  show (initTape []).cells j = Γ.blank
  simp only [initTape]
  rw [if_neg (by omega : ¬ j = 0)]
  simp

/-- **Appending one bit.** Writing `Γ.ofBool b` at the accumulator head and
    moving right extends the accumulator by `b`. -/
theorem outAcc_append_bit {ys : List Bool} {out : Tape} (h : outAcc ys out) (b : Bool) :
    outAcc (ys ++ [b]) (out.writeAndMove (Γ.ofBool b) .right) := by
  obtain ⟨hhead, hc0, hbits, hblank⟩ := h
  have hne : ¬ out.head = 0 := by omega
  have hcells : (out.writeAndMove (Γ.ofBool b) .right).cells
      = Function.update out.cells (ys.length + 1) (Γ.ofBool b) := by
    show ((out.write _).move _).cells = _
    rw [Tape.move]
    show (out.write _).cells = _
    rw [Tape.write, if_neg hne, hhead]
  have hhead' : (out.writeAndMove (Γ.ofBool b) .right).head = out.head + 1 := by
    show ((out.write _).move _).head = _
    rw [Tape.move]
    show (out.write _).head + 1 = _
    rw [Tape.write, if_neg hne]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hhead', hhead]; simp
  · rw [hcells, Function.update_of_ne (by omega : ¬ (0 : ℕ) = ys.length + 1)]
    exact hc0
  · intro i hi
    rw [List.length_append, List.length_cons, List.length_nil] at hi
    rcases Nat.lt_or_ge i ys.length with hlt | hge
    · rw [hcells, Function.update_of_ne (by omega : ¬ i + 1 = ys.length + 1),
        List.getElem_append_left hlt]
      exact hbits i hlt
    · obtain rfl : i = ys.length := by omega
      rw [hcells, Function.update_self,
        List.getElem_append_right (le_refl _)]
      simp
  · intro j hj
    rw [List.length_append, List.length_cons, List.length_nil] at hj
    rw [hcells, Function.update_of_ne (by omega : ¬ j = ys.length + 1)]
    exact hblank j (by omega)

-- ════════════════════════════════════════════════════════════════════════
-- emitBitsTM: append a fixed word to the output
-- ════════════════════════════════════════════════════════════════════════

/-- Writable symbol for a bit. -/
def Γw.ofBool : Bool → Γw
  | false => .zero
  | true => .one

@[simp] theorem Γw.ofBool_toΓ (b : Bool) : (Γw.ofBool b).toΓ = Γ.ofBool b := by
  cases b <;> rfl

/-- **Append the fixed word `w` to the output** and halt. State `k` = number of
    bits already emitted; each step writes bit `k` and moves the output head
    right; input and work tapes are parked and untouched. -/
def emitBitsTM (w : List Bool) : TM n where
  Q := Fin (w.length + 1)
  qstart := ⟨0, by omega⟩
  qhalt := ⟨w.length, by omega⟩
  δ := fun k iHead wHeads oHead =>
    if h : k.val < w.length then
      (⟨k.val + 1, by omega⟩, fun i => readBackWrite (wHeads i), Γw.ofBool w[k.val],
       idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
    else
      allIdle k iHead wHeads oHead
  δ_right_of_start := by
    intro k iHead wHeads oHead
    by_cases h : k.val < w.length
    · simp only [h, ↓reduceDIte]
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => trivial⟩
    · simp only [h, ↓reduceDIte]
      exact rightOfStart_allIdle iHead wHeads oHead

/-- One emit step: from state `k < |w|`, the machine writes bit `k`, advances
    the accumulator, and leaves the parked input and work tapes unchanged. -/
private theorem emitBitsTM_step (w : List Bool) (c : Cfg n (emitBitsTM (n := n) w).Q)
    (k : ℕ) (hk : k < w.length) (hst : c.state = ⟨k, by omega⟩)
    (hinp : Parked c.input) (hwork : ∀ i, Parked (c.work i)) :
    (emitBitsTM (n := n) w).step c = some
      { state := ⟨k + 1, by omega⟩, input := c.input, work := c.work,
        output := c.output.writeAndMove (Γ.ofBool w[k]) .right } := by
  have hne : ¬ c.state = (emitBitsTM (n := n) w).qhalt := by
    rw [hst]
    simp only [emitBitsTM, Fin.mk.injEq]
    omega
  rw [TM.step, if_neg hne]
  simp only [emitBitsTM, hst, hk, ↓reduceDIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact hinp.move_idle
  · funext i
    exact (hwork i).writeAndMove_readBack_idle
  · rw [Γw.ofBool_toΓ]

/-- The emit loop: from state `k` with `|w| = k + m`, the machine reaches the
    halt state in exactly `m` steps, appending `w.drop k` and preserving the
    input and work tapes. -/
private theorem emitBitsTM_run (w : List Bool) (m : ℕ) :
    ∀ (k : ℕ) (hk : w.length = k + m),
      ∀ (c : Cfg n (emitBitsTM (n := n) w).Q) (ys : List Bool),
      c.state = ⟨k, by omega⟩ → Parked c.input → (∀ i, Parked (c.work i)) →
      outAcc ys c.output →
      ∃ c', (emitBitsTM (n := n) w).reachesIn m c c' ∧
        c'.state = ⟨w.length, by omega⟩ ∧ c'.input = c.input ∧ c'.work = c.work ∧
        outAcc (ys ++ w.drop k) c'.output := by
  induction m with
  | zero =>
    intro k hk c ys hst hinp hwork hout
    refine ⟨c, .zero, ?_, rfl, rfl, ?_⟩
    · rw [hst]; congr 1; omega
    · rw [List.drop_of_length_le (by omega), List.append_nil]
      exact hout
  | succ m ih =>
    intro k hk c ys hst hinp hwork hout
    have hklt : k < w.length := by omega
    have hstep := emitBitsTM_step w c k hklt hst hinp hwork
    set c₁ : Cfg n (emitBitsTM (n := n) w).Q :=
      { state := ⟨k + 1, by omega⟩, input := c.input, work := c.work,
        output := c.output.writeAndMove (Γ.ofBool w[k]) .right } with hc₁
    obtain ⟨c', hreach, hst', hinp', hwork', hout'⟩ :=
      ih (k + 1) (by omega) c₁ (ys ++ [w[k]]) rfl hinp hwork
        (outAcc_append_bit hout w[k])
    refine ⟨c', .step hstep hreach, hst', hinp', hwork', ?_⟩
    rwa [List.append_assoc, List.singleton_append,
      List.getElem_cons_drop] at hout'

/-- **`emitBitsTM` Hoare specification.** Appends the word `w` to the output
    accumulator in `|w|` steps, leaving the (parked) input and work tapes
    literally unchanged. Ghost-parametrized by the initial tapes for
    `seqTM` composition. -/
theorem emitBitsTM_hoareTime (w : List Bool) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (ys : List Bool) (hinp₀ : Parked inp₀) (hwork₀ : ∀ i, Parked (work₀ i)) :
    (emitBitsTM (n := n) w).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ outAcc ys out)
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ outAcc (ys ++ w) out)
      w.length := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  obtain ⟨c', hreach, hst', hinp', hwork', hout'⟩ :=
    emitBitsTM_run w w.length 0 (by omega)
      { state := ⟨0, by omega⟩, input := inp, work := work, output := out }
      ys rfl hinp₀ hwork₀ hout
  refine ⟨c', w.length, le_refl _, hreach, ?_, hinp', hwork', ?_⟩
  · exact hst'
  · rw [List.drop_zero] at hout'
    exact hout'

end TM
