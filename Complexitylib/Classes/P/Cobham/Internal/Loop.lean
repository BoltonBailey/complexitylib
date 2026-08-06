/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Models.TuringMachine.Combinators.RetargetCompute
public import Complexitylib.Models.TuringMachine.Hoare.RetargetOutput
public import Complexitylib.Models.TuringMachine.Registers
public import Complexitylib.Models.TuringMachine.Registers.ForReg
public import Complexitylib.Models.TuringMachine.Registers.RegisterOps
public import Complexitylib.Models.TuringMachine.Registers.EmitSeq
public import Complexitylib.Models.TuringMachine.Subroutines.UnaryLength
public import Complexitylib.Models.TuringMachine.Subroutines.CopyWorkOutput
public import Complexitylib.Models.TuringMachine.Subroutines.ClearWork
public import Complexitylib.Models.TuringMachine.Subroutines.Internal
public import Complexitylib.Models.TuringMachine.Placement

/-!
# Running an `FP` machine from a work tape onto a work tape — proof internals

The loop of the `boundedRec` case (`Complexity.Cobham.recFoldClamp_mem_FP`) has
to apply an arbitrary `FP` function once per iteration, on a value that lives on
a work tape and whose result must land on a work tape — the real output tape is
one-way, so it cannot serve as scratch inside a loop.

Both halves of that redirection already exist separately: `TM.retargetInputStarted`
reads a machine's input off a work tape, and `TM.retargetOutput` writes its
output onto a fresh work tape. Composing them gives `TM.applyTM`, a
work-to-work evaluator, and composing their two Hoare rules gives its contract.

The loop also has to *branch on a bit* — apply `A` or `B` according to the bit
being consumed. Nothing in the existing `FP` toolkit can: `Complexity.takeLen`,
`Complexity.reverse`, `Complexity.pair`, `Cobham.fstBlock`, `Cobham.sndBlock` and
`Cobham.mulUnpair` all determine their output's *length* from their inputs'
lengths alone, so none of them can react to a bit's value. `Complexity.headFlag`
closes that gap by turning a bit test into a length.

## Main results

- `Complexity.TM.applyTM` — the work-to-work evaluator for a source machine
- `Complexity.TM.applyTM_hoareTime` — its time contract
- `Complexity.headFlag_mem_FP` — a bit test whose answer is a length

## What else lives here

Besides the evaluator, this file carries the pieces the bounded-iteration
machine of `Complexitylib.Classes.P.Cobham.Internal.Iterate` is built from: the
content-agnostic reset (`Complexity.resetTapesTM`), the value move
(`Complexity.copyToVirtualInputTM`), the tape layout
(`Complexity.rfIdx`/`wfIdx`/`junkIdx`/`appIdx`/`vinIdx`/`resIdx`), and the four
phase contracts `Complexity.placedApply_hoareTime`,
`Complexity.iterPark_hoareTime`, `Complexity.iterResetScratch_hoareTime` and
`Complexity.iterFinish_hoareTime`. -/


@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-- **Work-tape-to-work-tape evaluation.** `applyTM M : TM (k + 2)` reads the
source machine's input off work tape `k`, runs `M` on it, and leaves the result
on work tape `k + 1`; the real input and output tapes are untouched.

Work tapes `0, …, k-1` are `M`'s own scratch, so a caller that runs `applyTM M`
more than once has to restore them between calls — that is what the
precondition below demands. -/
def applyTM (M : TM k) : TM (k + 2) := (retargetInputStarted M).retargetOutput

/-- The parked blank tape every scratch tape starts and ends at. -/
def parkedBlank : Tape := (Tape.init []).move Dir3.right

/-- The tapes `applyTM M` expects at entry: `M`'s scratch blank, the virtual
input holding `y`, the result tape blank. -/
def applyPre (M : TM k) (y : List Bool) (realInput : Tape) :
    Fin (k + 2) → Tape :=
  Fin.snoc (retargetInputStartedCfg M y realInput).work parkedBlank

/-- **The contract of the work-to-work evaluator.** Given `M`'s own time bound,
`applyTM M` halts within that bound with `f y` on its result tape — provided
`M`'s scratch tapes were blank, work tape `k` held `y`, and the result tape was
blank. -/
theorem applyTM_hoareTime (M : TM k) {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) :
    (applyTM M).HoareTime
      (fun inp work out =>
        ((fun i : Fin (k + 1) => work (Fin.castSucc i))
          = (retargetInputStartedCfg M y inp).work) ∧
        work (Fin.last (k + 1)) = parkedBlank ∧
        out = parkedBlank)
      (fun _inp work out =>
        (work (Fin.last (k + 1))).HasOutput (f y) ∧ out = parkedBlank)
      (T y.length) := by
  have h := retargetOutput_hoareTime (retargetInputStarted M)
    (retargetInputStarted_hoareTime M hcomp y)
  intro inp work out hpre
  obtain ⟨h1, h2, h3⟩ := hpre
  exact h inp work out ⟨⟨h1, h2⟩, h3⟩

/-- The entry tapes do satisfy the entry condition. -/
theorem applyPre_spec (M : TM k) (y : List Bool) (realInput : Tape) :
    ((fun i : Fin (k + 1) => applyPre M y realInput (Fin.castSucc i))
      = (retargetInputStartedCfg M y realInput).work) ∧
    applyPre M y realInput (Fin.last (k + 1)) = parkedBlank := by
  refine ⟨funext fun i => ?_, ?_⟩
  · rw [applyPre, Fin.snoc_castSucc]
  · rw [applyPre, Fin.snoc_last]

/-! ## Embedding a Hoare triple in a larger tape space

`iterate_mem_FP`'s machine runs several sub-machines (computing `init`,
`ruler`, `width`, `F`, …) that each own a fixed number of work tapes, inside
one composite machine that also carries persistent state (the running
iterate, fuel registers) on tapes those sub-machines never touch.
`TM.placeWorkTM` already gives the exact frame-preserving simulation
(`placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant`); this section turns
that into a Hoare-triple-level tool, so each embedding is a single lemma
application instead of a fresh `reachesIn` argument. -/

/-- **Placing a Hoare triple.** If `tm : TM n` satisfies a Hoare triple, then
`placeWorkTM pre post tm` satisfies the triple obtained by reindexing `tm`'s
work-tape predicate through the middle block, with an arbitrary `Parked`-style
frame (`extras`) held exactly fixed outside it. -/
theorem placeWorkTM_hoareTime_frame {n pre post : ℕ} (tm : TM n)
    {preSmall postSmall : TapePred n} {b : ℕ}
    (h : tm.HoareTime preSmall postSmall b)
    (extras : Fin (pre + n + post) → Tape)
    (hinv : ∀ i, ¬placeWorkInMiddle pre n i → Tape.StartInvariant (extras i))
    (hhead : ∀ i, ¬placeWorkInMiddle pre n i → 1 ≤ (extras i).head) :
    (placeWorkTM pre post tm).HoareTime
      (fun inp work out => preSmall inp (fun i => work (placeWorkIdx pre post i)) out ∧
        ∀ i, ¬placeWorkInMiddle pre n i → work i = extras i)
      (fun inp work out => postSmall inp (fun i => work (placeWorkIdx pre post i)) out ∧
        ∀ i, ¬placeWorkInMiddle pre n i → work i = extras i)
      b := by
  rintro inp work out ⟨hpre, hextra⟩
  set wSmall : Fin n → Tape := fun i => work (placeWorkIdx pre post i) with hwSmall
  obtain ⟨c', t, ht, hreach, hhalt, hpost⟩ := h inp wSmall out hpre
  have hweq : work = (placeWorkCfg tm pre post extras
      { state := tm.qstart, input := inp, work := wSmall, output := out }).work := by
    funext i
    by_cases hmid : placeWorkInMiddle pre n i
    · rw [show i = placeWorkIdx pre post (placeWorkCoord pre n i hmid) from
        (placeWorkIdx_placeWorkCoord i hmid).symm, placeWorkCfg_work_middle]
    · rw [placeWorkCfg_work_extra tm pre post extras _ i hmid]
      exact hextra i hmid
  refine ⟨placeWorkCfg tm pre post extras c', t, ht, ?_,
    (placeWorkCfg_halted_iff tm pre post extras c').mpr hhalt, ?_, ?_⟩
  · rw [hweq]
    exact placeWorkTM_reachesIn_placeWorkCfg_of_startInvariant tm pre post extras hreach
      hinv hhead
  · show postSmall c'.input (fun i => (placeWorkCfg tm pre post extras c').work
      (placeWorkIdx pre post i)) c'.output
    simp only [placeWorkCfg_work_middle]
    exact hpost
  · intro i hi
    exact placeWorkCfg_work_extra tm pre post extras c' i hi

/-! ## What a bounded run can have disturbed

Resetting an opaque `FP` witness machine's scratch tapes between calls needs
to know *how far out* the machine could possibly have written. Since each head
moves by at most one cell per step and a machine only ever writes under its
heads, a `t`-step run leaves every cell beyond `head + t` exactly as it found
it. That is what makes the bounded wipe of `TM.resetTapesTM` complete rather
than merely partial. -/

/-- One step leaves every work-tape cell other than that tape's own head
unchanged: a machine writes only under its heads. -/
theorem work_cells_ne_of_step {n : ℕ} {tm : TM n} {c c' : Cfg n tm.Q}
    (hstep : tm.step c = some c') (i : Fin n) {j : ℕ} (hj : j ≠ (c.work i).head) :
    (c'.work i).cells j = (c.work i).cells j := by
  simp only [TM.step] at hstep
  split at hstep
  · simp at hstep
  · simp only [Option.some.injEq] at hstep
    rw [← hstep]
    simp only [Tape.move_cells, Tape.write]
    split
    · rfl
    · change Function.update (c.work i).cells (c.work i).head _ j = (c.work i).cells j
      rw [Function.update_of_ne hj]

/-- **Cells beyond a work head's maximum reach are never touched.** -/
theorem reachesIn_work_cells_far {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      ∀ (i : Fin n) (j : ℕ), (c.work i).head + t < j →
        (c'.work i).cells j = (c.work i).cells j := by
  intro t
  induction t with
  | zero =>
      intro c c' hreach i j _
      cases hreach
      rfl
  | succ t ih =>
      intro c c' hreach i j hj
      cases hreach with
      | step hstep hrest =>
          next c'' =>
            have hhead : (c''.work i).head ≤ (c.work i).head + 1 :=
              (head_le_start_add_of_reachesIn tm (TM.reachesIn.step hstep TM.reachesIn.zero)).2.2 i
            have hcell : (c''.work i).cells j = (c.work i).cells j :=
              work_cells_ne_of_step hstep i (by omega)
            rw [ih hrest i j (by omega), hcell]

/-- The standing left-marker invariant survives an entire run, on every tape. -/
theorem reachesIn_startInvariant {n : ℕ} {tm : TM n} :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' →
      c.input.StartInvariant → (∀ i, (c.work i).StartInvariant) → c.output.StartInvariant →
      c'.input.StartInvariant ∧ (∀ i, (c'.work i).StartInvariant) ∧
        c'.output.StartInvariant := by
  intro t c c' hreach
  induction hreach with
  | zero => exact fun hi hw ho => ⟨hi, hw, ho⟩
  | step hstep _ ih =>
      intro hi hw ho
      obtain ⟨hi', hw', ho'⟩ := Tape.StartInvariant.step _ hstep hi hw ho
      exact ih hi' hw' ho'

/-- A fully parked tape frame passes through a combinator seam unchanged —
the boundary obligation of `TM.seqTM_hoareTime` in the common case where every
tape is parked on both sides of the seam. -/
theorem parked_transition {n : ℕ} {inp₀ out₀ : Tape} {W : Fin n → Tape}
    (hinp : Parked inp₀) (hW : ∀ i, Parked (W i)) (hout : Parked out₀) :
    transitionInput inp₀ = inp₀ ∧
      (fun i => transitionTape (W i)) = W ∧ transitionTape out₀ = out₀ :=
  ⟨transitionInput_eq_self hinp.read_ne_start,
    funext fun i => transitionTape_eq_self (hW i).read_ne_start,
    transitionTape_eq_self hout.read_ne_start⟩

/-- **Chaining two fully-determined phases.** When each phase pins down the
entire tape family and every intermediate tape is parked, sequential
composition needs no boundary reasoning at all. -/
theorem seqTM_det {n : ℕ} (m₁ m₂ : TM n) {inp₀ out₀ : Tape} {W₀ W₁ W₂ : Fin n → Tape}
    {b₁ b₂ : ℕ} (hinp : Parked inp₀) (hout : Parked out₀) (hW₁ : ∀ i, Parked (W₁ i))
    (h₁ : m₁.HoareTime (fun inp work out => inp = inp₀ ∧ work = W₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = out₀) b₁)
    (h₂ : m₂.HoareTime (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₂ ∧ out = out₀) b₂) :
    (seqTM m₁ m₂).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = W₂ ∧ out = out₀)
      (b₁ + 1 + b₂) := by
  refine seqTM_hoareTime m₁ m₂ h₁ ?_ h₂
  rintro inp work out ⟨rfl, rfl, rfl⟩
  exact parked_transition hinp hW₁ hout

/-- A machine that never moves its real input head off a parked position: its
transition function always returns `idleDir` for the input tape. Machines that
read their input from a work tape instead (`TM.retargetInput` and everything
built on it) satisfy this. -/
def IdlesInput {n : ℕ} (tm : TM n) : Prop :=
  ∀ q iHead wHeads oHead, (tm.δ q iHead wHeads oHead).2.2.2.1 = idleDir iHead

/-- An input-idling machine preserves a parked real input tape exactly, for
any number of steps. -/
theorem reachesIn_input_eq_of_idlesInput {n : ℕ} {tm : TM n} (hidle : IdlesInput tm) :
    ∀ {t : ℕ} {c c' : Cfg n tm.Q}, tm.reachesIn t c c' → Parked c.input →
      c'.input = c.input := by
  intro t
  induction t with
  | zero =>
      intro c c' hreach _
      cases hreach
      rfl
  | succ t ih =>
      intro c c' hreach hp
      cases hreach with
      | step hstep hrest =>
          next c'' =>
            have hc'' : c''.input = c.input := by
              simp only [TM.step] at hstep
              split at hstep
              · simp at hstep
              · simp only [Option.some.injEq] at hstep
                rw [← hstep]
                show c.input.move _ = c.input
                rw [hidle, hp.move_idle]
            rw [ih hrest (by rw [hc'']; exact hp), hc'']

/-- The work-to-work evaluator reads its input from a work tape, so it idles
the real input head. -/
theorem applyTM_idlesInput (M : TM k) : IdlesInput (applyTM M) := fun _ _ _ _ => rfl

/-- Every entry tape of the work-to-work evaluator is parked at cell `1`. -/
theorem applyPre_head (M : TM k) (y : List Bool) (realInput : Tape) (i : Fin (k + 2)) :
    (applyPre M y realInput i).head = 1 := by
  refine Fin.lastCases ?_ ?_ i
  · rw [applyPre, Fin.snoc_last]; rfl
  · intro i'
    rw [applyPre, Fin.snoc_castSucc]
    show ((retargetInputStartedCfg M y realInput).work i').head = 1
    rw [retargetInputStartedCfg]
    dsimp only
    split <;> rfl

/-- The blank tape satisfies the left-marker invariant. -/
theorem startInvariant_initNil : Tape.StartInvariant (Tape.init ([] : List Γ)) := by
  refine ⟨Tape.init_cells_zero [], fun j hj => ?_⟩
  rw [show j = (j - 1) + 1 from by omega, Tape.init_cells_ge [] (j - 1) (by simp)]
  decide

/-- A tape initialized with a Boolean string satisfies the left-marker
invariant: `Γ.ofBool` never produces `▷`. -/
theorem startInvariant_initOfBool (y : List Bool) :
    Tape.StartInvariant (Tape.init (y.map Γ.ofBool)) := by
  refine ⟨Tape.init_cells_zero _, fun j hj => ?_⟩
  have hj1 : j = (j - 1) + 1 := by omega
  by_cases hlt : j - 1 < y.length
  · rw [hj1, Tape.init_ofBool_cells_lt y (j - 1) hlt]
    cases y[j - 1]'hlt <;> decide
  · rw [hj1, Tape.init_ofBool_cells_ge y (j - 1) (by omega)]
    decide

/-- Every entry tape of the work-to-work evaluator satisfies the left-marker
invariant. -/
theorem applyPre_startInvariant (M : TM k) (y : List Bool) (realInput : Tape)
    (i : Fin (k + 2)) : Tape.StartInvariant (applyPre M y realInput i) := by
  refine Fin.lastCases ?_ ?_ i
  · rw [applyPre, Fin.snoc_last]
    show Tape.StartInvariant ((Tape.init ([] : List Γ)).move Dir3.right)
    exact startInvariant_initNil.move Dir3.right
  · intro i'
    rw [applyPre, Fin.snoc_castSucc]
    show Tape.StartInvariant ((retargetInputStartedCfg M y realInput).work i')
    rw [retargetInputStartedCfg]
    dsimp only
    split
    · exact startInvariant_initNil.move Dir3.right
    · exact (startInvariant_initOfBool y).move Dir3.right

/-- Every entry tape of the work-to-work evaluator is blank beyond the virtual
input's length. -/
theorem applyPre_cells_blank (M : TM k) (y : List Bool) (realInput : Tape)
    (i : Fin (k + 2)) (j : ℕ) (hj : y.length < j) :
    (applyPre M y realInput i).cells j = Γ.blank := by
  have hj0 : j = (j - 1) + 1 := by omega
  refine Fin.lastCases ?_ ?_ i
  · rw [applyPre, Fin.snoc_last]
    show ((Tape.init ([] : List Γ)).move Dir3.right).cells j = Γ.blank
    rw [Tape.move_cells, hj0, Tape.init_cells_ge [] (j - 1) (by simp)]
  · intro i'
    rw [applyPre, Fin.snoc_castSucc]
    show ((retargetInputStartedCfg M y realInput).work i').cells j = Γ.blank
    rw [retargetInputStartedCfg]
    dsimp only
    split
    · show ((Tape.init ([] : List Γ)).move Dir3.right).cells j = Γ.blank
      rw [Tape.move_cells, hj0, Tape.init_cells_ge [] (j - 1) (by simp)]
    · show ((Tape.init (y.map Γ.ofBool)).move Dir3.right).cells j = Γ.blank
      rw [Tape.move_cells, hj0,
        Tape.init_cells_ge (y.map Γ.ofBool) (j - 1) (by simp only [List.length_map]; omega)]

/-- **The work-to-work evaluator, with its disturbance framed.** Beyond
computing `f y` onto the result tape, this records the two facts a caller needs
in order to reset the machine for a second call: every tape's head is still
within `H`, and every cell beyond `H` is still blank. Both follow from the run
being `T |y|`-bounded and every entry tape being parked and blank past `|y|`. -/
theorem applyTM_hoareTime_frame (M : TM k) {f : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime f T) (y : List Bool) (inp₀ : Tape) (hinp : Parked inp₀)
    (hinpSI : Tape.StartInvariant inp₀)
    (H : ℕ) (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H) :
    (applyTM M).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = applyPre M y inp₀ ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work (Fin.last (k + 1))).HasOutput (f y) ∧
        ∀ i, Tape.StartInvariant (work i) ∧ (work i).head ≤ H ∧
          ∀ j, H < j → (work i).cells j = Γ.blank)
      (T y.length) := by
  intro inp work out hpre
  obtain ⟨hi, hw, ho⟩ := hpre
  rw [hi, hw, ho]
  obtain ⟨c', t, ht, hreach, hhalt, hOut, hOutEq⟩ :=
    applyTM_hoareTime M hcomp y inp₀ (applyPre M y inp₀) parkedBlank
      ⟨(applyPre_spec M y inp₀).1, (applyPre_spec M y inp₀).2, rfl⟩
  have hinpEq : c'.input = inp₀ :=
    reachesIn_input_eq_of_idlesInput (applyTM_idlesInput M) hreach hinp
  have hSI := reachesIn_startInvariant hreach hinpSI
    (fun i => applyPre_startInvariant M y inp₀ i)
    (show Tape.StartInvariant parkedBlank from startInvariant_initNil.move Dir3.right)
  refine ⟨c', t, ht, hreach, hhalt, hinpEq, hOutEq, hOut,
    fun i => ⟨hSI.2.1 i, ?_, fun j hj => ?_⟩⟩
  · have hh := (head_le_start_add_of_reachesIn (applyTM M) hreach).2.2 i
    rw [show ((⟨(applyTM M).qstart, inp₀, applyPre M y inp₀, parkedBlank⟩ :
      Cfg (k + 2) (applyTM M).Q).work i).head = 1 from applyPre_head M y inp₀ i] at hh
    omega
  · rw [reachesIn_work_cells_far hreach i j
      (by rw [applyPre_head M y inp₀ i]; omega)]
    exact applyPre_cells_blank M y inp₀ i j (by omega)

end TM

/-! ## Turning a bit test into a length

Everything `FP` already offers — `Complexity.takeLen`, `Complexity.reverse`,
`Complexity.pair`, `Cobham.mulUnpair` — determines its output *length* from its
inputs' lengths alone, so none of it can branch on a bit's **value**. The two
machines below close that gap: they return a one-bit string exactly when the
input starts with the given bit, so a value test becomes a length, which
`takeLen` and `mulUnpair` then propagate. -/

section HeadFlag

open Complexity.TM

/-- Control states of the head-bit flag machine. -/
inductive HeadPhase where
  /-- Advance past the left-end markers. -/
  | skip
  /-- Read the first input bit. -/
  | test
  /-- Halted. -/
  | done
  deriving DecidableEq

instance instFintypeHeadPhase : Fintype HeadPhase where
  elems := {.skip, .test, .done}
  complete := fun p => by cases p <;> simp

/-- `[false]` when `x` begins with `target`, and `[]` otherwise: a bit test whose
answer is carried by the *length* of the result. -/
def headFlag (target : Bool) (x : List Bool) : List Bool :=
  if x.head? = some target then [false] else []

/-- Read the first input bit and emit one output bit exactly when it is
`target`. Two steps: `skip` moves off the left-end markers, `test` reads the bit
and either writes or not. -/
def headFlagTM (target : Bool) : TM 0 where
  Q := HeadPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.test, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .test =>
        if iHead = Γ.ofBool target then
          (.done, fun i => readBackWrite (wHeads i), Γw.zero, idleDir iHead,
            fun i => idleDir (wHeads i), Dir3.right)
        else
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .test =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- Writing back the symbol already under the head changes nothing. -/
private theorem write_read_self' (t : Tape) : t.write t.read = t := by
  rw [Tape.write]
  split
  · rfl
  · exact Tape.ext rfl (Function.update_eq_self _ _)

/-- The input's first cell after the marker holds the first bit, or blank. -/
private theorem headFlagTM_read (x : List Bool) :
    ((Tape.init (x.map Γ.ofBool)).move Dir3.right).read
      = (x.head?).elim Γ.blank Γ.ofBool := by
  cases x with
  | nil => simp [Tape.read, Tape.move, Tape.init]
  | cons a t => cases a <;> simp [Tape.read, Tape.move, Tape.init, Γ.ofBool]

/-- `headFlagTM target` computes `headFlag target` in two steps. -/
theorem headFlagTM_computesInTime (target : Bool) :
    (headFlagTM target).ComputesInTime (headFlag target) (fun _ => 2) := by
  intro x
  let c1 : Cfg 0 (headFlagTM target).Q :=
    { state := HeadPhase.test
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).writeAndMove
        (readBackWrite (Tape.init []).read) (idleDir (Tape.init []).read)
      output := (Tape.init []).move Dir3.right }
  have hstep1 : (headFlagTM target).step ((headFlagTM target).initCfg x) = some c1 := by
    simp [TM.step, headFlagTM, c1, Tape.read, Tape.init, idleDir, Tape.writeAndMove,
      Tape.write, Tape.move]
  have hread : c1.input.read = (x.head?).elim Γ.blank Γ.ofBool :=
    headFlagTM_read x
  by_cases hb : x.head? = some target
  · -- The bit matches: one output cell is written.
    have hri : c1.input.read = Γ.ofBool target := by rw [hread, hb]; rfl
    let c2 : Cfg 0 (headFlagTM target).Q :=
      { state := HeadPhase.done
        input := c1.input.move (idleDir c1.input.read)
        work := fun i => (c1.work i).writeAndMove
          (readBackWrite (c1.work i).read) (idleDir (c1.work i).read)
        output := c1.output.writeAndMove Γw.zero.toΓ Dir3.right }
    have hstep2 : (headFlagTM target).step c1 = some c2 := by
      simp [TM.step, headFlagTM, c1, c2, hri]
    refine ⟨c2, 2, le_rfl, .step hstep1 (.step hstep2 .zero), rfl, ?_⟩
    rw [headFlag, if_pos hb]
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp [c2, c1, Tape.write, Tape.move, Tape.init, Γw.toΓ, Γ.ofBool]
    · simp [c2, c1, Tape.write, Tape.move, Tape.init, Γw.toΓ]
  · -- The bit does not match: nothing is written.
    have hri : c1.input.read ≠ Γ.ofBool target := by
      rw [hread]
      cases hx : x.head? with
      | none => cases target <;> simp [Γ.ofBool]
      | some a =>
          rw [hx] at hb
          simp only [Option.elim]
          cases a <;> cases target <;> simp_all [Γ.ofBool]
    let c2 : Cfg 0 (headFlagTM target).Q :=
      { state := HeadPhase.done
        input := c1.input.move (idleDir c1.input.read)
        work := fun i => (c1.work i).writeAndMove
          (readBackWrite (c1.work i).read) (idleDir (c1.work i).read)
        output := c1.output.writeAndMove (readBackWrite c1.output.read).toΓ
          (idleDir c1.output.read) }
    have hstep2 : (headFlagTM target).step c1 = some c2 := by
      simp [TM.step, headFlagTM, c1, c2, hri]
    refine ⟨c2, 2, le_rfl, .step hstep1 (.step hstep2 .zero), rfl, ?_⟩
    rw [headFlag, if_neg hb]
    refine ⟨fun i hi => by simp at hi, ?_⟩
    have hoc : c1.output.read = Γ.blank := by
      simp [c1, Tape.read, Tape.move, Tape.init]
    have hcells : c2.output.cells = c1.output.cells := by
      show ((c1.output.write ((readBackWrite c1.output.read).toΓ)).move
        (idleDir c1.output.read)).cells = c1.output.cells
      rw [Tape.move_cells,
        show (readBackWrite c1.output.read).toΓ = c1.output.read from by rw [hoc]; rfl,
        write_read_self']
    rw [hcells]
    simp [c1, Tape.move, Tape.init]

/-- **A bit test, as a length.** -/
theorem headFlag_mem_FP (target : Bool) : headFlag target ∈ FP :=
  ⟨1, 0, headFlagTM target, (fun _ => 2), headFlagTM_computesInTime target,
    BigO.const_le_pow 2 1⟩

end HeadFlag

/-! ## An unconditional, content-agnostic wipe step

`Cobham.recFoldClamp_mem_FP`'s loop needs to run an arbitrary `FP` witness
machine `M` more than once, reusing the same scratch tapes. Between calls
those tapes must be genuinely blank (`M`'s own `initCfg` assumes it), but `M`
is an arbitrary machine from an existential `F ∈ FP` — nothing says its
scratch is left in a "clean, single blank-terminated prefix" shape the way
this library's own hand-built scanners (`blankWorkTM`, `clearWorkTM`, …) are.
A machine that writes cell `5` then later cell `3` without revisiting cell
`4` leaves a *gap*: an isolated blank cell with more nonblank content beyond
it. Content-driven scanners (`blankWorkTM` scans right until the *first*
blank) stop at such a gap and under-wipe.

`wipeStepTM` sidesteps this: one step writes `Γ.blank` to every targeted tape
and advances its head, unconditionally — it never reads the targeted tapes'
content to decide anything. Iterated a known number of times (via
`TM.forRegTM`, driven by a *separate* fuel register unrelated to the wiped
tapes' content) it blanks an exact number of cells regardless of what was
there. -/

section WipeStep

open Complexity.TM

/-- Control states of the unconditional wipe-step machine. -/
inductive WipeStepPhase where
  /-- Write blank to every targeted tape and advance; then halt. -/
  | running
  /-- Halted. -/
  | done
  deriving DecidableEq

instance instFintypeWipeStepPhase : Fintype WipeStepPhase where
  elems := {.running, .done}
  complete := fun p => by cases p <;> simp

/-- One unconditional step: every work tape named in `targets` is written
`Γ.blank` and its head advances right; every other work tape, the input, and
the output are held by `readBackWrite`/`idleDir`. Does not inspect the
targeted tapes' contents at all. -/
def wipeStepTM {n : ℕ} (targets : List (Fin n)) : TM n where
  Q := WipeStepPhase
  qstart := .running
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .running =>
        (.done,
          fun i => if i ∈ targets then Γw.blank else readBackWrite (wHeads i),
          readBackWrite oHead, idleDir iHead,
          fun i => if i ∈ targets then Dir3.right else idleDir (wHeads i),
          idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .running =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only
        split
        · rfl
        · exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- **`wipeStepTM`'s exact one-step Hoare contract.** From tapes where every
non-targeted work tape, the input, and the output are `Parked`, one step
unconditionally blanks and advances every targeted work tape and preserves
everything else exactly. -/
theorem wipeStepTM_hoareTime {n : ℕ} (targets : List (Fin n))
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hout : Parked out₀)
    (hother : ∀ i, i ∉ targets → Parked (work₀ i)) :
    (wipeStepTM targets).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        ∀ i, work i = if i ∈ targets then (work₀ i).writeAndMove Γw.blank.toΓ Dir3.right
          else work₀ i)
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨(⟨WipeStepPhase.done,
      inp.move (idleDir inp.read),
      (fun i => if i ∈ targets then (work i).writeAndMove Γw.blank.toΓ Dir3.right
        else (work i).writeAndMove (readBackWrite (work i).read) (idleDir (work i).read)),
      out.writeAndMove (readBackWrite out.read) (idleDir out.read)⟩ :
      Cfg n (wipeStepTM targets).Q),
    1, le_refl 1, ?_, rfl, hinp.move_idle, hout.writeAndMove_readBack_idle, fun i => ?_⟩
  · refine TM.reachesIn.step ?_ .zero
    simp only [TM.step, wipeStepTM,
      if_neg (show WipeStepPhase.running ≠ WipeStepPhase.done by decide)]
    congr 1
    congr 1
    funext i
    split <;> rfl
  · dsimp only
    split
    · rfl
    · next hi => exact (hother i hi).writeAndMove_readBack_idle

end WipeStep

/-! ## Moving left unconditionally

Before an opaque `FP` witness machine's scratch tapes can be safely wiped
(`wipeStepTM` scans strictly rightward from the current head), every one of
them first needs its head brought back to a *known* position. Since the
`▷` marker at cell `0` is immutable, moving left far enough always reaches
it regardless of current content — `moveLeftStepTM`, run enough times, is a
content-agnostic bulk rewind for a whole list of tapes at once, exactly as
`wipeStepTM` is a content-agnostic bulk wipe. -/

section MoveLeftStep

open Complexity.TM

/-- Unconditional write-then-move collapses to a pure move whenever the
tape's only possible `▷` is at cell `0` — regardless of whether the head is
currently on it. -/
theorem writeAndMove_readBack_of_startInvariant (t : Tape) (h : Tape.StartInvariant t)
    (d : Dir3) : t.writeAndMove (readBackWrite t.read) d = t.move d := by
  by_cases hh : t.head = 0
  · show (t.write _).move d = t.move d
    congr 1
    rw [Tape.write, if_pos hh]
  · exact writeAndMove_readBack t (h.read_ne_start (by omega)) d

/-- One unconditional step: every work tape named in `targets` moves left
(bouncing off `▷` via `moveLeftDir`); every other work tape, the input, and
the output are held by `readBackWrite`/`idleDir`. Content is always preserved. -/
def moveLeftStepTM {n : ℕ} (targets : List (Fin n)) : TM n where
  Q := WipeStepPhase
  qstart := .running
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .running =>
        (.done,
          fun i => readBackWrite (wHeads i),
          readBackWrite oHead, idleDir iHead,
          fun i => if i ∈ targets then moveLeftDir (wHeads i) else idleDir (wHeads i),
          idleDir oHead)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .running =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only
        split
        · exact moveLeftDir_right_of_start hi
        · exact idleDir_right_of_start hi
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- **`moveLeftStepTM`'s exact one-step Hoare contract.** Targeted tapes need
only `StartInvariant` (their `▷`, if any, is at cell `0` — true regardless of
current head position); every other work tape, the input, and the output
must be `Parked`. -/
theorem moveLeftStepTM_hoareTime {n : ℕ} (targets : List (Fin n))
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Parked inp₀) (hout : Parked out₀)
    (htarget : ∀ i, i ∈ targets → Tape.StartInvariant (work₀ i))
    (hother : ∀ i, i ∉ targets → Parked (work₀ i)) :
    (moveLeftStepTM targets).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        ∀ i, work i = if i ∈ targets then (work₀ i).move (moveLeftDir (work₀ i).read)
          else work₀ i)
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨(⟨WipeStepPhase.done,
      inp.move (idleDir inp.read),
      (fun i => if i ∈ targets then (work i).move (moveLeftDir (work i).read)
        else (work i).writeAndMove (readBackWrite (work i).read) (idleDir (work i).read)),
      out.writeAndMove (readBackWrite out.read) (idleDir out.read)⟩ :
      Cfg n (moveLeftStepTM targets).Q),
    1, le_refl 1, ?_, rfl, hinp.move_idle, hout.writeAndMove_readBack_idle, fun i => ?_⟩
  · refine TM.reachesIn.step ?_ .zero
    simp only [TM.step, moveLeftStepTM,
      if_neg (show WipeStepPhase.running ≠ WipeStepPhase.done by decide)]
    congr 1
    congr 1
    funext i
    by_cases hi : i ∈ targets
    · simp only [if_pos hi]
      exact writeAndMove_readBack_of_startInvariant (work i) (htarget i hi) _
    · simp only [if_neg hi]
  · dsimp only
    split
    · rfl
    · next hi => exact (hother i hi).writeAndMove_readBack_idle

end MoveLeftStep

/-! ## The wipe loop

`forRegTM` already drives a body an exact input-independent number of times
off a dedicated unary fuel register; running `wipeStepTM targets` through it,
fueled by a register holding `v` marks unrelated to any of the wiped tapes'
content, blanks the leading `v` cells of every tape in `targets` regardless of
what was there — the content-agnostic bulk wipe the loop of `iterate_mem_FP`
needs between calls to an opaque `FP` witness machine. -/

section WipeLoop

open Complexity.TM

/-- Wipe-step applied `i` times to `t`, in closed form. -/
def wipedTape (t : Tape) (i : ℕ) : Tape :=
  (fun s : Tape => s.writeAndMove Γw.blank.toΓ Dir3.right)^[i] t

@[simp] theorem wipedTape_zero (t : Tape) : wipedTape t 0 = t := rfl

theorem wipedTape_succ (t : Tape) (i : ℕ) :
    wipedTape t (i + 1) = (wipedTape t i).writeAndMove Γw.blank.toΓ Dir3.right :=
  Function.iterate_succ_apply' _ i t

/-- Wiping advances the head one cell per step. -/
theorem wipedTape_head (t : Tape) (i : ℕ) : (wipedTape t i).head = t.head + i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [wipedTape_succ]
      show (((wipedTape t i).write Γw.blank.toΓ).move Dir3.right).head = t.head + (i + 1)
      rw [show (((wipedTape t i).write Γw.blank.toΓ).move Dir3.right).head
            = ((wipedTape t i).write Γw.blank.toΓ).head + 1 from rfl,
        Tape.write_head, ih]
      omega

/-- **What wiping does.** From a head parked at cell `1`, wiping `H` times
blanks exactly cells `1 … H` and leaves every other cell alone. -/
theorem wipedTape_cells_of_head_one {t : Tape} (hh : t.head = 1) (H j : ℕ) :
    (wipedTape t H).cells j = if 1 ≤ j ∧ j ≤ H then Γ.blank else t.cells j := by
  induction H with
  | zero => rw [wipedTape_zero, if_neg (by omega : ¬(1 ≤ j ∧ j ≤ 0))]
  | succ H ih =>
      have hheadH : (wipedTape t H).head = H + 1 := by rw [wipedTape_head, hh]; omega
      rw [wipedTape_succ]
      show (((wipedTape t H).write Γw.blank.toΓ).move Dir3.right).cells j = _
      rw [Tape.move_cells, Tape.write, if_neg (by rw [hheadH]; omega)]
      show Function.update (wipedTape t H).cells (wipedTape t H).head Γw.blank.toΓ j = _
      rw [hheadH]
      by_cases hj : j = H + 1
      · rw [hj, Function.update_self, if_pos ⟨by omega, by omega⟩]
        rfl
      · rw [Function.update_of_ne hj, ih]
        by_cases hc : 1 ≤ j ∧ j ≤ H
        · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
        · have hc' : ¬(1 ≤ j ∧ j ≤ H + 1) := by
            rintro ⟨h1, h2⟩
            exact hc ⟨h1, by omega⟩
          rw [if_neg hc, if_neg hc']

/-- The canonical blank tape's cells, spelled out. -/
theorem initNil_cells (j : ℕ) :
    (Tape.init ([] : List Γ)).cells j = if j = 0 then Γ.start else Γ.blank := by
  cases j with
  | zero => exact Tape.init_cells_zero []
  | succ i => rw [Tape.init_cells_ge [] i (by simp), if_neg (Nat.succ_ne_zero i)]

/-- **Wiping really blanks the tape.** A tape parked at cell `1` whose content
is confined to cells `1 … H` becomes literally the blank tape (head at `H + 1`)
after `H` wipe steps — this is where the content-agnostic wipe pays off: no
assumption is made about *where* inside `1 … H` the nonblank cells sit. -/
theorem wipedTape_eq_blank {t : Tape} (H : ℕ) (hh : t.head = 1)
    (h0 : t.cells 0 = Γ.start) (hfar : ∀ j, H < j → t.cells j = Γ.blank) :
    wipedTape t H = (⟨H + 1, (Tape.init ([] : List Γ)).cells⟩ : Tape) := by
  refine Tape.ext (by rw [wipedTape_head, hh]; show 1 + H = H + 1; omega) (funext fun j => ?_)
  rw [wipedTape_cells_of_head_one hh, initNil_cells]
  by_cases hj0 : j = 0
  · rw [hj0, if_neg (by omega : ¬(1 ≤ 0 ∧ 0 ≤ H)), if_pos rfl, h0]
  · rw [if_neg hj0]
    by_cases hc : 1 ≤ j ∧ j ≤ H
    · rw [if_pos hc]
    · rw [if_neg hc, hfar j (by omega)]

/-- Wiping preserves `Parked`-ness: the head only advances, and every
written or untouched cell beyond the marker stays off `▷`. -/
theorem wipedTape_parked {t : Tape} (h : Parked t) (i : ℕ) : Parked (wipedTape t i) := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rw [wipedTape_succ]
      have hheq : (wipedTape t i).writeAndMove Γw.blank.toΓ Dir3.right =
          ((wipedTape t i).write Γw.blank.toΓ).move Dir3.right := rfl
      have hhead_ne : (wipedTape t i).head ≠ 0 := by
        have := ih.1; omega
      refine ⟨?_, fun j hj => ?_⟩
      · rw [hheq]
        show 1 ≤ ((wipedTape t i).write Γw.blank.toΓ).head + 1
        omega
      · rw [hheq, Tape.move_cells]
        simp only [Tape.write, if_neg hhead_ne]
        show Function.update (wipedTape t i).cells (wipedTape t i).head Γw.blank.toΓ j ≠ Γ.start
        by_cases hje : j = (wipedTape t i).head
        · rw [hje, Function.update_self]; decide
        · rw [Function.update_of_ne hje]; exact ih.2 j hj

/-- A fresh output tape (`(Tape.init []).move Dir3.right`) is `Parked`. -/
theorem parked_parkedBlank : Parked ((Tape.init []).move Dir3.right) := by
  refine ⟨le_refl 1, fun j hj => ?_⟩
  rw [Tape.move_cells, show j = (j - 1) + 1 from by omega,
    Tape.init_cells_ge [] (j - 1) (by simp)]
  decide

/-- A fresh output tape satisfies the empty output accumulator. -/
theorem outAcc_nil_of_parkedBlank :
    OutAcc [] ((Tape.init []).move Dir3.right) := by
  refine ⟨rfl, ?_, nofun, fun j hj => ?_⟩
  · rw [Tape.move_cells]; exact Tape.init_cells_zero []
  · rw [Tape.move_cells, show j = (j - 1) + 1 from by omega,
      Tape.init_cells_ge [] (j - 1) (by simp)]

/-- The only tape satisfying the empty output accumulator is the fresh
parked blank tape. -/
theorem eq_parkedBlank_of_outAcc_nil {t : Tape} (h : OutAcc [] t) :
    t = (Tape.init []).move Dir3.right := by
  obtain ⟨hhead, hcell0, -, htail⟩ := h
  refine Tape.ext ?_ ?_
  · rw [hhead]; rfl
  · rw [Tape.move_cells]
    funext j
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0; rw [hcell0, Tape.init_cells_zero]
    · rw [htail j (by simpa using hj1), show j = (j - 1) + 1 from by omega,
        Tape.init_cells_ge [] (j - 1) (by simp)]

/-- The register-shaped tape at iteration `i` is `Parked`. -/
theorem regIterCells_parked (v i : ℕ) : Parked (⟨i + 2, regCells v⟩ : Tape) := by
  refine ⟨show 1 ≤ i + 2 by omega, fun j _ => ?_⟩
  show regCells v j ≠ Γ.start
  simp only [regCells]
  split
  · omega
  · split <;> decide

/-- **The wipe loop.** Fueled by a register at `r` holding `v` marks (`r`
disjoint from `targets`), `forRegTM (wipeStepTM targets) r` blanks the leading
`v` cells of every tape in `targets`, leaving every other tape — including the
fuel register itself — exactly as it was. -/
theorem wipeLoop_hoareTime {n : ℕ} (targets : List (Fin n)) (r : Fin n)
    (hr : r ∉ targets) (v : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape)
    (hinp₀ : Parked inp₀)
    (hother : ∀ j, j ≠ r → Parked (work₀ j)) :
    (forRegTM (wipeStepTM targets) r).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update work₀ r (regTape v) ∧
        out = (Tape.init []).move Dir3.right)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update
          (fun j => if j ∈ targets then wipedTape (work₀ j) v else work₀ j) r (regTape v) ∧
        out = (Tape.init []).move Dir3.right)
      (v * 3 + (v + 2)) := by
  set w : ℕ → Fin n → Tape := fun i j =>
    if j = r then regTape v else if j ∈ targets then wipedTape (work₀ j) i else work₀ j
    with hw
  have hw0 : w 0 = Function.update work₀ r (regTape v) := by
    funext j
    by_cases hjr : j = r
    · subst hjr; simp [hw, Function.update_self]
    · rw [Function.update_of_ne hjr]
      simp only [hw, if_neg hjr]
      split
      · rfl
      · rfl
  have hwv : w v = Function.update
      (fun j => if j ∈ targets then wipedTape (work₀ j) v else work₀ j) r (regTape v) := by
    funext j
    by_cases hjr : j = r
    · subst hjr; simp [hw, Function.update_self]
    · rw [Function.update_of_ne hjr]; simp [hw, if_neg hjr]
  have hwork_parked : ∀ i j, j ≠ r → Parked (w i j) := by
    intro i j hjr
    by_cases hjt : j ∈ targets
    · simp only [hw, if_neg hjr, if_pos hjt]
      exact wipedTape_parked (hother j hjr) i
    · simp only [hw, if_neg hjr, if_neg hjt]
      exact hother j hjr
  have hbody : ∀ i, i < v → (wipeStepTM targets).HoareTime
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (w i) r (⟨i + 2, regCells v⟩ : Tape) ∧ OutAcc [] out)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (w (i + 1)) r (⟨i + 2, regCells v⟩ : Tape) ∧ OutAcc [] out)
      1 := by
    intro i _
    set W : Fin n → Tape := Function.update (w i) r (⟨i + 2, regCells v⟩ : Tape) with hW
    have hcopy := wipeStepTM_hoareTime targets inp₀ W ((Tape.init []).move Dir3.right)
      hinp₀ parked_parkedBlank
      (fun k _ => by
        by_cases hkr : k = r
        · subst hkr; rw [hW, Function.update_self]; exact regIterCells_parked v i
        · rw [hW, Function.update_of_ne hkr]; exact hwork_parked i k hkr)
    refine (hcopy.weaken_pre ?_).strengthen_post ?_
    · rintro inp work out ⟨rfl, rfl, hout⟩
      exact ⟨rfl, rfl, eq_parkedBlank_of_outAcc_nil hout⟩
    · rintro inp work out ⟨rfl, hout, hwork⟩
      refine ⟨rfl, ?_, hout ▸ outAcc_nil_of_parkedBlank⟩
      funext j
      rw [hwork j]
      by_cases hjr : j = r
      · subst hjr
        rw [if_neg hr, hW, Function.update_self, Function.update_self]
      · by_cases hjt : j ∈ targets
        · rw [if_pos hjt]
          have hWj : W j = wipedTape (work₀ j) i := by
            rw [hW, Function.update_of_ne hjr, hw]; simp [if_neg hjr, if_pos hjt]
          have hRj : Function.update (w (i + 1)) r (⟨i + 2, regCells v⟩ : Tape) j =
              wipedTape (work₀ j) (i + 1) := by
            rw [Function.update_of_ne hjr, hw]; simp [if_neg hjr, if_pos hjt]
          rw [hWj, hRj, wipedTape_succ]
        · rw [if_neg hjt]
          have hWj : W j = work₀ j := by
            rw [hW, Function.update_of_ne hjr, hw]; simp [if_neg hjr, if_neg hjt]
          have hRj : Function.update (w (i + 1)) r (⟨i + 2, regCells v⟩ : Tape) j = work₀ j := by
            rw [Function.update_of_ne hjr, hw]; simp [if_neg hjr, if_neg hjt]
          rw [hWj, hRj]
  have key := forRegTM_hoareTime (wipeStepTM targets) r v inp₀ w (fun _ => []) 1 hinp₀
    (fun i => by simp [hw]) hwork_parked hbody
  refine key.consequence
    (fun inp work out ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, hw0], h3 ▸ outAcc_nil_of_parkedBlank⟩)
    (fun inp work out ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, hwv], (eq_parkedBlank_of_outAcc_nil h3)⟩)
    (by omega)

end WipeLoop

/-! ## Parking every tape at once

Rewinding several tapes one at a time (`rewindWorkTM`, chained) needs every
tape *not* currently being rewound to already be `Parked` — off the `▷`
marker — since an idled tape still reading `▷` would itself bounce to cell 1
as a side effect, silently perturbing the invariant. A single `skipTM` step,
run once with no target at all, sidesteps this: every tape merely needs
`StartInvariant` (its only possible `▷` is at cell `0`, regardless of current
head), and one step brings every one of them to `Parked` uniformly — cell-0
tapes bounce to cell 1, tapes already parked stay exactly put. This is the
one-time "let everything bounce" pass that makes the subsequent sequential
rewinds valid. -/

section ParkAll

open Complexity.TM

/-- One idle step on a `StartInvariant` tape is exactly a bounce off `▷` if it
was there, and otherwise a no-op: the resulting head is `max t.head 1`. -/
theorem move_idleDir_eq_of_startInvariant {t : Tape} (h : Tape.StartInvariant t) :
    t.move (idleDir t.read) = ⟨max t.head 1, t.cells⟩ := by
  by_cases hh : t.read = Γ.start
  · have hh0 : t.head = 0 := by
      by_contra hc
      exact (h.2 t.head (by omega)) hh
    rw [idleDir, if_pos hh]
    refine Tape.ext ?_ (Tape.move_cells t Dir3.right)
    show t.head + 1 = max t.head 1
    omega
  · have hh0 : t.head ≠ 0 := fun hc => hh (by rw [Tape.read, hc]; exact h.1)
    rw [idleDir, if_neg hh]
    show t = ⟨max t.head 1, t.cells⟩
    have : max t.head 1 = t.head := by omega
    rw [this]

/-- One idle step parks a `StartInvariant` tape: bounces it off `▷` if it was
there, and otherwise leaves it exactly as it was. -/
theorem parked_move_idleDir_of_startInvariant {t : Tape} (h : Tape.StartInvariant t) :
    Parked (t.move (idleDir t.read)) ∧ (t.move (idleDir t.read)).cells = t.cells := by
  rw [move_idleDir_eq_of_startInvariant h]
  exact ⟨⟨le_max_right _ _, fun j hj => h.2 j hj⟩, rfl⟩

/-- **Parking every tape at once.** From tapes satisfying only
`StartInvariant`, one `skipTM` step brings every one of them to `Parked`,
preserving all cell contents exactly. -/
theorem parkAll_hoareTime {n : ℕ} (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinp : Tape.StartInvariant inp₀) (hwork : ∀ i, Tape.StartInvariant (work₀ i))
    (hout : Tape.StartInvariant out₀) :
    (skipTM (n := n)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = (⟨max inp₀.head 1, inp₀.cells⟩ : Tape) ∧
        (∀ i, work i = (⟨max (work₀ i).head 1, (work₀ i).cells⟩ : Tape)) ∧
        out = (⟨max out₀.head 1, out₀.cells⟩ : Tape))
      1 := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  refine ⟨⟨(skipTM (n := n)).qhalt,
      inp.move (idleDir inp.read),
      fun i => (work i).move (idleDir (work i).read),
      out.move (idleDir out.read)⟩,
    1, le_refl 1, ?_, rfl, ?_, ?_, ?_⟩
  · refine TM.reachesIn.step ?_ .zero
    simp only [TM.step, skipTM,
      if_neg (show BumpPhase.go ≠ BumpPhase.done by decide),
      writeAndMove_readBack_of_startInvariant out hout]
    congr 2
    funext i
    exact writeAndMove_readBack_of_startInvariant (work i) (hwork i) _
  · exact move_idleDir_eq_of_startInvariant hinp
  · exact fun i => move_idleDir_eq_of_startInvariant (hwork i)
  · exact move_idleDir_eq_of_startInvariant hout

end ParkAll

/-! ## Rewinding a list of tapes, one at a time

Rewinding several tapes to cell `1` can't be done in one uniform pass over
all of them (unlike wiping): `rewindWorkTM`'s left-moving direction bounces
at `▷` (§`δ_right_of_start`) rather than saturating there, so a naive
"move everyone left the same number of times" oscillates. Doing it one tape
at a time — via `bigSeqTM`, needing every *other* tape `Parked` at each
step — works once every tape has *already* been parked once
(`parkAll_hoareTime`): a tape being individually rewound doesn't need to be
`Parked` itself, only the ones not yet reached do, and after the initial
park-everything pass that's every tape in the list. -/

section RewindList

open Complexity.TM

/-- **Rewinding a list of tapes, one at a time.** Given a uniform head bound
`B` and that *every* tape (not just the targets) is already `Parked` — the
state after `parkAll_hoareTime` — sequentially rewinding each named tape
lands it at cell `1` with its cells unchanged, leaving every other tape
(targeted-but-not-yet-reached, or never targeted) exactly as it was. -/
theorem rewindList_hoareTime {n : ℕ} :
    ∀ (targets : List (Fin n)), targets.Nodup →
    ∀ (B : ℕ) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape),
    Parked inp₀ → Parked out₀ → (∀ j, Parked (work₀ j)) →
    (∀ j, j ∈ targets → (work₀ j).cells 0 = Γ.start ∧ (work₀ j).head ≤ B) →
    (bigSeqTM (targets.map rewindWorkTM)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = ⟨1, (work₀ j).cells⟩) ∧
        (∀ j, j ∉ targets → work j = work₀ j))
      (targets.length * (B + 3) + 1) := by
  intro targets
  induction targets with
  | nil =>
    intro _ B inp₀ work₀ out₀ hinp hout hwork _
    simp only [List.map_nil, List.length_nil, Nat.zero_mul, Nat.zero_add]
    refine (skipTM_hoareTime_frame inp₀ work₀ out₀ hinp hwork hout).strengthen_post ?_
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, nofun, fun j _ => rfl⟩
  | cons t ts ih =>
    intro hnodup B inp₀ work₀ out₀ hinp hout hwork htarget
    have htnts : t ∉ ts := (List.nodup_cons.mp hnodup).1
    have htsnodup : ts.Nodup := (List.nodup_cons.mp hnodup).2
    have hP : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
        (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
        ((work t).cells = (work₀ t).cells ∧
          inp = inp₀ ∧ out = out₀ ∧ ∀ j, j ≠ t → work j = work₀ j) →
        (work' t).cells = (work t).cells → (work' t).head = 1 →
        (∀ j, j ≠ t → work' j = work j) →
        inp' = inp → out'.cells = out.cells → out'.head = out.head →
        ((work' t).cells = (work₀ t).cells ∧
          inp' = inp₀ ∧ out' = out₀ ∧ ∀ j, j ≠ t → work' j = work₀ j) := by
      rintro inp work out inp' work' out' ⟨hcellsP, rfl, rfl, hrest⟩ hcells' _ hkeep rfl
        hout'c hout'h
      exact ⟨hcells'.trans hcellsP, rfl, Tape.ext hout'h hout'c,
        fun j hjt => (hkeep j hjt).trans (hrest j hjt)⟩
    have h1 := rewindWorkTM_hoareTime_frame t B hP
    have h1' := h1.weaken_pre
      (show (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀) ≤ _ by
        rintro inp work out ⟨rfl, rfl, rfl⟩
        exact ⟨(htarget t (by simp)).1, fun j hj => (hwork t).2 j hj, (htarget t (by simp)).2,
          hinp.read_ne_start, hout.read_ne_start, hout.1,
          fun i _ => ⟨(hwork i).read_ne_start, (hwork i).1⟩, rfl, rfl, rfl, fun _ _ => rfl⟩)
    set work₁ : Fin n → Tape := Function.update work₀ t (⟨1, (work₀ t).cells⟩ : Tape) with hwork₁
    have hwork₁P : ∀ j, Parked (work₁ j) := by
      intro j
      by_cases hjt : j = t
      · rw [hjt, hwork₁, Function.update_self]
        exact ⟨le_refl 1, fun i hi => (hwork t).2 i hi⟩
      · rw [hwork₁, Function.update_of_ne hjt]; exact hwork j
    have hwork₁target : ∀ j, j ∈ ts → (work₁ j).cells 0 = Γ.start ∧ (work₁ j).head ≤ B := by
      intro j hj
      have hjt : j ≠ t := by rintro rfl; exact htnts hj
      rw [hwork₁, Function.update_of_ne hjt]
      exact htarget j (by simp [hj])
    have ih' := ih htsnodup B inp₀ work₁ out₀ hinp hout hwork₁P hwork₁target
    have hread_t : ∀ (work : Fin n → Tape), (work t).cells = (work₀ t).cells →
        (work t).head = 1 → (work t).read ≠ Γ.start := by
      intro work hcells hhead
      show (work t).cells (work t).head ≠ Γ.start
      rw [hhead, hcells]
      exact (hwork t).2 1 le_rfl
    have h2 : (bigSeqTM ((t :: ts).map rewindWorkTM)).HoareTime
        (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
        (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
          (∀ j, j ∈ ts → work j = ⟨1, (work₁ j).cells⟩) ∧
          (∀ j, j ∉ ts → work j = work₁ j))
        ((B + 2) + 1 + (ts.length * (B + 3) + 1)) := by
      simp only [List.map_cons, bigSeqTM]
      refine seqTM_hoareTime (rewindWorkTM t) (bigSeqTM (ts.map rewindWorkTM)) h1' ?_ ih'
      rintro inp work out ⟨hhead1, hcellsP, hpinp, hpout, hprest⟩
      have hreadt : (work t).read ≠ Γ.start := hread_t work hcellsP hhead1
      have ht1 : transitionInput inp = inp₀ := by
        rw [hpinp]; exact transitionInput_eq_self hinp.read_ne_start
      have ht3 : transitionTape out = out₀ := by
        rw [hpout]; exact transitionTape_eq_self hout.read_ne_start
      have ht2 : (fun i => transitionTape (work i)) = work₁ := by
        funext j
        by_cases hjt : j = t
        · rw [hjt, transitionTape_eq_self hreadt, hwork₁, Function.update_self]
          exact Tape.ext hhead1 hcellsP
        · rw [hprest j hjt, transitionTape_eq_self (hwork j).read_ne_start,
            hwork₁, Function.update_of_ne hjt]
      rw [ht1, ht2, ht3]
      exact ⟨rfl, rfl, rfl⟩
    refine h2.consequence (fun _ _ _ h => h)
      (fun inp work out ⟨hinpeq, houteq, hts, hnts⟩ => ?_)
      (by rw [List.length_cons]; ring_nf; omega)
    refine ⟨hinpeq, houteq, fun j hj => ?_, fun j hj => ?_⟩
    · rw [List.mem_cons] at hj
      rcases hj with hjeqt | hjts
      · rw [hnts j (hjeqt ▸ htnts), hjeqt, hwork₁, Function.update_self]
      · rw [hts j hjts]
        congr 1
        have hjt : j ≠ t := fun h => htnts (h ▸ hjts)
        rw [hwork₁, Function.update_of_ne hjt]
    · have hjt : j ≠ t := fun h => hj (List.mem_cons.mpr (Or.inl h))
      have hjts : j ∉ ts := fun h => hj (List.mem_cons.mpr (Or.inr h))
      rw [hnts j hjts, hwork₁, Function.update_of_ne hjt]

end RewindList

/-! ## Resetting a list of tapes to blank, content-agnostically

The full reset an opaque `FP` witness machine's scratch needs between calls:
park everything (`parkAll_hoareTime`), rewind every targeted tape to cell `1`
(`rewindList_hoareTime`), then wipe `H` cells forward from there
(`wipeLoop_hoareTime`). A dedicated fuel register `r`, disjoint from the
targets, drives the wipe and is left exactly as it started. -/

section ResetTapes

open Complexity.TM

/-- **Resetting a list of tapes.** Regardless of their current content or head
position (bounded by `H`), every tape in `targets` ends up blanked from cell
`1` through cell `H`, with its tail beyond cell `H` untouched; the fuel
register `r` (disjoint from `targets`) and every other tape are exactly as
they were. -/
theorem resetTapes_hoareTime {n : ℕ} (targets : List (Fin n)) (hnodup : targets.Nodup)
    (r : Fin n) (hr : r ∉ targets) (H : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinpSI : Tape.StartInvariant inp₀) (hinpP : Parked inp₀)
    (hout0 : out₀ = (Tape.init []).move Dir3.right)
    (hworkSI : ∀ j, j ≠ r → Tape.StartInvariant (work₀ j))
    (htargetHead : ∀ j, j ∈ targets → (work₀ j).head ≤ H)
    (hworkR : work₀ r = regTape H)
    (hother : ∀ j, j ≠ r → j ∉ targets → Parked (work₀ j)) :
    (seqTM (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
        (forRegTM (wipeStepTM targets) r)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = wipedTape (⟨1, (work₀ j).cells⟩ : Tape) H) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = work₀ j))
      (targets.length * (H + 4) + H * 4 + 8) := by
  have hregParked : Parked (regTape H) :=
    ⟨le_refl 1, fun i hi => by
      show regCells H i ≠ Γ.start
      simp only [regCells]; split
      · omega
      · split <;> decide⟩
  have houtSI : Tape.StartInvariant out₀ := by
    rw [hout0]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [Tape.move_cells]; exact Tape.init_cells_zero []
    · rw [Tape.move_cells, show j = (j - 1) + 1 from by omega,
        Tape.init_cells_ge [] (j - 1) (by simp)]
      decide
  have houtP : Parked out₀ := by rw [hout0]; exact parked_parkedBlank
  have hworkSI' : ∀ j, Tape.StartInvariant (work₀ j) := by
    intro j
    by_cases hjr : j = r
    · subst hjr; rw [hworkR]; exact ⟨rfl, hregParked.2⟩
    · exact hworkSI j hjr
  set workA : Fin n → Tape := fun j => (⟨max (work₀ j).head 1, (work₀ j).cells⟩ : Tape)
    with hworkA
  have hAP : ∀ j, Parked (workA j) := fun j => ⟨le_max_right _ _, fun i hi => (hworkSI' j).2 i hi⟩
  have hAtarget : ∀ j, j ∈ targets → (workA j).cells 0 = Γ.start ∧ (workA j).head ≤ H + 1 := by
    intro j hj
    refine ⟨(hworkSI' j).1, ?_⟩
    show max (work₀ j).head 1 ≤ H + 1
    have := htargetHead j hj
    omega
  have hA := parkAll_hoareTime inp₀ work₀ out₀ hinpSI hworkSI' houtSI
  have hinpAeq : (⟨max inp₀.head 1, inp₀.cells⟩ : Tape) = inp₀ :=
    Tape.ext (by show max inp₀.head 1 = inp₀.head; have := hinpP.1; omega) rfl
  have houtAeq : (⟨max out₀.head 1, out₀.cells⟩ : Tape) = out₀ :=
    Tape.ext (by show max out₀.head 1 = out₀.head; have := houtP.1; omega) rfl
  have hApost_imp : ∀ inp work out,
      (inp = (⟨max inp₀.head 1, inp₀.cells⟩ : Tape) ∧
        (∀ i, work i = workA i) ∧ out = (⟨max out₀.head 1, out₀.cells⟩ : Tape)) →
      (inp = inp₀ ∧ work = workA ∧ out = out₀) := by
    rintro inp work out ⟨hi, hw, ho⟩
    exact ⟨hi.trans hinpAeq, funext hw, ho.trans houtAeq⟩
  have hA' := hA.strengthen_post hApost_imp
  have hB0 := rewindList_hoareTime targets hnodup (H + 1) inp₀ workA out₀ hinpP houtP hAP hAtarget
  have hB : (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM))).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = (⟨1, (work₀ j).cells⟩ : Tape)) ∧
        (∀ j, j ∉ targets → work j = workA j))
      (1 + 1 + targets.length * ((H + 1) + 3) + 1) := by
    refine seqTM_hoareTime skipTM (bigSeqTM (targets.map rewindWorkTM)) hA' ?_ hB0
    rintro inp work out ⟨rfl, rfl, rfl⟩
    refine ⟨transitionInput_eq_self hinpP.read_ne_start, ?_,
      transitionTape_eq_self houtP.read_ne_start⟩
    funext i
    exact transitionTape_eq_self (hAP i).read_ne_start
  set workC : Fin n → Tape := fun j => if j ∈ targets then (⟨1, (work₀ j).cells⟩ : Tape)
    else work₀ j with hworkC
  have hCother : ∀ j, j ≠ r → Parked (workC j) := by
    intro j hjr
    rw [hworkC]
    dsimp only
    split
    · next hjt => exact ⟨le_refl 1, (hworkSI' j).2⟩
    · next hjt => exact hother j hjr hjt
  have hC0 := wipeLoop_hoareTime targets r hr H inp₀ workC hinpP hCother
  have hworkeq : ∀ (work : Fin n → Tape),
      (∀ j, j ∈ targets → work j = (⟨1, (work₀ j).cells⟩ : Tape)) →
      (∀ j, j ∉ targets → work j = workA j) →
      work = Function.update workC r (regTape H) := by
    intro work hts hnts
    funext j
    by_cases hjr : j = r
    · rw [hjr, Function.update_self]
      rw [hnts r hr]
      show (⟨max (work₀ r).head 1, (work₀ r).cells⟩ : Tape) = regTape H
      rw [hworkR]
      exact Tape.ext (by show max 1 1 = 1; omega) (by rw [regT_cells])
    · rw [Function.update_of_ne hjr]
      by_cases hjt : j ∈ targets
      · rw [hts j hjt, hworkC]; simp [hjt]
      · rw [hnts j hjt, hworkC]
        simp only [hjt, if_false]
        exact Tape.ext (by
          show max (work₀ j).head 1 = (work₀ j).head
          have := (hother j hjr hjt).1
          omega) rfl
  have hread : ∀ (work : Fin n → Tape),
      (∀ j, j ∈ targets → work j = (⟨1, (work₀ j).cells⟩ : Tape)) →
      (∀ j, j ∉ targets → work j = workA j) →
      ∀ j, (work j).read ≠ Γ.start := by
    intro work hts hnts j
    by_cases hjt : j ∈ targets
    · rw [hts j hjt]
      exact (hworkSI' j).2 1 le_rfl
    · rw [hnts j hjt]
      exact (hAP j).read_ne_start
  have htrans : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape),
      (inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = (⟨1, (work₀ j).cells⟩ : Tape)) ∧
        (∀ j, j ∉ targets → work j = workA j)) →
      transitionInput inp = inp₀ ∧
        (fun i => transitionTape (work i)) = Function.update workC r (regTape H) ∧
        transitionTape out = (Tape.init []).move Dir3.right := by
    rintro inp work out ⟨hi, ho, hts, hnts⟩
    refine ⟨by rw [hi]; exact transitionInput_eq_self hinpP.read_ne_start,
      ?_, by rw [ho, transitionTape_eq_self houtP.read_ne_start]; exact hout0⟩
    rw [← hworkeq work hts hnts]
    funext j
    exact transitionTape_eq_self (hread work hts hnts j)
  have hFull := seqTM_hoareTime (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
    (forRegTM (wipeStepTM targets) r) hB htrans hC0
  have hpost_imp : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape),
      (inp = inp₀ ∧
        work = Function.update (fun j => if j ∈ targets then wipedTape (workC j) H else workC j)
          r (regTape H) ∧
        out = (Tape.init []).move Dir3.right) →
      (inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = wipedTape (⟨1, (work₀ j).cells⟩ : Tape) H) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = work₀ j)) := by
    rintro inp work out ⟨hi, hw, ho⟩
    refine ⟨hi, ho.trans hout0.symm, fun j hjt => ?_, ?_, fun j hjr hjt => ?_⟩
    · rw [hw, Function.update_of_ne (fun h => hr (by rw [h] at hjt; exact hjt)),
        if_pos hjt, hworkC]
      simp [hjt]
    · rw [hw, Function.update_self]
    · rw [hw, Function.update_of_ne hjr, hworkC]
      simp [hjt]
  refine (hFull.strengthen_post hpost_imp).mono_bound ?_
  ring_nf
  omega

/-- The composite reset machine: park everything, rewind the targets, wipe
`H` cells forward, then rewind the targets again. -/
def resetTapesTM {n : ℕ} (targets : List (Fin n)) (r : Fin n) : TM n :=
  seqTM (seqTM (seqTM skipTM (bigSeqTM (targets.map rewindWorkTM)))
      (forRegTM (wipeStepTM targets) r))
    (bigSeqTM (targets.map rewindWorkTM))

/-- **The full reset.** Every tape in `targets` whose content is confined to
cells `1 … H` — no matter *where* in that range, and no matter where its head
currently sits — ends up literally blank and parked at cell `1`. The fuel
register `r` and all other tapes are returned exactly as they were. -/
theorem resetTapesTM_hoareTime {n : ℕ} (targets : List (Fin n)) (hnodup : targets.Nodup)
    (r : Fin n) (hr : r ∉ targets) (H : ℕ)
    (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hinpSI : Tape.StartInvariant inp₀) (hinpP : Parked inp₀)
    (hout0 : out₀ = (Tape.init []).move Dir3.right)
    (hworkSI : ∀ j, j ≠ r → Tape.StartInvariant (work₀ j))
    (htargetHead : ∀ j, j ∈ targets → (work₀ j).head ≤ H)
    (htargetFar : ∀ j, j ∈ targets → ∀ i, H < i → (work₀ j).cells i = Γ.blank)
    (hworkR : work₀ r = regTape H)
    (hother : ∀ j, j ≠ r → j ∉ targets → Parked (work₀ j)) :
    (resetTapesTM targets r).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = (Tape.init []).move Dir3.right) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = work₀ j))
      (targets.length * (H + 4) + H * 4 + 8 + 1 + (targets.length * (H + 4) + 1)) := by
  have houtP : Parked out₀ := by rw [hout0]; exact parked_parkedBlank
  have hregParked : Parked (regTape H) :=
    ⟨le_refl 1, fun i hi => by
      show regCells H i ≠ Γ.start
      simp only [regCells]; split
      · omega
      · split <;> decide⟩
  -- the wipe's exact effect on a targeted tape, spelled out
  have hwiped : ∀ j, j ∈ targets →
      wipedTape (⟨1, (work₀ j).cells⟩ : Tape) H = (⟨H + 1, (Tape.init []).cells⟩ : Tape) := by
    intro j hj
    refine wipedTape_eq_blank H rfl ?_ (fun i hi => htargetFar j hj i hi)
    exact (hworkSI j (fun h => hr (h ▸ hj))).1
  -- the tape family after the wipe phase
  set workD : Fin n → Tape := fun j =>
    if j ∈ targets then (⟨H + 1, (Tape.init []).cells⟩ : Tape)
    else if j = r then regTape H else work₀ j with hworkD
  have hDP : ∀ j, Parked (workD j) := by
    intro j
    rw [hworkD]
    dsimp only
    split
    · exact ⟨show 1 ≤ H + 1 by omega,
        fun i hi => by rw [initNil_cells, if_neg (by omega)]; decide⟩
    · split
      · exact hregParked
      · next hjt hjr => exact hother j hjr hjt
  have hDtarget : ∀ j, j ∈ targets →
      (workD j).cells 0 = Γ.start ∧ (workD j).head ≤ H + 1 := by
    intro j hj
    rw [hworkD]
    simp only [if_pos hj]
    exact ⟨by rw [initNil_cells, if_pos rfl], le_refl _⟩
  have hfirst := resetTapes_hoareTime targets hnodup r hr H inp₀ work₀ out₀ hinpSI hinpP
    hout0 hworkSI htargetHead hworkR hother
  have hsecond := rewindList_hoareTime targets hnodup (H + 1) inp₀ workD out₀ hinpP houtP
    hDP hDtarget
  refine seqTM_hoareTime _ _ hfirst ?_ hsecond |>.strengthen_post ?_
  · -- the boundary: everything is parked, so the seam is the identity
    rintro inp work out ⟨hi, ho, hts, hR, hrest⟩
    have hworkD_eq : work = workD := by
      funext j
      by_cases hjt : j ∈ targets
      · rw [hts j hjt, hwiped j hjt, hworkD]; simp [hjt]
      · by_cases hjr : j = r
        · rw [hjr, hR, hworkD]; simp [hr]
        · rw [hrest j hjr hjt, hworkD]; simp [hjt, hjr]
    subst hworkD_eq
    refine ⟨by rw [hi]; exact transitionInput_eq_self hinpP.read_ne_start, ?_,
      by rw [ho]; exact transitionTape_eq_self houtP.read_ne_start⟩
    funext j
    exact transitionTape_eq_self (hDP j).read_ne_start
  · rintro inp work out ⟨hi, ho, hts, hnts⟩
    refine ⟨hi, ho, fun j hj => ?_, ?_, fun j hjr hjt => ?_⟩
    · rw [hts j hj, hworkD]
      simp only [if_pos hj]
      rfl
    · rw [hnts r hr, hworkD]
      simp [hr]
    · rw [hnts j hjt, hworkD]
      simp [hjt, hjr]

/-- **The reset, keyed on bounds rather than on a named tape family.** The
tapes an opaque machine leaves behind are only known through bounds, never as
a closed form, so this is the shape the loop body actually needs: the exact
starting family is instantiated inside the proof. -/
theorem resetTapesTM_hoareTime_of_bounds {n : ℕ} (targets : List (Fin n))
    (hnodup : targets.Nodup) (r : Fin n) (hr : r ∉ targets) (H : ℕ)
    (inp₀ : Tape) (extras : Fin n → Tape) (out₀ : Tape)
    (hinpSI : Tape.StartInvariant inp₀) (hinpP : Parked inp₀)
    (hout0 : out₀ = (Tape.init []).move Dir3.right)
    (hextraP : ∀ j, j ≠ r → j ∉ targets → Parked (extras j)) :
    (resetTapesTM targets r).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ≠ r → Tape.StartInvariant (work j)) ∧
        (∀ j, j ∈ targets → (work j).head ≤ H ∧ ∀ i, H < i → (work j).cells i = Γ.blank) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = extras j))
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        (∀ j, j ∈ targets → work j = (Tape.init []).move Dir3.right) ∧
        work r = regTape H ∧
        (∀ j, j ≠ r → j ∉ targets → work j = extras j))
      (targets.length * (H + 4) + H * 4 + 8 + 1 + (targets.length * (H + 4) + 1)) := by
  intro inp work out hpre
  obtain ⟨hi, ho, hSI, hbnd, hR, hext⟩ := hpre
  rw [hi, ho]
  obtain ⟨c', t, ht, hreach, hhalt, hi', ho', hts, hR', hrest⟩ :=
    resetTapesTM_hoareTime targets hnodup r hr H inp₀ work out₀ hinpSI hinpP hout0 hSI
      (fun j hj => (hbnd j hj).1) (fun j hj i hii => (hbnd j hj).2 i hii) hR
      (fun j hjr hjt => by rw [hext j hjr hjt]; exact hextraP j hjr hjt)
      inp₀ work out₀ ⟨rfl, rfl, rfl⟩
  exact ⟨c', t, ht, hreach, hhalt, hi', ho', hts, hR',
    fun j hjr hjt => (hrest j hjr hjt).trans (hext j hjr hjt)⟩

end ResetTapes

/-! ## Copying a value into virtual-input shape

`retargetInputStartedCfg` expects the virtual-input work tape in the exact
shape `(Tape.init (y.map Γ.ofBool)).move Dir3.right` (head parked at cell
`1`). A value produced elsewhere lands as a `HasOutput`/`HasBinaryPrefix`
tape (head *past* its content, at `|y| + 1`); one more rewind closes the
gap. -/

section CopyToVirtualInput

open Complexity.TM

/-- Copy the value held at `src` into `dst`, then rewind `dst` to cell `1` —
the exact shape `retargetInputStartedCfg` expects of a virtual input. Every
tape besides `src`/`dst`, the real input, and the real output are held at
fixed `Parked` values throughout. -/
theorem copyToVirtualInput_hoareTime {n : ℕ} (src dst : Fin n) (hne : src ≠ dst)
    (x : List Bool) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrcHead : (work₀ src).head = 1) (hsrcOut : (work₀ src).HasOutput x)
    (hsrcParked : Parked (work₀ src))
    (hdst : work₀ dst = (Tape.init []).move Dir3.right)
    (hinp : Parked inp₀) (hout : Parked out₀)
    (hother : ∀ i, i ≠ src → i ≠ dst → Parked (work₀ i)) :
    (seqTM (copyWorkToWorkTM src dst) (rewindWorkTM dst)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ out = out₀ ∧
        work dst = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        (work src).cells = (work₀ src).cells ∧
        (work src).head = x.length + 1 ∧
        (∀ i, i ≠ src → i ≠ dst → work i = work₀ i))
      (2 * x.length + 5) := by
  have hP : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      (inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i) →
      (work' src).cells = (work₀ src).cells →
      (work' src).head = x.length + 1 →
      (work' src).HasOutput x →
      (work' dst).HasBinaryPrefix x →
      (work' dst).cells 0 = Γ.start →
      inp' = inp → out' = out →
      (∀ i, i ≠ src → i ≠ dst → work' i = work i) →
      (inp' = inp₀ ∧ out' = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work' i = work₀ i) := by
    rintro inp work out inp' work' out' ⟨rfl, rfl, hrest⟩ _ _ _ _ _ rfl rfl hkeep
    exact ⟨rfl, rfl, fun i hisrc hidst => (hkeep i hisrc hidst).trans (hrest i hisrc hidst)⟩
  have hcopy := copyWorkToWorkTM_hoareTime_frame_of_hasOutput src dst hne x (work₀ src) hP
  have hpre_imp : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape),
      (inp = inp₀ ∧ work = work₀ ∧ out = out₀) →
      (work src = work₀ src ∧ (work₀ src).head = 1 ∧ (work₀ src).HasOutput x ∧
        work dst = (Tape.init []).move Dir3.right ∧
        inp.read ≠ Γ.start ∧ out.read ≠ Γ.start ∧ 1 ≤ out.head ∧
        (∀ i, i ≠ src → i ≠ dst → (work i).read ≠ Γ.start ∧ 1 ≤ (work i).head) ∧
        (inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i)) := by
    rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, hsrcHead, hsrcOut, hdst, hinp.read_ne_start, hout.read_ne_start, hout.1,
      fun i hisrc hidst => ⟨(hother i hisrc hidst).read_ne_start, (hother i hisrc hidst).1⟩,
      rfl, rfl, fun i _ _ => rfl⟩
  have h₁ := hcopy.weaken_pre hpre_imp
  have hP2 : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin n → Tape) (out' : Tape),
      ((work dst).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work src).cells = (work₀ src).cells ∧
        (work src).head = x.length + 1 ∧
        inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i) →
      (work' dst).cells = (work dst).cells →
      (work' dst).head = 1 →
      (∀ i, i ≠ dst → work' i = work i) →
      inp' = inp →
      out'.cells = out.cells →
      out'.head = out.head →
      ((work' dst).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work' src).cells = (work₀ src).cells ∧
        (work' src).head = x.length + 1 ∧
        inp' = inp₀ ∧ out' = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work' i = work₀ i) := by
    rintro inp work out inp' work' out' ⟨hcellsP, hsc, hsh, rfl, rfl, hrest⟩ hcells' _ hkeep rfl
      hout'c hout'h
    refine ⟨hcells'.trans hcellsP, ?_, ?_, rfl, Tape.ext hout'h hout'c,
      fun i hisrc hidst => (hkeep i hidst).trans (hrest i hisrc hidst)⟩
    · rw [hkeep src hne]; exact hsc
    · rw [hkeep src hne]; exact hsh
  have h₂ := rewindWorkTM_hoareTime_frame (n := n) dst (x.length + 1)
    (P := fun inp work out =>
      (work dst).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      (work src).cells = (work₀ src).cells ∧
      (work src).head = x.length + 1 ∧
      inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i) hP2
  have hcomb : (seqTM (copyWorkToWorkTM src dst) (rewindWorkTM dst)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => (work dst).head = 1 ∧
        (work dst).cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        (work src).cells = (work₀ src).cells ∧
        (work src).head = x.length + 1 ∧
        inp = inp₀ ∧ out = out₀ ∧ ∀ i, i ≠ src → i ≠ dst → work i = work₀ i)
      (2 * x.length + 5) := by
    refine (seqTM_hoareTime (copyWorkToWorkTM src dst) (rewindWorkTM dst) h₁ ?_ h₂).mono_bound
      (by omega)
    rintro inp work out ⟨hcells, hhead, hout_, hprefix, hcell0, hPinp, hPout, hPrest⟩
    have hread_src : (work src).read ≠ Γ.start := by
      show (work src).cells (work src).head ≠ Γ.start
      rw [hhead, hcells]
      exact hsrcParked.2 (x.length + 1) (by omega)
    have hread_dst : (work dst).read ≠ Γ.start := by
      rw [hprefix.read_blank]; decide
    have hread_other : ∀ i, i ≠ dst → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1 := by
      intro i hidst
      by_cases hisrc : i = src
      · subst hisrc; exact ⟨hread_src, by omega⟩
      · rw [hPrest i hisrc hidst]
        exact ⟨(hother i hisrc hidst).read_ne_start, (hother i hisrc hidst).1⟩
    have hinp_ns : inp.read ≠ Γ.start := by rw [hPinp]; exact hinp.read_ne_start
    have hout_ns : out.read ≠ Γ.start := by rw [hPout]; exact hout.read_ne_start
    have ht1 : transitionInput inp = inp := transitionInput_eq_self hinp_ns
    have ht2 : (fun i => transitionTape (work i)) = work :=
      funext fun i => by
        by_cases hidst : i = dst
        · subst hidst; exact transitionTape_eq_self hread_dst
        · exact transitionTape_eq_self (hread_other i hidst).1
    have ht3 : transitionTape out = out := transitionTape_eq_self hout_ns
    rw [ht1, ht2, ht3]
    have hcellsP : (work dst).cells = (Tape.init (x.map Γ.ofBool)).cells :=
      hprefix.cells_eq_init hcell0
    refine ⟨hcell0, ?_, le_of_eq hprefix.1, hinp_ns, hout_ns, ?_,
      fun i hidst => hread_other i hidst,
      hcellsP, hcells, hhead, hPinp, hPout, hPrest⟩
    · intro j hj
      have hj1 : j - 1 + 1 = j := by omega
      by_cases hle : j ≤ x.length
      · rw [← hj1, hprefix.2.1 (j - 1) (by omega)]
        cases x[j - 1]'(by omega) <;> decide
      · rw [← hj1, hprefix.2.2 (j - 1) (by omega)]
        decide
    · rw [hPout]; exact hout.1
  exact hcomb.strengthen_post (by
    rintro inp work out ⟨hhead1, hcellsP, hsc, hsh, hPinp, hPout, hPrest⟩
    exact ⟨hPinp, hPout, Tape.ext hhead1 hcellsP, hsc, hsh, hPrest⟩)

/-- Copy a work tape's value into another and park the result at cell `1`. -/
def copyToVirtualInputTM {n : ℕ} (src dst : Fin n) : TM n :=
  seqTM (copyWorkToWorkTM src dst) (rewindWorkTM dst)

/-- **The copy, with the whole tape family pinned down.** The source keeps its
cells but ends with its head past the copied value; the destination holds the
value parked at cell `1`; nothing else moves. This determined form is what
`TM.seqTM_det` chains. -/
theorem copyToVirtualInputTM_hoareTime {n : ℕ} (src dst : Fin n) (hne : src ≠ dst)
    (x : List Bool) (inp₀ : Tape) (work₀ : Fin n → Tape) (out₀ : Tape)
    (hsrcHead : (work₀ src).head = 1) (hsrcOut : (work₀ src).HasOutput x)
    (hsrcParked : Parked (work₀ src))
    (hdst : work₀ dst = (Tape.init []).move Dir3.right)
    (hinp : Parked inp₀) (hout : Parked out₀)
    (hother : ∀ i, i ≠ src → i ≠ dst → Parked (work₀ i)) :
    (copyToVirtualInputTM src dst).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧
        work = Function.update (Function.update work₀ dst
            ((Tape.init (x.map Γ.ofBool)).move Dir3.right))
          src (⟨x.length + 1, (work₀ src).cells⟩ : Tape) ∧
        out = out₀)
      (2 * x.length + 5) := by
  refine (copyToVirtualInput_hoareTime src dst hne x inp₀ work₀ out₀ hsrcHead hsrcOut
    hsrcParked hdst hinp hout hother).strengthen_post ?_
  rintro inp work out ⟨hi, ho, hd, hsc, hsh, hrest⟩
  refine ⟨hi, ?_, ho⟩
  funext j
  by_cases hjs : j = src
  · rw [hjs, Function.update_self]
    exact Tape.ext (hjs ▸ hsh) (hjs ▸ hsc)
  · rw [Function.update_of_ne hjs]
    by_cases hjd : j = dst
    · rw [hjd, Function.update_self]
      exact hjd ▸ hd
    · rw [Function.update_of_ne hjd]
      exact hrest j hjs hjd

end CopyToVirtualInput

/-! ## Unary marks, as an `FP` function

`forRegTM`'s fuel register is driven by *head position on a run of `Γ.one`
marks*, not by a bit's value, so a loop count `n` needs to be realized as
`List.replicate n true` on some tape before the loop can consume it. Since
this realization is itself just another `FP` function, it composes with
whatever `FP` function produced `n` as a length. -/

/-- **A run of `n` marks is `FP`.** Immediate from `unaryLengthTM`'s linear-time
correctness. -/
theorem unaryOnes_mem_FP : (fun x : List Bool => List.replicate x.length true) ∈ FP := by
  refine ⟨1, 0, TM.unaryLengthTM, (fun m => m + 2), TM.unaryLengthTM_computesInTime 0, ?_⟩
  have hn : (fun m : ℕ => m) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun m : ℕ => m)
  exact BigO.add hn (BigO.const_le_pow 2 1)

/-! ## The iteration machine's tape layout

Two unary fuel registers (one consumed by the outer loop, one reused by every
reset), one junk tape holding the input's padding block, and then
`TM.applyTM`'s own tapes placed after them. The running value needs no tape of
its own: it lives on `applyTM`'s virtual-input tape, which is exactly where the
next call wants it. -/

section IterateLayout

open Complexity.TM

variable {k : ℕ}

/-- The outer loop's fuel register. -/
def rfIdx : Fin (3 + (k + 2) + 0) := ⟨0, by omega⟩

/-- The reset's fuel register, restored by every reset. -/
def wfIdx : Fin (3 + (k + 2) + 0) := ⟨1, by omega⟩

/-- Holds the input's padding block; never read again. -/
def junkIdx : Fin (3 + (k + 2) + 0) := ⟨2, by omega⟩

/-- Where `TM.applyTM`'s tape `j` sits in the composite layout. -/
def appIdx (j : Fin (k + 2)) : Fin (3 + (k + 2) + 0) := placeWorkIdx 3 0 j

/-- The running value's tape — `applyTM`'s virtual input. -/
def vinIdx : Fin (3 + (k + 2) + 0) := appIdx (Fin.castSucc (Fin.last k))

/-- Where one application of the iterated function leaves its result. -/
def resIdx : Fin (3 + (k + 2) + 0) := appIdx (Fin.last (k + 1))

@[simp] theorem rfIdx_val : (rfIdx (k := k)).val = 0 := rfl
@[simp] theorem wfIdx_val : (wfIdx (k := k)).val = 1 := rfl
@[simp] theorem junkIdx_val : (junkIdx (k := k)).val = 2 := rfl
@[simp] theorem appIdx_val (j : Fin (k + 2)) : (appIdx j).val = 3 + j.val := rfl

/-- The three bookkeeping tapes are exactly the ones outside `applyTM`'s
block. -/
theorem not_middle_iff (i : Fin (3 + (k + 2) + 0)) :
    ¬ placeWorkInMiddle 3 (k + 2) i ↔ i.val < 3 := by
  have hlt := i.isLt
  unfold placeWorkInMiddle
  constructor <;> intro h <;> omega

theorem appIdx_middle (j : Fin (k + 2)) : placeWorkInMiddle 3 (k + 2) (appIdx j) :=
  placeWorkInMiddle_placeWorkIdx 3 0 j

theorem appIdx_injective : Function.Injective (appIdx (k := k)) :=
  placeWorkIdx_injective 3 0

theorem rfIdx_not_middle : ¬ placeWorkInMiddle 3 (k + 2) (rfIdx (k := k)) :=
  (not_middle_iff _).mpr (by rw [rfIdx_val]; omega)

theorem wfIdx_not_middle : ¬ placeWorkInMiddle 3 (k + 2) (wfIdx (k := k)) :=
  (not_middle_iff _).mpr (by rw [wfIdx_val]; omega)

theorem junkIdx_not_middle : ¬ placeWorkInMiddle 3 (k + 2) (junkIdx (k := k)) :=
  (not_middle_iff _).mpr (by rw [junkIdx_val]; omega)

theorem wfIdx_ne_appIdx (j : Fin (k + 2)) : wfIdx ≠ appIdx j := by
  intro h
  exact wfIdx_not_middle (h ▸ appIdx_middle j)

theorem rfIdx_ne_appIdx (j : Fin (k + 2)) : rfIdx ≠ appIdx j := by
  intro h
  exact rfIdx_not_middle (h ▸ appIdx_middle j)

theorem junkIdx_ne_appIdx (j : Fin (k + 2)) : junkIdx ≠ appIdx j := by
  intro h
  exact junkIdx_not_middle (h ▸ appIdx_middle j)

/-- **The layout is exhaustive.** Every tape of the composite machine is one of
the three bookkeeping tapes or one of `TM.applyTM`'s own, so a predicate that
names all four kinds pins down the whole tape family. -/
theorem layout_cases (i : Fin (3 + (k + 2) + 0)) :
    i = rfIdx ∨ i = wfIdx ∨ i = junkIdx ∨ ∃ j : Fin (k + 2), i = appIdx j := by
  by_cases hmid : placeWorkInMiddle 3 (k + 2) i
  · exact Or.inr (Or.inr (Or.inr
      ⟨placeWorkCoord 3 (k + 2) i hmid, (placeWorkIdx_placeWorkCoord i hmid).symm⟩))
  · rw [not_middle_iff] at hmid
    have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases h with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))

/-- **One application of the iterated function, in the composite layout.**
The bookkeeping tapes are held fixed; `applyTM`'s block goes from its entry
shape for `y` to a state where the result tape holds `G y` and every tape of
the block is still confined to cells `1 … H` — the two facts
`Complexity.resetTapesTM` needs to clean up afterwards. -/
theorem placedApply_hoareTime (M : TM k) {G : List Bool → List Bool} {T : ℕ → ℕ}
    (hcomp : M.ComputesInTime G T) (y : List Bool)
    (inp₀ : Tape) (hinp : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (H : ℕ) (hHy : y.length ≤ H) (hHT : 1 + T y.length ≤ H)
    (extras : Fin (3 + (k + 2) + 0) → Tape)
    (hextraSI : ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → Tape.StartInvariant (extras i))
    (hextraH : ∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → 1 ≤ (extras i).head) :
    (placeWorkTM 3 0 (applyTM M)).HoareTime
      (fun inp work out => inp = inp₀ ∧
        (∀ j, work (appIdx j) = applyPre M y inp₀ j) ∧
        (∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → work i = extras i) ∧
        out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).HasOutput (G y) ∧
        (∀ j, Tape.StartInvariant (work (appIdx j)) ∧ (work (appIdx j)).head ≤ H ∧
          ∀ c, H < c → (work (appIdx j)).cells c = Γ.blank) ∧
        (∀ i, ¬ placeWorkInMiddle 3 (k + 2) i → work i = extras i))
      (T y.length) := by
  have hbase := placeWorkTM_hoareTime_frame (pre := 3) (post := 0) (applyTM M)
    (applyTM_hoareTime_frame M hcomp y inp₀ hinp hinpSI H hHy hHT) extras hextraSI hextraH
  refine (hbase.weaken_pre ?_).strengthen_post ?_
  · rintro inp work out ⟨hi, hmid, hext, ho⟩
    exact ⟨⟨hi, funext hmid, ho⟩, hext⟩
  · rintro inp work out ⟨⟨hi, ho, hres, hall⟩, hext⟩
    exact ⟨hi, ho, hres, hall, hext⟩

/-- The tapes cleaned between two applications of the iterated function: the
witness machine's own scratch together with the virtual-input tape. The result
tape is deliberately excluded — it still carries the value being moved. -/
def resetTargets (k : ℕ) : List (Fin (3 + (k + 2) + 0)) :=
  (List.finRange (k + 1)).map (fun j => appIdx (Fin.castSucc j))

theorem resetTargets_nodup : (resetTargets k).Nodup := by
  refine (List.nodup_finRange (k + 1)).map ?_
  intro a b hab
  exact Fin.castSucc_injective (k + 1) (appIdx_injective hab)

@[simp] theorem resetTargets_length : (resetTargets k).length = k + 1 := by
  simp [resetTargets]

theorem mem_resetTargets_iff (i : Fin (3 + (k + 2) + 0)) :
    i ∈ resetTargets k ↔ ∃ j : Fin (k + 1), appIdx (Fin.castSucc j) = i := by
  simp [resetTargets, eq_comm]

theorem wfIdx_notMem_resetTargets : wfIdx ∉ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  rintro ⟨j, hj⟩
  exact wfIdx_ne_appIdx _ hj.symm

theorem resIdx_notMem_resetTargets : resIdx ∉ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  rintro ⟨j, hj⟩
  have := appIdx_injective hj
  exact absurd (congrArg Fin.val this) (by simp; omega)

theorem vinIdx_mem_resetTargets : vinIdx ∈ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  exact ⟨Fin.last k, rfl⟩

/-- The tape cleaned after the result has been moved back. -/
def resetResult (k : ℕ) : List (Fin (3 + (k + 2) + 0)) := [resIdx]

theorem resetResult_nodup : (resetResult k).Nodup := List.nodup_singleton _

theorem wfIdx_notMem_resetResult : wfIdx ∉ resetResult (k := k) := by
  simp only [resetResult, List.mem_singleton]
  exact wfIdx_ne_appIdx _

/-- **Phases 2–3 of the body.** `δ_right_of_start` only constrains a head that
*reads* `▷`, so an arbitrary witness machine may halt with a head parked on
cell `0`. One idle step lifts every head to at least cell `1`, and one rewind
then brings the result tape's head back to exactly cell `1` — the shape both
`Complexity.resetTapesTM` (which preserves non-target tapes only when they are
parked) and `TM.copyWorkToWorkTM` (which wants its source at cell `1`)
require. -/
theorem iterPark_hoareTime (H : ℕ) (inp₀ : Tape) (hinpP : Parked inp₀)
    (hinpSI : Tape.StartInvariant inp₀)
    (W : Fin (3 + (k + 2) + 0) → Tape)
    (hSI : ∀ i, Tape.StartInvariant (W i))
    (hB : (W resIdx).head ≤ H) :
    (seqTM skipTM (rewindWorkTM resIdx)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).head = 1 ∧
        (work resIdx).cells = (W resIdx).cells ∧
        (∀ i, i ≠ resIdx → work i = (⟨max (W i).head 1, (W i).cells⟩ : Tape)))
      (1 + 1 + (H + 1 + 2)) := by
  set WA : Fin (3 + (k + 2) + 0) → Tape :=
    fun i => (⟨max (W i).head 1, (W i).cells⟩ : Tape) with hWA
  have hWAP : ∀ i, Parked (WA i) := fun i => ⟨le_max_right _ _, fun j hj => (hSI i).2 j hj⟩
  have houtP : Parked parkedBlank := parked_parkedBlank
  have houtSI : Tape.StartInvariant parkedBlank := startInvariant_initNil.move Dir3.right
  have hinpEq : (⟨max inp₀.head 1, inp₀.cells⟩ : Tape) = inp₀ :=
    Tape.ext (by show max inp₀.head 1 = inp₀.head; have := hinpP.1; omega) rfl
  have houtEq : (⟨max parkedBlank.head 1, parkedBlank.cells⟩ : Tape) = parkedBlank :=
    Tape.ext (by show max parkedBlank.head 1 = parkedBlank.head; have := houtP.1; omega) rfl
  have hA' : (skipTM (n := 3 + (k + 2) + 0)).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ work = WA ∧ out = parkedBlank) 1 :=
    (parkAll_hoareTime inp₀ W parkedBlank hinpSI hSI houtSI).strengthen_post (by
      rintro inp work out ⟨hi, hw, ho⟩
      exact ⟨hi.trans hinpEq, funext hw, ho.trans houtEq⟩)
  have hP : ∀ (inp : Tape) (work : Fin (3 + (k + 2) + 0) → Tape) (out : Tape)
      (inp' : Tape) (work' : Fin (3 + (k + 2) + 0) → Tape) (out' : Tape),
      ((work resIdx).cells = (W resIdx).cells ∧ inp = inp₀ ∧ out = parkedBlank ∧
        ∀ i, i ≠ resIdx → work i = WA i) →
      (work' resIdx).cells = (work resIdx).cells →
      (work' resIdx).head = 1 →
      (∀ i, i ≠ resIdx → work' i = work i) →
      inp' = inp → out'.cells = out.cells → out'.head = out.head →
      ((work' resIdx).cells = (W resIdx).cells ∧ inp' = inp₀ ∧ out' = parkedBlank ∧
        ∀ i, i ≠ resIdx → work' i = WA i) := by
    rintro inp work out inp' work' out' ⟨hc, rfl, rfl, hrest⟩ hc' _ hkeep rfl hoc hoh
    exact ⟨hc'.trans hc, rfl, Tape.ext hoh hoc,
      fun i hi => (hkeep i hi).trans (hrest i hi)⟩
  have hC := rewindWorkTM_hoareTime_frame (n := 3 + (k + 2) + 0) resIdx (H + 1)
    (P := fun inp work out => (work resIdx).cells = (W resIdx).cells ∧
      inp = inp₀ ∧ out = parkedBlank ∧ ∀ i, i ≠ resIdx → work i = WA i) hP
  have hpreC : ∀ (inp : Tape) (work : Fin (3 + (k + 2) + 0) → Tape) (out : Tape),
      (inp = inp₀ ∧ work = WA ∧ out = parkedBlank) →
      ((work resIdx).cells 0 = Γ.start ∧
        (∀ j, j ≥ 1 → (work resIdx).cells j ≠ Γ.start) ∧
        (work resIdx).head ≤ H + 1 ∧
        inp.read ≠ Γ.start ∧
        out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
        (∀ i, i ≠ resIdx → (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧
        ((work resIdx).cells = (W resIdx).cells ∧ inp = inp₀ ∧ out = parkedBlank ∧
          ∀ i, i ≠ resIdx → work i = WA i)) := by
    rintro inp work out ⟨hi, hw, ho⟩
    subst hw
    refine ⟨(hSI resIdx).1, fun j hj => (hSI resIdx).2 j hj, ?_,
      by rw [hi]; exact hinpP.read_ne_start, by rw [ho]; exact houtP.read_ne_start,
      by rw [ho]; exact houtP.1,
      fun i _ => ⟨(hWAP i).read_ne_start, (hWAP i).1⟩, rfl, hi, ho, fun i _ => rfl⟩
    show max (W resIdx).head 1 ≤ H + 1
    omega
  have hC' := hC.weaken_pre hpreC
  refine (seqTM_hoareTime _ _ hA' ?_ hC').strengthen_post ?_
  · rintro inp work out ⟨rfl, rfl, rfl⟩
    exact ⟨transitionInput_eq_self hinpP.read_ne_start,
      funext fun i => transitionTape_eq_self (hWAP i).read_ne_start,
      transitionTape_eq_self houtP.read_ne_start⟩
  · rintro inp work out ⟨hh, hc, hi, ho, hrest⟩
    exact ⟨hi, ho, hh, hc, hrest⟩

theorem rfIdx_ne_wfIdx : rfIdx (k := k) ≠ wfIdx := by
  intro h; exact absurd (congrArg Fin.val h) (by simp)

theorem junkIdx_ne_wfIdx : junkIdx (k := k) ≠ wfIdx := by
  intro h; exact absurd (congrArg Fin.val h) (by simp)

theorem resIdx_ne_wfIdx : resIdx (k := k) ≠ wfIdx := fun h => wfIdx_ne_appIdx _ h.symm

theorem rfIdx_notMem_resetTargets : rfIdx ∉ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  rintro ⟨j, hj⟩
  exact rfIdx_ne_appIdx _ hj.symm

theorem junkIdx_notMem_resetTargets : junkIdx ∉ resetTargets (k := k) := by
  rw [mem_resetTargets_iff]
  rintro ⟨j, hj⟩
  exact junkIdx_ne_appIdx _ hj.symm

/-- **Phase 4 of the body.** Blank the witness machine's scratch tapes and the
virtual-input tape, leaving the result tape (which carries the value being
moved), both fuel registers, and the junk tape exactly as they were. -/
theorem iterResetScratch_hoareTime (H : ℕ) (hH : 1 ≤ H)
    (inp₀ : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (W : Fin (3 + (k + 2) + 0) → Tape)
    (hSI : ∀ i, Tape.StartInvariant (W i))
    (hB : ∀ j : Fin (k + 1), (W (appIdx (Fin.castSucc j))).head ≤ H)
    (hfar : ∀ j : Fin (k + 1), ∀ c, H < c → (W (appIdx (Fin.castSucc j))).cells c = Γ.blank)
    (hwf : W wfIdx = regTape H) :
    (resetTapesTM (resetTargets k) wfIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).head = 1 ∧
        (work resIdx).cells = (W resIdx).cells ∧
        (∀ i, i ≠ resIdx → work i = (⟨max (W i).head 1, (W i).cells⟩ : Tape)))
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        (work resIdx).head = 1 ∧
        (work resIdx).cells = (W resIdx).cells ∧
        (∀ j : Fin (k + 1), work (appIdx (Fin.castSucc j)) = parkedBlank) ∧
        work wfIdx = regTape H ∧
        work rfIdx = (⟨max (W rfIdx).head 1, (W rfIdx).cells⟩ : Tape) ∧
        work junkIdx = (⟨max (W junkIdx).head 1, (W junkIdx).cells⟩ : Tape))
      ((k + 1) * (H + 4) + H * 4 + 8 + 1 + ((k + 1) * (H + 4) + 1)) := by
  intro inp work out hpre
  obtain ⟨hi, ho, hrh, hrc, hrest⟩ := hpre
  rw [hi, ho]
  have hworkSI : ∀ j, j ≠ wfIdx → Tape.StartInvariant (work j) := by
    intro j _
    by_cases hjr : j = resIdx
    · exact ⟨by rw [hjr, hrc]; exact (hSI resIdx).1,
        fun c hc => by rw [hjr, hrc]; exact (hSI resIdx).2 c hc⟩
    · rw [hrest j hjr]
      exact ⟨(hSI j).1, fun c hc => (hSI j).2 c hc⟩
  have hbnd : ∀ j, j ∈ resetTargets k →
      (work j).head ≤ H ∧ ∀ c, H < c → (work j).cells c = Γ.blank := by
    intro j hj
    obtain ⟨j', rfl⟩ := (mem_resetTargets_iff j).mp hj
    have hne : appIdx (Fin.castSucc j') ≠ resIdx := by
      intro hc
      exact absurd (congrArg Fin.val (appIdx_injective hc)) (by simp; omega)
    rw [hrest _ hne]
    refine ⟨?_, fun c hc => hfar j' c hc⟩
    show max (W (appIdx (Fin.castSucc j'))).head 1 ≤ H
    have := hB j'
    omega
  have hwfEq : work wfIdx = regTape H := by
    rw [hrest wfIdx (fun h => resIdx_ne_wfIdx h.symm), hwf]
    refine Tape.ext ?_ rfl
    show max (regTape H).head 1 = 1
    rw [regT_head]
    omega
  obtain ⟨c', t, ht, hreach, hhalt, hi', ho', hts, hR', hkeep⟩ :=
    resetTapesTM_hoareTime_of_bounds (resetTargets k) resetTargets_nodup wfIdx
      wfIdx_notMem_resetTargets H inp₀ work parkedBlank hinpSI hinpP rfl
      (fun j hjw hjt => by
        by_cases hjr : j = resIdx
        · exact ⟨by rw [hjr, hrh], fun c hc => by
            rw [hjr, hrc]; exact (hSI resIdx).2 c hc⟩
        · rw [hrest j hjr]
          exact ⟨le_max_right _ _, fun c hc => (hSI j).2 c hc⟩)
      inp₀ work parkedBlank ⟨rfl, rfl, hworkSI, hbnd, hwfEq, fun _ _ _ => rfl⟩
  rw [resetTargets_length] at ht
  refine ⟨c', t, ht, hreach, hhalt, hi', ho', ?_, ?_, ?_, hR', ?_, ?_⟩
  · rw [hkeep resIdx (fun h => resIdx_ne_wfIdx h) resIdx_notMem_resetTargets]; exact hrh
  · rw [hkeep resIdx (fun h => resIdx_ne_wfIdx h) resIdx_notMem_resetTargets]; exact hrc
  · intro j
    exact hts _ ((mem_resetTargets_iff _).mpr ⟨j, rfl⟩)
  · rw [hkeep rfIdx rfIdx_ne_wfIdx rfIdx_notMem_resetTargets]
    exact hrest rfIdx (fun h => rfIdx_ne_appIdx _ h)
  · rw [hkeep junkIdx junkIdx_ne_wfIdx junkIdx_notMem_resetTargets]
    exact hrest junkIdx (fun h => junkIdx_ne_appIdx _ h)

/-- `TM.applyPre` in closed form: the virtual-input tape carries the value, and
every other tape of the block is blank. -/
theorem applyPre_eq (M : TM k) (x : List Bool) (inp₀ : Tape) (j : Fin (k + 2)) :
    TM.applyPre M x inp₀ j =
      if j = Fin.castSucc (Fin.last k) then (Tape.init (x.map Γ.ofBool)).move Dir3.right
      else parkedBlank := by
  refine Fin.lastCases ?_ ?_ j
  · rw [TM.applyPre, Fin.snoc_last, if_neg]
    intro hc
    exact absurd (congrArg Fin.val hc) (by simp)
  · intro j'
    rw [TM.applyPre, Fin.snoc_castSucc]
    show (TM.retargetInputStartedCfg M x inp₀).work j' = _
    rw [TM.retargetInputStartedCfg]
    dsimp only
    by_cases hj : j' = Fin.last k
    · rw [hj, if_neg (by simp), if_pos rfl]
    · have hlt : j'.val < k := by
        have := j'.isLt
        rcases Nat.lt_or_ge j'.val k with h | h
        · exact h
        · exact absurd (Fin.ext (show j'.val = (Fin.last k).val by
            rw [Fin.val_last]; omega)) hj
      rw [if_pos hlt, if_neg (fun hc => hj (Fin.castSucc_injective (k + 1) hc))]
      rfl

theorem resIdx_ne_vinIdx : resIdx (k := k) ≠ vinIdx := by
  intro h
  exact absurd (congrArg Fin.val (appIdx_injective h)) (by simp)

theorem rfIdx_ne_resIdx : rfIdx (k := k) ≠ resIdx := rfIdx_ne_appIdx _
theorem junkIdx_ne_resIdx : junkIdx (k := k) ≠ resIdx := junkIdx_ne_appIdx _
theorem wfIdx_ne_resIdx : wfIdx (k := k) ≠ resIdx := wfIdx_ne_appIdx _
theorem rfIdx_ne_vinIdx : rfIdx (k := k) ≠ vinIdx := rfIdx_ne_appIdx _
theorem junkIdx_ne_vinIdx : junkIdx (k := k) ≠ vinIdx := junkIdx_ne_appIdx _
theorem wfIdx_ne_vinIdx : wfIdx (k := k) ≠ vinIdx := wfIdx_ne_appIdx _

theorem junkIdx_ne_rfIdx : junkIdx (k := k) ≠ rfIdx := by
  intro h; exact absurd (congrArg Fin.val h) (by simp)

/-- **Phases 5–6 of the body.** Move the freshly computed value from the result
tape onto the virtual-input tape — where the next application will read it —
and then blank the result tape, restoring `TM.applyPre`'s entry shape for the
new value. -/
theorem iterFinish_hoareTime (M : TM k) (H : ℕ)
    (x : List Bool) (hx : x.length + 1 ≤ H)
    (inp₀ : Tape) (hinpP : Parked inp₀) (hinpSI : Tape.StartInvariant inp₀)
    (resT rfT junkT : Tape)
    (hresH : resT.head = 1) (hresOut : resT.HasOutput x)
    (hresSI : Tape.StartInvariant resT)
    (hresFar : ∀ c, H < c → resT.cells c = Γ.blank)
    (hrfP : Parked rfT) (hrfSI : Tape.StartInvariant rfT)
    (hjunkP : Parked junkT) (hjunkSI : Tape.StartInvariant junkT) :
    (seqTM (copyToVirtualInputTM resIdx vinIdx)
      (resetTapesTM (resetResult k) wfIdx)).HoareTime
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        work resIdx = resT ∧ work rfIdx = rfT ∧ work junkIdx = junkT ∧
        work wfIdx = regTape H ∧
        (∀ j : Fin (k + 1), work (appIdx (Fin.castSucc j)) = parkedBlank))
      (fun inp work out => inp = inp₀ ∧ out = parkedBlank ∧
        work rfIdx = rfT ∧ work junkIdx = junkT ∧ work wfIdx = regTape H ∧
        (∀ j, work (appIdx j) = TM.applyPre M x inp₀ j))
      (2 * x.length + 5 + 1 +
        (1 * (H + 4) + H * 4 + 8 + 1 + (1 * (H + 4) + 1))) := by
  have hregP : Parked (regTape H) :=
    ⟨le_refl 1, fun i hi => by
      show regCells H i ≠ Γ.start
      simp only [regCells]; split
      · omega
      · split <;> decide⟩
  have hregSI : Tape.StartInvariant (regTape H) := ⟨rfl, hregP.2⟩
  have houtP : Parked parkedBlank := parked_parkedBlank
  have hblankSI : Tape.StartInvariant parkedBlank := startInvariant_initNil.move Dir3.right
  -- the tape family entering phase 5
  set W₀ : Fin (3 + (k + 2) + 0) → Tape := fun i =>
    if i = resIdx then resT else if i = rfIdx then rfT else if i = junkIdx then junkT
    else if i = wfIdx then regTape H else parkedBlank with hW₀
  have hW₀SI : ∀ i, Tape.StartInvariant (W₀ i) := by
    intro i; rw [hW₀]; dsimp only
    split; · exact hresSI
    split; · exact hrfSI
    split; · exact hjunkSI
    split; · exact hregSI
    exact hblankSI
  have hW₀other : ∀ i, i ≠ resIdx → i ≠ vinIdx → Parked (W₀ i) := by
    intro i hir _; rw [hW₀]; dsimp only
    rw [if_neg hir]
    split; · exact hrfP
    split; · exact hjunkP
    split; · exact hregP
    exact houtP
  have hW₀res : W₀ resIdx = resT := by rw [hW₀]; simp
  have hW₀vin : W₀ vinIdx = parkedBlank := by
    rw [hW₀]
    dsimp only
    rw [if_neg (fun h => resIdx_ne_vinIdx h.symm), if_neg (fun h => rfIdx_ne_appIdx _ h.symm),
      if_neg (fun h => junkIdx_ne_appIdx _ h.symm), if_neg (fun h => wfIdx_ne_appIdx _ h.symm)]
  have hW₀app : ∀ j : Fin (k + 2), appIdx j ≠ resIdx → W₀ (appIdx j) = parkedBlank := by
    intro j hj
    rw [hW₀]
    dsimp only
    rw [if_neg hj, if_neg (fun h => rfIdx_ne_appIdx _ h.symm),
      if_neg (fun h => junkIdx_ne_appIdx _ h.symm), if_neg (fun h => wfIdx_ne_appIdx _ h.symm)]
  have hW₀rf : W₀ rfIdx = rfT := by
    rw [hW₀]
    dsimp only
    rw [if_neg rfIdx_ne_resIdx, if_pos rfl]
  have hW₀junk : W₀ junkIdx = junkT := by
    rw [hW₀]
    dsimp only
    rw [if_neg junkIdx_ne_resIdx, if_neg junkIdx_ne_rfIdx, if_pos rfl]
  have hW₀wf : W₀ wfIdx = regTape H := by
    rw [hW₀]
    dsimp only
    rw [if_neg wfIdx_ne_resIdx, if_neg (fun h => rfIdx_ne_wfIdx h.symm),
      if_neg (fun h => junkIdx_ne_wfIdx h.symm), if_pos rfl]
  -- the value tape produced by the copy, and the family after each phase
  set vinT : Tape := (Tape.init (x.map Γ.ofBool)).move Dir3.right with hvinT
  have hvinSI : Tape.StartInvariant vinT := (startInvariant_initOfBool x).move Dir3.right
  have hvinP : Parked vinT := ⟨le_refl 1, hvinSI.2⟩
  set W₁ : Fin (3 + (k + 2) + 0) → Tape :=
    Function.update (Function.update W₀ vinIdx vinT) resIdx
      (⟨x.length + 1, (W₀ resIdx).cells⟩ : Tape) with hW₁
  set W₂ : Fin (3 + (k + 2) + 0) → Tape := Function.update W₁ resIdx parkedBlank with hW₂
  have hW₁res : W₁ resIdx = (⟨x.length + 1, resT.cells⟩ : Tape) := by
    rw [hW₁, Function.update_self, hW₀res]
  have hW₁vin : W₁ vinIdx = vinT := by
    rw [hW₁, Function.update_of_ne resIdx_ne_vinIdx.symm, Function.update_self]
  have hW₁other : ∀ i, i ≠ resIdx → i ≠ vinIdx → W₁ i = W₀ i := by
    intro i hir hiv
    rw [hW₁, Function.update_of_ne hir, Function.update_of_ne hiv]
  have hW₁P : ∀ i, Parked (W₁ i) := by
    intro i
    by_cases hir : i = resIdx
    · rw [hir, hW₁res]
      exact ⟨show 1 ≤ x.length + 1 by omega, fun j hj => hresSI.2 j hj⟩
    · by_cases hiv : i = vinIdx
      · rw [hiv, hW₁vin]; exact hvinP
      · rw [hW₁other i hir hiv]; exact hW₀other i hir hiv
  -- phase 5: the copy
  have hcopy := copyToVirtualInputTM_hoareTime resIdx vinIdx resIdx_ne_vinIdx x inp₀ W₀
    parkedBlank (by rw [hW₀res]; exact hresH) (by rw [hW₀res]; exact hresOut)
    (by rw [hW₀res]; exact ⟨by omega, fun j hj => hresSI.2 j hj⟩) hW₀vin hinpP houtP hW₀other
  -- phase 6: blanking the result tape
  have hreset := resetTapesTM_hoareTime (resetResult k) resetResult_nodup wfIdx
    wfIdx_notMem_resetResult H inp₀ W₁ parkedBlank hinpSI hinpP rfl
    (fun j _ => by
      by_cases hjr : j = resIdx
      · rw [hjr, hW₁res]; exact ⟨hresSI.1, fun c hc => hresSI.2 c hc⟩
      · by_cases hjv : j = vinIdx
        · rw [hjv, hW₁vin]; exact hvinSI
        · rw [hW₁other j hjr hjv]; exact hW₀SI j)
    (fun j hj => by
      rw [List.mem_singleton.mp hj, hW₁res]
      show x.length + 1 ≤ H
      omega)
    (fun j hj c hc => by
      rw [List.mem_singleton.mp hj, hW₁res]
      exact hresFar c hc)
    (by rw [hW₁other wfIdx (fun h => resIdx_ne_wfIdx h.symm) (fun h => wfIdx_ne_appIdx _ h),
      hW₀wf])
    (fun j hjw hjt => hW₁P j)
  have hreset' : (resetTapesTM (resetResult k) wfIdx).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = W₁ ∧ out = parkedBlank)
      (fun inp work out => inp = inp₀ ∧ work = W₂ ∧ out = parkedBlank)
      (1 * (H + 4) + H * 4 + 8 + 1 + (1 * (H + 4) + 1)) := by
    refine (hreset.strengthen_post ?_).mono_bound (by simp [resetResult])
    rintro inp work out ⟨hi, ho, hts, hR, hrest⟩
    refine ⟨hi, funext fun j => ?_, ho⟩
    by_cases hjr : j = resIdx
    · rw [hjr, hts resIdx (by simp [resetResult]), hW₂, Function.update_self]
      rfl
    · rw [hW₂, Function.update_of_ne hjr]
      by_cases hjw : j = wfIdx
      · rw [hjw, hR, hW₁other wfIdx (fun h => resIdx_ne_wfIdx h.symm)
          (fun h => wfIdx_ne_appIdx _ h), hW₀wf]
      · exact hrest j hjw (by simp only [resetResult, List.mem_singleton]; exact hjr)
  -- chain the two phases and read the result off
  have hpre_imp : ∀ (inp : Tape) (work : Fin (3 + (k + 2) + 0) → Tape) (out : Tape),
      (inp = inp₀ ∧ out = parkedBlank ∧
        work resIdx = resT ∧ work rfIdx = rfT ∧ work junkIdx = junkT ∧
        work wfIdx = regTape H ∧
        (∀ j : Fin (k + 1), work (appIdx (Fin.castSucc j)) = parkedBlank)) →
      (inp = inp₀ ∧ work = W₀ ∧ out = parkedBlank) := by
    rintro inp work out ⟨hi, ho, hres, hrf, hjunk, hwf, happ⟩
    refine ⟨hi, funext fun i => ?_, ho⟩
    rcases layout_cases i with hi' | hi' | hi' | ⟨j, hi'⟩
    · rw [hi', hrf, hW₀rf]
    · rw [hi', hwf, hW₀wf]
    · rw [hi', hjunk, hW₀junk]
    · subst hi'
      refine Fin.lastCases ?_ ?_ j
      · rw [show appIdx (Fin.last (k + 1)) = resIdx from rfl, hres, hW₀res]
      · intro j'
        rw [happ j', hW₀app _ (fun h => absurd (appIdx_injective h)
          (Fin.castSucc_lt_last j').ne)]
  refine (((seqTM_det (copyToVirtualInputTM resIdx vinIdx)
    (resetTapesTM (resetResult k) wfIdx) hinpP houtP hW₁P hcopy
    hreset').weaken_pre hpre_imp).strengthen_post ?_).mono_bound le_rfl
  · rintro inp work out ⟨hi, hw, ho⟩
    subst hw
    refine ⟨hi, ho, ?_, ?_, ?_, fun j => ?_⟩
    · rw [hW₂, Function.update_of_ne rfIdx_ne_resIdx,
        hW₁other rfIdx rfIdx_ne_resIdx rfIdx_ne_vinIdx, hW₀rf]
    · rw [hW₂, Function.update_of_ne junkIdx_ne_resIdx,
        hW₁other junkIdx junkIdx_ne_resIdx junkIdx_ne_vinIdx, hW₀junk]
    · rw [hW₂, Function.update_of_ne wfIdx_ne_resIdx,
        hW₁other wfIdx wfIdx_ne_resIdx wfIdx_ne_vinIdx, hW₀wf]
    · rw [applyPre_eq]
      by_cases hj : j = Fin.castSucc (Fin.last k)
      · rw [if_pos hj, hj, show appIdx (Fin.castSucc (Fin.last k)) = vinIdx from rfl,
          hW₂, Function.update_of_ne resIdx_ne_vinIdx.symm, hW₁vin]
      · rw [if_neg hj]
        by_cases hjl : j = Fin.last (k + 1)
        · rw [hjl, show appIdx (Fin.last (k + 1)) = resIdx from rfl, hW₂, Function.update_self]
        · have hjr : appIdx j ≠ resIdx := fun h =>
            hjl (appIdx_injective (h.trans (rfl : resIdx = appIdx (Fin.last (k + 1)))))
          have hjv : appIdx j ≠ vinIdx := fun h =>
            hj (appIdx_injective (h.trans (rfl : vinIdx = appIdx (Fin.castSucc (Fin.last k)))))
          rw [hW₂, Function.update_of_ne hjr, hW₁other _ hjr hjv, hW₀app j hjr]

end IterateLayout

end Complexity
