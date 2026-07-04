import Complexitylib.Models.TuringMachine.Arith

/-!
# Clock constructibility for the time hierarchy theorem

`TM.ClockConstructible g` is the constructibility hypothesis of the
forthcoming time hierarchy theorem: an 8-tape machine can write the unary
clock `regT (g n)` on work tape 6 in time `O(g n + n)`, ghost-preserving
the rest of the diagonalizer's tape layout.

Contents:

1. `TM.ClockConstructible` — the layout-pinned definition (see its
   docstring for the design tradeoffs), plus the congruence helper
   `ClockConstructible.congr`.
2. `TM.clockLenTM` and `TM.clockConstructible_succ` — the base instance
   `ClockConstructible (fun n => n + 1)` via a single input sweep.
3. `TM.moveClockTM`, `TM.clockMulTM` and `ClockConstructible.mul_succ` —
   closure under multiplication by `n + 1`: move the clock to the scratch
   tape, then append it to the clock tape's frontier once per input
   position.
4. `TM.clockConstructible_pow` — `ClockConstructible (fun n => (n + 1) ^ k)`
   for all `k ≥ 1`: the polynomial clocks of the hierarchy theorem.

All machines are hand-written in the UTM house style (small inductive
state, ghost-framed step/run lemmas as in `UTM/Clock.lean` and
`InputLen.lean`).
-/

namespace TM

-- ════════════════════════════════════════════════════════════════════════
-- Small helpers: input-tape cells, blank tapes, register cells
-- ════════════════════════════════════════════════════════════════════════

/-- The canonical parked blank tape (`liftTM`'s pinned extra tape) is the
    zero register. -/
theorem initTape_move_right_eq_regT_zero :
    (initTape []).move Dir3.right = regT 0 := by
  refine Tape.ext' rfl ?_
  show (initTape []).cells = regCells 0
  funext j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  · show (initTape []).cells j = regCells 0 j
    rw [regCells_blank (by omega)]
    simp only [initTape]
    rw [if_neg (by omega : ¬ j = 0)]
    simp

private theorem inpCells_zero (x : List Bool) :
    (initTape (x.map Γ.ofBool)).cells 0 = Γ.start := by
  simp [initTape]

private theorem inpCells_bit (x : List Bool) {k : ℕ} (hk : k < x.length) :
    (initTape (x.map Γ.ofBool)).cells (k + 1) = Γ.ofBool x[k] := by
  simp only [initTape]
  rw [if_neg (by omega : ¬ k + 1 = 0)]
  rw [show k + 1 - 1 = k from by omega]
  rw [List.getElem?_eq_getElem (by simpa using hk)]
  simp

private theorem inpCells_blank (x : List Bool) {j : ℕ} (hj : x.length + 1 ≤ j) :
    (initTape (x.map Γ.ofBool)).cells j = Γ.blank := by
  simp only [initTape]
  rw [if_neg (by omega : ¬ j = 0)]
  rw [List.getElem?_eq_none (by simpa using by omega : (x.map Γ.ofBool).length ≤ j - 1)]
  rfl

private theorem ofBool_ne_blank (b : Bool) : Γ.ofBool b ≠ Γ.blank := by
  cases b <;> decide

private theorem ofBool_ne_start (b : Bool) : Γ.ofBool b ≠ Γ.start := by
  cases b <;> decide

private theorem inpCells_ne_start (x : List Bool) {j : ℕ} (hj : 1 ≤ j) :
    (initTape (x.map Γ.ofBool)).cells j ≠ Γ.start := by
  rcases Nat.lt_or_ge j (x.length + 1) with hlt | hge
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [inpCells_bit x (by omega)]
    exact ofBool_ne_start _
  · rw [inpCells_blank x hge]
    decide

private theorem regCells_ne_start' {v j : ℕ} (hj : 1 ≤ j) :
    regCells v j ≠ Γ.start := by
  rw [regCells, if_neg (by omega)]
  split <;> decide

/-- Erasing the top mark shrinks the register cells by one. -/
private theorem regCells_erase (d : ℕ) :
    Function.update (regCells (d + 1)) (d + 1) Γ.blank = regCells d := by
  funext j
  rw [Function.update_apply]
  split
  · next h =>
    subst h
    exact (regCells_blank (by omega)).symm
  · next h =>
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rfl
    · rcases Nat.lt_or_ge d j with hlt | hge
      · rw [regCells_blank (by omega), regCells_blank (by omega)]
      · rw [regCells_one (by omega) (by omega), regCells_one (by omega) (by omega)]

/-- The output-tape frame carried through all clock-construction phases:
    head parked at cell 1, sentinel at cell 0, no spurious `▷`s. The clock
    machines never write the output tape, so this frame is preserved
    literally. -/
private def outF (out : Tape) : Prop :=
  out.head = 1 ∧ out.cells 0 = Γ.start ∧ ∀ j, 1 ≤ j → out.cells j ≠ Γ.start

private theorem outF_read_ne_start {out : Tape} (h : outF out) :
    out.read ≠ Γ.start := by
  rw [Tape.read, h.1]
  exact h.2.2 1 le_rfl

-- ════════════════════════════════════════════════════════════════════════
-- The definition
-- ════════════════════════════════════════════════════════════════════════

/-- **Clock constructibility** — the hypothesis of the time hierarchy
    theorem. `g` is clock-constructible if some 8-tape machine, started on
    input `x` in the diagonalizer's tape layout, writes the unary register
    `regT (g |x|)` on work tape 6 within `C * (g |x| + |x| + 1)` steps,
    disturbing nothing else.

    The definition is deliberately **layout-pinned** rather than maximally
    general: the diagonalizer `D` is an 8-tape machine whose UTM phases run
    on tapes 0–5, whose encoded pair ⟨M, x⟩ lives on tape 7, and whose
    clock lives on tape 6. Instead of a lift-and-frame story, the
    hypothesis quantifies over the ghost frame `work₀` directly:

    * tapes 0–4 and 7 may hold **arbitrary parked content** (head ≥ 1,
      reading a non-`▷` symbol) and must be preserved **exactly**;
    * tape 6 (the clock) starts as the canonical parked blank tape
      `(initTape []).move Dir3.right` (the tape the `liftTM` combinators
      pin blank extras to; it equals `regT 0`) and ends as `regT (g |x|)`;
    * tape 5 is a **designated scratch tape**: it must also start blank,
      and it is restored blank — this is exactly the `work i = work₀ i`
      clause at `i = 5`, since `work₀ 5` is pinned blank. `D` runs
      clock-initialization before any UTM phase touches tapes 0–5, so
      granting the clock machine one blank scratch tape costs nothing,
      and it makes the closure constructions (multiplication, hence all
      polynomials) feasible;
    * the input tape is read-only, so only its cells are pinned; its head
      is returned to cell 1 (needed to chain clock phases sequentially);
    * the output tape must be `▷`-clean with head parked at cell 1, and is
      returned in the same state (clock machines never write the output).
-/
def ClockConstructible (g : ℕ → ℕ) : Prop :=
  ∃ (tm : TM 8) (C : ℕ),
    ∀ (x : List Bool) (work₀ : Fin 8 → Tape),
      (∀ i, 1 ≤ (work₀ i).head ∧ (work₀ i).read ≠ Γ.start) →
      work₀ (5 : Fin 8) = (initTape []).move Dir3.right →
      work₀ (6 : Fin 8) = (initTape []).move Dir3.right →
      tm.HoareTime
        (fun inp work out =>
          inp = initTape (x.map Γ.ofBool) ∧ work = work₀ ∧
          out.head = 1 ∧ out.cells 0 = Γ.start ∧
          (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
        (fun inp work out =>
          inp.cells = (initTape (x.map Γ.ofBool)).cells ∧ inp.head = 1 ∧
          (∀ i, i ≠ (6 : Fin 8) → work i = work₀ i) ∧
          work (6 : Fin 8) = regT (g x.length) ∧
          out.head = 1 ∧ out.cells 0 = Γ.start ∧
          (∀ j, 1 ≤ j → out.cells j ≠ Γ.start))
        (C * (g x.length + x.length + 1))

/-- `ClockConstructible` respects pointwise-equal clock bounds. -/
theorem ClockConstructible.congr {g g' : ℕ → ℕ} (h : ClockConstructible g)
    (hgg' : ∀ n, g n = g' n) : ClockConstructible g' :=
  funext hgg' ▸ h

-- ════════════════════════════════════════════════════════════════════════
-- clockLenTM: write |x| + 1 marks on the clock tape
-- ════════════════════════════════════════════════════════════════════════

/-- **Measure the input length plus one into the clock tape**: scan the
    input left to right writing one mark on tape 6 per bit, write one
    final mark at the input's first blank (the `+ 1`), then rewind both
    heads to cell 1 in lockstep. Every other tape idles throughout. -/
def clockLenTM : TM 8 where
  Q := IncPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if iHead = Γ.start then
        (.scan, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      else if iHead = Γ.blank then
        (.back, fun i => if i = 6 then Γw.one else readBackWrite (wHeads i),
         readBackWrite oHead, Dir3.left,
         fun i => if i = 6 then (if wHeads 6 = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (.scan, fun i => if i = 6 then Γw.one else readBackWrite (wHeads i),
         readBackWrite oHead, Dir3.right,
         fun i => if i = 6 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads 6 = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => if i = 6 then Dir3.right else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         (if iHead = Γ.start then Dir3.right else Dir3.left),
         fun i => if i = 6 then Dir3.left else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .scan =>
      dsimp only []
      split
      · exact ⟨fun _ => rfl, fun i hi => idleDir_right_of_start hi,
          idleDir_right_of_start⟩
      · next hns =>
        split
        · refine ⟨fun hi => absurd hi hns, fun i hi => ?_, idleDir_right_of_start⟩
          dsimp only []
          by_cases hir : i = (6 : Fin 8)
          · subst hir; rw [if_pos rfl, if_pos hi]
          · rw [if_neg hir]; exact idleDir_right_of_start hi
        · refine ⟨fun _ => rfl, fun i hi => ?_, idleDir_right_of_start⟩
          dsimp only []
          by_cases hir : i = (6 : Fin 8)
          · rw [if_pos hir]
          · rw [if_neg hir]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨fun _ => rfl, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (6 : Fin 8)
        · rw [if_pos hir]
        · rw [if_neg hir]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨fun hi => by rw [if_pos hi], fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir : i = (6 : Fin 8)
        · subst hir; exact absurd hi hns
        · rw [if_neg hir]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section ClockLen

private theorem clockLen_ne_halt {s : IncPhase} (h : s ≠ .done)
    {c : Cfg 8 clockLenTM.Q} (hst : c.state = s) :
    ¬ c.state = clockLenTM.qhalt := by
  rw [hst]
  show ¬ s = IncPhase.done
  exact h

/-- `scan` on the input sentinel: only the input head moves (right). -/
private theorem clockLen_step_scan_start (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .scan) (hi : c.input.read = Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .scan, input := c.input.move .right,
        work := c.work, output := c.output } := by
  rw [TM.step, if_neg (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hi, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `scan` over a bit: mark the clock, advance the input and clock heads. -/
private theorem clockLen_step_scan_bit (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .scan) (hns : c.input.read ≠ Γ.start)
    (hbl : c.input.read ≠ Γ.blank)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .scan, input := c.input.move .right,
        work := Function.update c.work 6 (((c.work 6).write Γw.one).move .right),
        output := c.output } := by
  rw [TM.step, if_neg (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hns, hbl, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      simp only [↓reduceIte, Function.update_self]
    · rw [if_neg hir, if_neg hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `scan` at the input's first blank: write the final mark and turn both
    heads around. -/
private theorem clockLen_step_scan_blank (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .scan) (hbl : c.input.read = Γ.blank)
    (hclk : (c.work 6).read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .back, input := c.input.move .left,
        work := Function.update c.work 6 (((c.work 6).write Γw.one).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hbl, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      simp only [↓reduceIte, Function.update_self]
      rw [if_neg hclk]
    · rw [if_neg hir, if_neg hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` off the sentinel: input and clock heads keep rewinding. -/
private theorem clockLen_step_back_left (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .back) (hclk : (c.work 6).read ≠ Γ.start)
    (hins : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .back, input := c.input.move .left,
        work := Function.update c.work 6 ((c.work 6).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hclk, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · rw [if_neg hins]
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      rw [if_pos rfl, Function.update_self, writeAndMove_readBack _ hclk]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` on the sentinel: input and clock heads step right to cell 1. -/
private theorem clockLen_step_back_start (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .back) (hs : (c.work 6).read = Γ.start)
    (hcr : ∀ j, 1 ≤ j → (c.work 6).cells j ≠ Γ.start)
    (hoth : ∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .park, input := c.input.move .right,
        work := Function.update c.work 6 ((c.work 6).move .right),
        output := c.output } := by
  have h0 : (c.work 6).head = 0 := by
    by_contra hc
    exact hcr _ (by omega) hs
  rw [TM.step, if_neg (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, rfl, ?_, ?_⟩)
  · funext i
    by_cases hir : i = (6 : Fin 8)
    · subst hir
      rw [if_pos rfl, Function.update_self]
      show ((c.work 6).write _).move Dir3.right = (c.work 6).move .right
      congr 1
      rw [Tape.write, if_pos h0]
    · rw [if_neg hir, Function.update_of_ne hir]
      exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `park`: one idle step into `done`. -/
private theorem clockLen_step_park (c : Cfg 8 clockLenTM.Q)
    (hst : c.state = .park) (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    clockLenTM.step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, if_neg (clockLen_ne_halt (by decide) hst)]
  simp only [clockLenTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_id hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- The lockstep scan: one clock mark per input bit. -/
private theorem clockLen_scan_run (x : List Bool) (m : ℕ) :
    ∀ (k : ℕ), x.length = k + m →
      ∀ (c : Cfg 8 clockLenTM.Q),
      c.state = .scan →
      c.input.cells = (initTape (x.map Γ.ofBool)).cells → c.input.head = k + 1 →
      (∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 6).cells = regCells k → (c.work 6).head = k + 1 →
      ∃ c', clockLenTM.reachesIn m c c' ∧
        c'.state = .scan ∧
        c'.input.cells = (initTape (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length + 1 ∧
        (∀ i, i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 6).cells = regCells x.length ∧
        (c'.work 6).head = x.length + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst hic hih hoth hout hcl hhd
    obtain rfl : x.length = k := by omega
    exact ⟨c, .zero, hst, hic, hih, fun _ _ => rfl, hcl, hhd, rfl⟩
  | succ m ih =>
    intro k hk c hst hic hih hoth hout hcl hhd
    have hread : c.input.read = Γ.ofBool (x[k]'(by omega)) := by
      rw [Tape.read, hih, hic]
      exact inpCells_bit x (by omega)
    have hns : c.input.read ≠ Γ.start := by
      rw [hread]; exact ofBool_ne_start _
    have hbl : c.input.read ≠ Γ.blank := by
      rw [hread]; exact ofBool_ne_blank _
    have hstep := clockLen_step_scan_bit c hst hns hbl hoth hout
    have hq₁cells : (((c.work 6).write Γw.one).move .right).cells
        = regCells (k + 1) := by
      rw [tape_move_cells, Tape.write, if_neg (by rw [hhd]; omega)]
      show Function.update (c.work 6).cells (c.work 6).head Γw.one.toΓ = _
      rw [hhd, hcl]
      exact regCells_update_succ k
    have hq₁head : (((c.work 6).write Γw.one).move .right).head = (k + 1) + 1 := by
      show ((c.work 6).write Γw.one).head + 1 = _
      rw [tape_write_head, hhd]
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input.move .right,
          work := Function.update c.work 6 (((c.work 6).write Γw.one).move .right),
          output := c.output } rfl
        (by show (c.input.move .right).cells = _
            rw [tape_move_cells]
            exact hic)
        (by show c.input.head + 1 = (k + 1) + 1
            rw [hih])
        (fun i hi => by
          show ((Function.update c.work 6 _ i)).read ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by show (Function.update c.work 6 _ 6).cells = _
            rw [Function.update_self]
            exact hq₁cells)
        (by show (Function.update c.work 6 _ 6).head = _
            rw [Function.update_self]
            exact hq₁head)
    refine ⟨c', .step hstep hreach, h1, h2, h3, ?_, h5, h6, h7⟩
    intro i hi
    rw [h4 i hi]
    show Function.update c.work 6 _ i = c.work i
    rw [Function.update_of_ne hi]

/-- The lockstep rewind: input and clock heads return to cell 1. -/
private theorem clockLen_back_run (x : List Bool) (h : ℕ) :
    ∀ (c : Cfg 8 clockLenTM.Q),
      c.state = .back →
      c.input.cells = (initTape (x.map Γ.ofBool)).cells → c.input.head = h →
      (∀ i, i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 6).cells 0 = Γ.start →
      (∀ j, 1 ≤ j → (c.work 6).cells j ≠ Γ.start) →
      (c.work 6).head = h →
      ∃ c', clockLenTM.reachesIn (h + 2) c c' ∧
        c'.state = .done ∧
        c'.input.cells = (initTape (x.map Γ.ofBool)).cells ∧ c'.input.head = 1 ∧
        (∀ i, i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 6).cells = (c.work 6).cells ∧ (c'.work 6).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hic hih hoth hout hc0 hcr hhd
    have hs : (c.work 6).read = Γ.start := by rw [Tape.read, hhd]; exact hc0
    have hstep₁ := clockLen_step_back_start c hst hs hcr hoth hout
    have hstep₂ := clockLen_step_park
      { state := .park, input := c.input.move .right,
        work := Function.update c.work 6 ((c.work 6).move .right),
        output := c.output } rfl
      (by show (c.input.move .right).read ≠ Γ.start
          rw [Tape.read, tape_move_cells]
          show c.input.cells (c.input.head + 1) ≠ Γ.start
          rw [hih, hic]
          exact inpCells_ne_start x (by omega))
      (fun i => by
        by_cases hir : i = (6 : Fin 8)
        · subst hir
          show (Function.update c.work 6 ((c.work 6).move .right) 6).read ≠ Γ.start
          rw [Function.update_self]
          show (c.work 6).cells ((c.work 6).head + 1) ≠ Γ.start
          exact hcr _ (by omega)
        · show (Function.update c.work 6 _ i).read ≠ Γ.start
          rw [Function.update_of_ne hir]
          exact hoth i hir)
      hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · show (c.input.move .right).cells = _
      rw [tape_move_cells]
      exact hic
    · show c.input.head + 1 = 1
      rw [hih]
    · intro i hi
      show Function.update c.work 6 ((c.work 6).move .right) i = c.work i
      rw [Function.update_of_ne hi]
    · show (Function.update c.work 6 ((c.work 6).move .right) 6).cells = _
      rw [Function.update_self]
      rfl
    · show (Function.update c.work 6 ((c.work 6).move .right) 6).head = 1
      rw [Function.update_self]
      show (c.work 6).head + 1 = 1
      rw [hhd]
  | succ h ih =>
    intro c hst hic hih hoth hout hc0 hcr hhd
    have hclk : (c.work 6).read ≠ Γ.start := by
      rw [Tape.read, hhd]
      exact hcr (h + 1) (by omega)
    have hins : c.input.read ≠ Γ.start := by
      rw [Tape.read, hih, hic]
      exact inpCells_ne_start x (by omega)
    have hstep₁ := clockLen_step_back_left c hst hclk hins hoth hout
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7⟩ :=
      ih { state := .back, input := c.input.move .left,
           work := Function.update c.work 6 ((c.work 6).move .left),
           output := c.output } rfl
        (by show (c.input.move .left).cells = _
            rw [tape_move_cells]
            exact hic)
        (by show c.input.head - 1 = h
            rw [hih]
            omega)
        (fun i hi => by
          show (Function.update c.work 6 _ i).read ≠ Γ.start
          rw [Function.update_of_ne hi]
          exact hoth i hi)
        hout
        (by show (Function.update c.work 6 _ 6).cells 0 = _
            rw [Function.update_self]
            exact hc0)
        (fun j hj => by
          show (Function.update c.work 6 _ 6).cells j ≠ _
          rw [Function.update_self]
          exact hcr j hj)
        (by show (Function.update c.work 6 _ 6).head = h
            rw [Function.update_self]
            show (c.work 6).head - 1 = h
            rw [hhd]
            omega)
    refine ⟨c', .step hstep₁ hreach, h1, h2, h3, ?_, ?_, h6, h7⟩
    · intro i hi
      rw [h4 i hi]
      show Function.update c.work 6 ((c.work 6).move .left) i = c.work i
      rw [Function.update_of_ne hi]
    · rw [h5]
      show (Function.update c.work 6 ((c.work 6).move .left) 6).cells = _
      rw [Function.update_self]
      rfl

/-- **`clockLenTM` Hoare specification.** From the initial input tape and a
    blank clock, write `regT (|x| + 1)` on tape 6 in `2|x| + 4` steps,
    returning the input head to cell 1 and preserving everything else
    exactly. -/
private theorem clockLenTM_hoareTime (x : List Bool) (work₀ : Fin 8 → Tape)
    (hoth : ∀ i : Fin 8, i ≠ 6 → (work₀ i).read ≠ Γ.start)
    (hclk : work₀ 6 = regT 0) :
    clockLenTM.HoareTime
      (fun inp work out =>
        inp = initTape (x.map Γ.ofBool) ∧ work = work₀ ∧ outF out)
      (fun inp work out =>
        inp = ⟨1, (initTape (x.map Γ.ofBool)).cells⟩ ∧
        (∀ i, i ≠ (6 : Fin 8) → work i = work₀ i) ∧
        work 6 = regT (x.length + 1) ∧ outF out)
      (2 * x.length + 4) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  have houtr : out.read ≠ Γ.start := outF_read_ne_start hout
  -- step off the input sentinel
  have hstep₁ := clockLen_step_scan_start
    { state := clockLenTM.qstart, input := initTape (x.map Γ.ofBool),
      work := work, output := out } rfl
    (by show (initTape (x.map Γ.ofBool)).cells 0 = Γ.start
        exact inpCells_zero x)
    (fun i => by
      by_cases hir : i = (6 : Fin 8)
      · subst hir
        show (work 6).read ≠ Γ.start
        rw [hclk]
        exact (regT_parked 0).read_ne_start
      · exact hoth i hir)
    houtr
  -- the scan sweep over the bits
  obtain ⟨c₂, hr₂, hst₂, hic₂, hih₂, hw₂, hcl₂, hhd₂, ho₂⟩ :=
    clockLen_scan_run x x.length 0 (by omega)
      { state := .scan, input := (initTape (x.map Γ.ofBool)).move .right,
        work := work, output := out } rfl
      (tape_move_cells _ _)
      rfl
      (fun i hi => hoth i hi)
      houtr
      (by show (work 6).cells = regCells 0
          rw [hclk]
          rfl)
      (by show (work 6).head = 0 + 1
          rw [hclk]
          rfl)
  have hoth₂ : ∀ i, i ≠ (6 : Fin 8) → (c₂.work i).read ≠ Γ.start := fun i hi => by
    rw [hw₂ i hi]
    exact hoth i hi
  have ho₂r : c₂.output.read ≠ Γ.start := by rw [ho₂]; exact houtr
  have hibl₂ : c₂.input.read = Γ.blank := by
    rw [Tape.read, hih₂, hic₂]
    exact inpCells_blank x le_rfl
  have hclk₂ : (c₂.work 6).read ≠ Γ.start := by
    rw [Tape.read, hhd₂, hcl₂, regCells_blank le_rfl]
    decide
  -- the final mark and the turn
  have hstep₃ := clockLen_step_scan_blank c₂ hst₂ hibl₂ hclk₂ hoth₂ ho₂r
  have hc₃cl : (Function.update c₂.work 6
      (((c₂.work 6).write Γw.one).move .left) 6).cells
      = regCells (x.length + 1) := by
    rw [Function.update_self, tape_move_cells, Tape.write,
      if_neg (by rw [hhd₂]; omega)]
    show Function.update (c₂.work 6).cells (c₂.work 6).head Γw.one.toΓ = _
    rw [hhd₂, hcl₂]
    exact regCells_update_succ x.length
  have hc₃hd : (Function.update c₂.work 6
      (((c₂.work 6).write Γw.one).move .left) 6).head = x.length := by
    rw [Function.update_self]
    show ((c₂.work 6).write Γw.one).head - 1 = x.length
    rw [tape_write_head, hhd₂]
    omega
  -- the lockstep rewind
  obtain ⟨c₄, hr₄, hst₄, hic₄, hih₄, hw₄, hcl₄, hhd₄, ho₄⟩ :=
    clockLen_back_run x x.length
      { state := .back, input := c₂.input.move .left,
        work := Function.update c₂.work 6 (((c₂.work 6).write Γw.one).move .left),
        output := c₂.output } rfl
      (by show (c₂.input.move .left).cells = _
          rw [tape_move_cells]
          exact hic₂)
      (by show c₂.input.head - 1 = x.length
          rw [hih₂]
          omega)
      (fun i hi => by
        show (Function.update c₂.work 6 _ i).read ≠ Γ.start
        rw [Function.update_of_ne hi]
        exact hoth₂ i hi)
      ho₂r
      (by rw [hc₃cl]; rfl)
      (fun j hj => by rw [hc₃cl]; exact regCells_ne_start' hj)
      hc₃hd
  refine ⟨c₄, _, ?_,
    .step hstep₁ (reachesIn_trans _ hr₂ (.step hstep₃ hr₄)), hst₄, ?_, ?_, ?_, ?_⟩
  · omega
  · exact Tape.ext' hih₄ hic₄
  · intro i hi
    rw [hw₄ i hi]
    show Function.update c₂.work 6 _ i = work i
    rw [Function.update_of_ne hi]
    exact hw₂ i hi
  · refine Tape.ext' hhd₄ ?_
    rw [hcl₄, hc₃cl]
    rfl
  · rw [ho₄, ho₂]
    exact hout

end ClockLen

/-- **The successor function is clock-constructible**: `clockLenTM` writes
    `|x| + 1` clock marks in a single input sweep, well within the
    `2 * (g n + n + 1)` budget. -/
theorem clockConstructible_succ : ClockConstructible (fun n => n + 1) := by
  refine ⟨clockLenTM, 2, ?_⟩
  intro x work₀ hpark _ h6
  have hspec := clockLenTM_hoareTime x work₀ (fun i _ => (hpark i).2)
    (by rw [h6, initTape_move_right_eq_regT_zero])
  refine hspec.consequence ?_ ?_ ?_
  · rintro inp work out ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro inp work out ⟨rfl, hw, h6', houtF⟩
    exact ⟨rfl, rfl, hw, h6', houtF.1, houtF.2.1, houtF.2.2⟩
  · show 2 * x.length + 4 ≤ 2 * ((x.length + 1) + x.length + 1)
    omega

-- ════════════════════════════════════════════════════════════════════════
-- moveClockTM: move the clock register to the scratch tape
-- ════════════════════════════════════════════════════════════════════════

/-- **Move the clock register to the scratch tape**: sweep right over tape
    6's marks, blanking each while writing a mark on tape 5 in lockstep,
    then rewind both heads to cell 1. From `(regT 0, regT v)` on tapes
    `(5, 6)` to `(regT v, regT 0)`; every other tape idles throughout. -/
def moveClockTM : TM 8 where
  Q := IncPhase
  qstart := .scan
  qhalt := .done
  δ := fun s iHead wHeads oHead =>
    match s with
    | .scan =>
      if wHeads 6 = Γ.one then
        (.scan,
         fun i => if i = 6 then Γw.blank else if i = 5 then Γw.one
                  else readBackWrite (wHeads i),
         readBackWrite oHead, idleDir iHead,
         fun i => if i = 6 then Dir3.right else if i = 5 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 6 then (if wHeads 6 = Γ.start then Dir3.right else Dir3.left)
                  else if i = 5 then (if wHeads 5 = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .back =>
      if wHeads 6 = Γ.start then
        (.park, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 6 then Dir3.right else if i = 5 then Dir3.right
                  else idleDir (wHeads i),
         idleDir oHead)
      else
        (.back, fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead,
         fun i => if i = 6 then Dir3.left
                  else if i = 5 then (if wHeads 5 = Γ.start then Dir3.right else Dir3.left)
                  else idleDir (wHeads i),
         idleDir oHead)
    | .park =>
      (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .done => allIdle s iHead wHeads oHead
  δ_right_of_start := by
    intro s iHead wHeads oHead
    match s with
    | .scan =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir6 : i = (6 : Fin 8)
        · rw [if_pos hir6]
        · rw [if_neg hir6]
          by_cases hir5 : i = (5 : Fin 8)
          · rw [if_pos hir5]
          · rw [if_neg hir5]; exact idleDir_right_of_start hi
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir6 : i = (6 : Fin 8)
        · subst hir6; rw [if_pos rfl, if_pos hi]
        · rw [if_neg hir6]
          by_cases hir5 : i = (5 : Fin 8)
          · subst hir5; rw [if_pos rfl, if_pos hi]
          · rw [if_neg hir5]; exact idleDir_right_of_start hi
    | .back =>
      dsimp only []
      split
      · refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir6 : i = (6 : Fin 8)
        · rw [if_pos hir6]
        · rw [if_neg hir6]
          by_cases hir5 : i = (5 : Fin 8)
          · rw [if_pos hir5]
          · rw [if_neg hir5]; exact idleDir_right_of_start hi
      · next hns =>
        refine ⟨idleDir_right_of_start, fun i hi => ?_, idleDir_right_of_start⟩
        dsimp only []
        by_cases hir6 : i = (6 : Fin 8)
        · subst hir6; exact absurd hi hns
        · rw [if_neg hir6]
          by_cases hir5 : i = (5 : Fin 8)
          · subst hir5; rw [if_pos rfl, if_pos hi]
          · rw [if_neg hir5]; exact idleDir_right_of_start hi
    | .park =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

section MoveClock

private theorem moveClock_ne_halt {s : IncPhase} (h : s ≠ .done)
    {c : Cfg 8 moveClockTM.Q} (hst : c.state = s) :
    ¬ c.state = moveClockTM.qhalt := by
  rw [hst]
  show ¬ s = IncPhase.done
  exact h

/-- `scan` over a clock mark: blank it, mark the scratch, both heads right. -/
private theorem moveClock_step_scan_one (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .scan) (hone : (c.work 6).read = Γ.one)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .scan, input := c.input,
        work := Function.update
          (Function.update c.work 6 (((c.work 6).write Γw.blank).move .right))
          5 (((c.work 5).write Γw.one).move .right),
        output := c.output } := by
  rw [TM.step, if_neg (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst, hone, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_id hinp
  · funext i
    by_cases hir6 : i = (6 : Fin 8)
    · subst hir6
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      simp only [Fin.isValue, ↓reduceIte]
    · by_cases hir5 : i = (5 : Fin 8)
      · subst hir5
        rw [Function.update_self]
        simp only [Fin.isValue, show ¬ ((5 : Fin 8) = 6) from by decide,
          ↓reduceIte]
      · rw [if_neg hir6, if_neg hir5, if_neg hir6, if_neg hir5,
          Function.update_of_ne hir5, Function.update_of_ne hir6]
        exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir5 hir6)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `scan` at the clock's first blank: turn both heads around. -/
private theorem moveClock_step_scan_turn (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .scan) (hbl : (c.work 6).read = Γ.blank)
    (h5ns : (c.work 5).read ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .back, input := c.input,
        work := Function.update
          (Function.update c.work 6 ((c.work 6).move .left))
          5 ((c.work 5).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst, hbl, h5ns, reduceCtorEq, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_id hinp
  · funext i
    by_cases hir6 : i = (6 : Fin 8)
    · subst hir6
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      simp only [Fin.isValue, ↓reduceIte]
      rw [writeAndMove_readBack _ (by rw [hbl]; decide)]
    · by_cases hir5 : i = (5 : Fin 8)
      · subst hir5
        rw [Function.update_self]
        simp only [Fin.isValue, show ¬ ((5 : Fin 8) = 6) from by decide,
          ↓reduceIte]
        rw [writeAndMove_readBack _ h5ns]
      · rw [if_neg hir6, if_neg hir5, Function.update_of_ne hir5,
          Function.update_of_ne hir6]
        exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir5 hir6)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` off the sentinel: both heads keep rewinding. -/
private theorem moveClock_step_back_left (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .back) (h6ns : (c.work 6).read ≠ Γ.start)
    (h5ns : (c.work 5).read ≠ Γ.start)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .back, input := c.input,
        work := Function.update
          (Function.update c.work 6 ((c.work 6).move .left))
          5 ((c.work 5).move .left),
        output := c.output } := by
  rw [TM.step, if_neg (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst, h6ns, h5ns, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_id hinp
  · funext i
    by_cases hir6 : i = (6 : Fin 8)
    · subst hir6
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      simp only [Fin.isValue, ↓reduceIte]
      rw [writeAndMove_readBack _ h6ns]
    · by_cases hir5 : i = (5 : Fin 8)
      · subst hir5
        rw [Function.update_self]
        simp only [Fin.isValue, show ¬ ((5 : Fin 8) = 6) from by decide,
          ↓reduceIte]
        rw [writeAndMove_readBack _ h5ns]
      · rw [if_neg hir6, if_neg hir5, Function.update_of_ne hir5,
          Function.update_of_ne hir6]
        exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir5 hir6)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `back` on the sentinel: both heads step right to cell 1 and park. -/
private theorem moveClock_step_back_start (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .back) (hs : (c.work 6).read = Γ.start)
    (h60 : (c.work 6).head = 0) (h50 : (c.work 5).head = 0)
    (hinp : c.input.read ≠ Γ.start)
    (hoth : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .park, input := c.input,
        work := Function.update
          (Function.update c.work 6 ((c.work 6).move .right))
          5 ((c.work 5).move .right),
        output := c.output } := by
  rw [TM.step, if_neg (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst, hs, ↓reduceIte]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_id hinp
  · funext i
    by_cases hir6 : i = (6 : Fin 8)
    · subst hir6
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      simp only [Fin.isValue, ↓reduceIte]
      show ((c.work 6).write _).move Dir3.right = (c.work 6).move .right
      congr 1
      rw [Tape.write, if_pos h60]
    · by_cases hir5 : i = (5 : Fin 8)
      · subst hir5
        rw [Function.update_self]
        simp only [Fin.isValue, show ¬ ((5 : Fin 8) = 6) from by decide,
          ↓reduceIte]
        show ((c.work 5).write _).move Dir3.right = (c.work 5).move .right
        congr 1
        rw [Tape.write, if_pos h50]
      · rw [if_neg hir6, if_neg hir5, Function.update_of_ne hir5,
          Function.update_of_ne hir6]
        exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hoth i hir5 hir6)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- `park`: one idle step into `done`. -/
private theorem moveClock_step_park (c : Cfg 8 moveClockTM.Q)
    (hst : c.state = .park) (hinp : c.input.read ≠ Γ.start)
    (hall : ∀ i, (c.work i).read ≠ Γ.start)
    (hout : c.output.read ≠ Γ.start) :
    moveClockTM.step c = some
      { state := .done, input := c.input, work := c.work, output := c.output } := by
  rw [TM.step, if_neg (moveClock_ne_halt (by decide) hst)]
  simp only [moveClockTM, hst]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl, ?_, ?_, ?_⟩)
  · exact transitionInput_id hinp
  · funext i
    exact Tape.writeAndMove_readBack_idle_of_ne_start _ (hall i)
  · exact Tape.writeAndMove_readBack_idle_of_ne_start _ hout

/-- The lockstep sweep: blank the clock marks, mark the scratch. -/
private theorem moveClock_scan_run (v m : ℕ) :
    ∀ (k : ℕ), v = k + m →
      ∀ (c : Cfg 8 moveClockTM.Q),
      c.state = .scan →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 5).cells = regCells k → (c.work 5).head = k + 1 →
      (c.work 6).cells = clearCells v k → (c.work 6).head = k + 1 →
      ∃ c', moveClockTM.reachesIn m c c' ∧
        c'.state = .scan ∧ c'.input = c.input ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 5).cells = regCells v ∧ (c'.work 5).head = v + 1 ∧
        (c'.work 6).cells = clearCells v v ∧ (c'.work 6).head = v + 1 ∧
        c'.output = c.output := by
  induction m with
  | zero =>
    intro k hk c hst hinp hoth hout hcl5 hhd5 hcl6 hhd6
    obtain rfl : v = k := by omega
    exact ⟨c, .zero, hst, rfl, fun _ _ _ => rfl, hcl5, hhd5, hcl6, hhd6, rfl⟩
  | succ m ih =>
    intro k hk c hst hinp hoth hout hcl5 hhd5 hcl6 hhd6
    have hone : (c.work 6).read = Γ.one := by
      rw [Tape.read, hhd6, hcl6, clearCells, if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]
    have hstep := moveClock_step_scan_one c hst hone hinp hoth hout
    have h6cl : (((c.work 6).write Γw.blank).move .right).cells
        = clearCells v (k + 1) := by
      rw [tape_move_cells, Tape.write, if_neg (by rw [hhd6]; omega)]
      show Function.update (c.work 6).cells (c.work 6).head Γw.blank.toΓ = _
      rw [hhd6, hcl6]
      exact clearCells_update_succ v k
    have h6hd : (((c.work 6).write Γw.blank).move .right).head = (k + 1) + 1 := by
      show ((c.work 6).write Γw.blank).head + 1 = _
      rw [tape_write_head, hhd6]
    have h5cl : (((c.work 5).write Γw.one).move .right).cells
        = regCells (k + 1) := by
      rw [tape_move_cells, Tape.write, if_neg (by rw [hhd5]; omega)]
      show Function.update (c.work 5).cells (c.work 5).head Γw.one.toΓ = _
      rw [hhd5, hcl5]
      exact regCells_update_succ k
    have h5hd : (((c.work 5).write Γw.one).move .right).head = (k + 1) + 1 := by
      show ((c.work 5).write Γw.one).head + 1 = _
      rw [tape_write_head, hhd5]
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      ih (k + 1) (by omega)
        { state := .scan, input := c.input,
          work := Function.update
            (Function.update c.work 6 (((c.work 6).write Γw.blank).move .right))
            5 (((c.work 5).write Γw.one).move .right),
          output := c.output } rfl hinp
        (fun i hi5 hi6 => by
          dsimp only
          rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
          exact hoth i hi5 hi6)
        hout
        (by dsimp only
            rw [Function.update_self]
            exact h5cl)
        (by dsimp only
            rw [Function.update_self]
            exact h5hd)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            exact h6cl)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            exact h6hd)
    refine ⟨c', .step hstep hreach, h1, h2, ?_, h4, h5, h6, h7, h8⟩
    intro i hi5 hi6
    rw [h3 i hi5 hi6]
    dsimp only
    rw [Function.update_of_ne hi5, Function.update_of_ne hi6]

/-- The lockstep rewind: both heads return to cell 1 and the machine parks. -/
private theorem moveClock_back_run (h : ℕ) :
    ∀ (c : Cfg 8 moveClockTM.Q),
      c.state = .back →
      c.input.read ≠ Γ.start →
      (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c.work i).read ≠ Γ.start) →
      c.output.read ≠ Γ.start →
      (c.work 5).cells 0 = Γ.start → (∀ j, 1 ≤ j → (c.work 5).cells j ≠ Γ.start) →
      (c.work 5).head = h →
      (c.work 6).cells 0 = Γ.start → (∀ j, 1 ≤ j → (c.work 6).cells j ≠ Γ.start) →
      (c.work 6).head = h →
      ∃ c', moveClockTM.reachesIn (h + 2) c c' ∧
        c'.state = .done ∧ c'.input = c.input ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → c'.work i = c.work i) ∧
        (c'.work 5).cells = (c.work 5).cells ∧ (c'.work 5).head = 1 ∧
        (c'.work 6).cells = (c.work 6).cells ∧ (c'.work 6).head = 1 ∧
        c'.output = c.output := by
  induction h with
  | zero =>
    intro c hst hinp hoth hout hc05 hcr5 hhd5 hc06 hcr6 hhd6
    have hs : (c.work 6).read = Γ.start := by rw [Tape.read, hhd6]; exact hc06
    have hstep₁ := moveClock_step_back_start c hst hs hhd6 hhd5 hinp hoth hout
    have hstep₂ := moveClock_step_park
      { state := .park, input := c.input,
        work := Function.update
          (Function.update c.work 6 ((c.work 6).move .right))
          5 ((c.work 5).move .right),
        output := c.output } rfl hinp
      (fun i => by
        by_cases hir5 : i = (5 : Fin 8)
        · subst hir5
          dsimp only
          rw [Function.update_self]
          show (c.work 5).cells ((c.work 5).head + 1) ≠ Γ.start
          exact hcr5 _ (by omega)
        · by_cases hir6 : i = (6 : Fin 8)
          · subst hir6
            dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            show (c.work 6).cells ((c.work 6).head + 1) ≠ Γ.start
            exact hcr6 _ (by omega)
          · dsimp only
            rw [Function.update_of_ne hir5, Function.update_of_ne hir6]
            exact hoth i hir5 hir6)
      hout
    refine ⟨_, .step hstep₁ (.step hstep₂ .zero), rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · intro i hi5 hi6
      dsimp only
      rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
    · dsimp only
      rw [Function.update_self]
      rfl
    · dsimp only
      rw [Function.update_self]
      show (c.work 5).head + 1 = 1
      rw [hhd5]
    · dsimp only
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      rfl
    · dsimp only
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      show (c.work 6).head + 1 = 1
      rw [hhd6]
  | succ h ih =>
    intro c hst hinp hoth hout hc05 hcr5 hhd5 hc06 hcr6 hhd6
    have h6ns : (c.work 6).read ≠ Γ.start := by
      rw [Tape.read, hhd6]; exact hcr6 (h + 1) (by omega)
    have h5ns : (c.work 5).read ≠ Γ.start := by
      rw [Tape.read, hhd5]; exact hcr5 (h + 1) (by omega)
    have hstep₁ := moveClock_step_back_left c hst h6ns h5ns hinp hoth hout
    obtain ⟨c', hreach, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      ih { state := .back, input := c.input,
           work := Function.update
             (Function.update c.work 6 ((c.work 6).move .left))
             5 ((c.work 5).move .left),
           output := c.output } rfl hinp
        (fun i hi5 hi6 => by
          dsimp only
          rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
          exact hoth i hi5 hi6)
        hout
        (by dsimp only
            rw [Function.update_self]
            exact hc05)
        (fun j hj => by
          dsimp only
          rw [Function.update_self]
          exact hcr5 j hj)
        (by dsimp only
            rw [Function.update_self]
            show (c.work 5).head - 1 = h
            rw [hhd5]
            omega)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            exact hc06)
        (fun j hj => by
          dsimp only
          rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
            Function.update_self]
          exact hcr6 j hj)
        (by dsimp only
            rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
              Function.update_self]
            show (c.work 6).head - 1 = h
            rw [hhd6]
            omega)
    refine ⟨c', .step hstep₁ hreach, h1, h2, ?_, ?_, h5, ?_, h7, h8⟩
    · intro i hi5 hi6
      rw [h3 i hi5 hi6]
      dsimp only
      rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
    · rw [h4]
      dsimp only
      rw [Function.update_self]
      rfl
    · rw [h6]
      dsimp only
      rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self]
      rfl

/-- **`moveClockTM` Hoare specification.** From `(regT 0, regT v)` on tapes
    `(5, 6)`, reach `(regT v, regT 0)` in `2v + 4` steps; the input, the
    output, and every other work tape are preserved exactly. -/
private theorem moveClockTM_hoareTime (v : ℕ) (inp₀ : Tape) (work₀ : Fin 8 → Tape)
    (hinp : inp₀.read ≠ Γ.start)
    (hoth : ∀ i : Fin 8, i ≠ 5 → i ≠ 6 → (work₀ i).read ≠ Γ.start)
    (h5 : work₀ 5 = regT 0) (h6 : work₀ 6 = regT v) :
    moveClockTM.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = work₀ ∧ outF out)
      (fun inp work out => inp = inp₀ ∧
        (∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → work i = work₀ i) ∧
        work 5 = regT v ∧ work 6 = regT 0 ∧ outF out)
      (2 * v + 4) := by
  rintro inp work out ⟨rfl, rfl, hout⟩
  have houtr : out.read ≠ Γ.start := outF_read_ne_start hout
  obtain ⟨c₂, hr₂, hst₂, hin₂, hw₂, hcl5₂, hhd5₂, hcl6₂, hhd6₂, ho₂⟩ :=
    moveClock_scan_run v v 0 (by omega)
      { state := moveClockTM.qstart, input := inp, work := work, output := out }
      rfl hinp hoth houtr
      (by show (work 5).cells = regCells 0
          rw [h5]
          rfl)
      (by show (work 5).head = 0 + 1
          rw [h5]
          rfl)
      (by show (work 6).cells = clearCells v 0
          rw [h6, regT_cells, clearCells_zero])
      (by show (work 6).head = 0 + 1
          rw [h6]
          rfl)
  have hoth₂ : ∀ i, i ≠ (5 : Fin 8) → i ≠ (6 : Fin 8) → (c₂.work i).read ≠ Γ.start :=
    fun i hi5 hi6 => by
      rw [hw₂ i hi5 hi6]
      exact hoth i hi5 hi6
  have hin₂r : c₂.input.read ≠ Γ.start := by rw [hin₂]; exact hinp
  have ho₂r : c₂.output.read ≠ Γ.start := by rw [ho₂]; exact houtr
  have h6bl₂ : (c₂.work 6).read = Γ.blank := by
    rw [Tape.read, hhd6₂, hcl6₂, clearCells_last]
    exact regCells_blank (by omega)
  have h5ns₂ : (c₂.work 5).read ≠ Γ.start := by
    rw [Tape.read, hhd5₂, hcl5₂]
    exact regCells_ne_start' (by omega)
  have hstep₃ := moveClock_step_scan_turn c₂ hst₂ h6bl₂ h5ns₂ hin₂r hoth₂ ho₂r
  obtain ⟨c₄, hr₄, hst₄, hin₄, hw₄, hcl5₄, hhd5₄, hcl6₄, hhd6₄, ho₄⟩ :=
    moveClock_back_run v
      { state := .back, input := c₂.input,
        work := Function.update
          (Function.update c₂.work 6 ((c₂.work 6).move .left))
          5 ((c₂.work 5).move .left),
        output := c₂.output } rfl hin₂r
      (fun i hi5 hi6 => by
        dsimp only
        rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
        exact hoth₂ i hi5 hi6)
      ho₂r
      (by dsimp only
          rw [Function.update_self]
          show (c₂.work 5).cells 0 = _
          rw [hcl5₂]
          rfl)
      (fun j hj => by
        dsimp only
        rw [Function.update_self]
        show (c₂.work 5).cells j ≠ _
        rw [hcl5₂]
        exact regCells_ne_start' hj)
      (by dsimp only
          rw [Function.update_self]
          show (c₂.work 5).head - 1 = v
          rw [hhd5₂]
          omega)
      (by dsimp only
          rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
            Function.update_self]
          show (c₂.work 6).cells 0 = _
          rw [hcl6₂]
          rfl)
      (fun j hj => by
        dsimp only
        rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
          Function.update_self]
        show (c₂.work 6).cells j ≠ _
        rw [hcl6₂]
        exact clearCells_ne_start hj)
      (by dsimp only
          rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5),
            Function.update_self]
          show (c₂.work 6).head - 1 = v
          rw [hhd6₂]
          omega)
  refine ⟨c₄, _, ?_, reachesIn_trans _ hr₂ (.step hstep₃ hr₄), hst₄, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [hin₄]
    exact hin₂
  · intro i hi5 hi6
    rw [hw₄ i hi5 hi6]
    dsimp only
    rw [Function.update_of_ne hi5, Function.update_of_ne hi6]
    exact hw₂ i hi5 hi6
  · refine Tape.ext' hhd5₄ ?_
    rw [hcl5₄]
    dsimp only
    rw [Function.update_self, tape_move_cells, hcl5₂, regT_cells]
  · refine Tape.ext' hhd6₄ ?_
    rw [hcl6₄]
    dsimp only
    rw [Function.update_of_ne (by decide : (6 : Fin 8) ≠ 5), Function.update_self,
      tape_move_cells, hcl6₂, clearCells_last, regT_cells]
  · rw [ho₄, ho₂]
    exact hout
end MoveClock

end TM
