/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.Cobham.Defs
public import Complexitylib.Classes.P.Cobham.Internal.MulLen
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.NormalForm
public import Complexitylib.Classes.P.Composition
public import Complexitylib.Classes.P.FinsetDomain
public import Complexitylib.Classes.P.PairWithInput
public import Complexitylib.Models.TuringMachine.Subroutines
public import Complexitylib.Models.TuringMachine.Tape.Encoding

/-!
# Cobham's characterization of FP — proof internals

This module reduces the equivalence `CobhamFP = FP`
(`Complexitylib.Classes.P.Cobham`) to a small set of named lemmas and proves the
parts that are already reachable from the existing `FP` and machine
infrastructure. It is **not** meant for human review of the mathematics — the
surface file `Complexitylib.Classes.P.Cobham` carries the auditable statements;
here we assemble the proof.

## Multi-arity bridge

`FP` is defined only for unary functions `List Bool → List Bool`, but Cobham's
algebra is inherently multi-arity (`(Fin n → List Bool) → List Bool`). We bridge
the two with a nested-pairing tuple encoding `encodeVec` and the derived
predicate `FPn`, which says a multi-arity function is polynomial-time *on encoded
argument vectors*. The soundness direction `CobhamFP ⊆ FP` is then an induction
`Cobham f → FPn f` (`cobham_imp_FPn`) specialized to arity one.

## Status of the reduction

Fully proved here:
- the framework (`encodeVec`, `FPn`) and its basic lemmas;
- the arity-one specialization glue `CobhamFP_subset_FP_of_FPn`, on top of the
  framing map `pairLeftNil_mem_FP`;
- the atomic machine lemmas `cons_mem_FP`, `sndBlock_mem_FP`,
  `fstBlock_mem_FP`, `reorder_mem_FP` (bespoke transducers) and the derived
  `pairFn_mem_FP`, `assembleVec_mem_FP`, `mulLenFn_mem_FP`;
- all six constructor cases of the soundness induction: `fpn_empty`, `fpn_proj`,
  `fpn_bit`, `fpn_smash`, `fpn_comp`, and `fpn_boundedRec` — the last modulo the
  single loop lemma below, with all of its algebra (`recFold`, `recFoldClamp`,
  `recFold_eq_recNotation`, `recFoldClamp_eq_recFold`) and the discharge of
  Cobham's limited-recursion side condition proved here.

Reduced to precisely-stated lemmas (still `sorry`, each documented with the
intended construction):
- `recFoldClamp_mem_FP` — the loop of the `boundedRec` case: iterating a
  width-clamped `FP` step function once per bit of `sndBlock z`;
- `FP_subset_CobhamFP_internal` — the completeness direction (Turing-machine
  interpreter inside the algebra).

See each lemma's docstring for the construction it stands for. This decomposition
is the contribution of the draft: it turns the two opaque `sorry`s of the surface
file into an auditable work-list.
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-! ## Tuple encoding and the multi-arity FP predicate -/

/-- Encode an argument vector as a single bitstring by nested pairing, with the
head component placed in the verbatim suffix:
`encodeVec ![] = []` and `encodeVec (x ::ᵥ v) = pair (encodeVec v) x`.

Putting the head last (as the `pair` suffix) is what makes the arity-one encoding
`pair [] x`, so the soundness glue only needs `pairLeftNil_mem_FP`, which follows
from the existing `mem_FP_pairWithInput`. Because `pair` is injective with a
verbatim suffix, `encodeVec` is injective and its length is linear in the total
length of the components — exactly what the polynomial-time bookkeeping of `FPn`
needs. -/
def encodeVec : {n : ℕ} → (Fin n → List Bool) → List Bool
  | 0, _ => []
  | _ + 1, v => pair (encodeVec (Fin.tail v)) (v 0)

@[simp] theorem encodeVec_zero (v : Fin 0 → List Bool) : encodeVec v = [] := rfl

@[simp] theorem encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    encodeVec v = pair (encodeVec (Fin.tail v)) (v 0) := rfl

/-- The arity-one encoding is the single component placed in the (verbatim)
suffix of an empty block: `encodeVec ![x] = pair [] x`. -/
theorem encodeVec_one (v : Fin 1 → List Bool) : encodeVec v = pair [] (v 0) := by
  simp [encodeVec]

/-- **Multi-arity polynomial time.** A function of an argument vector is `FPn`
when some genuine (unary) `FP` function computes it on encoded vectors. This is
the induction motive for `cobham_imp_FPn`; specialized to arity one it collapses
to `FP` (see `CobhamFP_subset_FP_of_FPn`). -/
def FPn {n : ℕ} (f : (Fin n → List Bool) → List Bool) : Prop :=
  ∃ g, g ∈ FP ∧ ∀ v, g (encodeVec v) = f v

/-! ## Foundational FP building blocks -/

/-- The constant empty-output function is in `FP` (the empty-support case of
`ite_mem_finset_mem_FP`). -/
theorem const_nil_mem_FP : (fun _ : List Bool => ([] : List Bool)) ∈ FP := by
  have h := ite_mem_finset_mem_FP (fun _ => []) (∅ : Finset (List Bool))
  simpa using h

/-- The framing map `x ↦ pair [] x` (i.e. `false :: true :: x`) is
polynomial-time. This is the foundational map behind the arity-one encoding
`encodeVec ![x] = pair [] x`, and it is exactly `mem_FP_pairWithInput` applied to
the constant empty function. -/
theorem pairLeftNil_mem_FP : (fun x : List Bool => pair [] x) ∈ FP := by
  have h := mem_FP_pairWithInput const_nil_mem_FP
  simpa using h

/-! ## Soundness: `Cobham f → FPn f`, constructor by constructor -/

/-- `empty` case: the constant empty function is `FPn` at every arity, witnessed
by `const_nil_mem_FP`. -/
theorem fpn_empty {n : ℕ} : FPn (fun _ : Fin n → List Bool => ([] : List Bool)) :=
  ⟨fun _ => [], const_nil_mem_FP, fun _ => rfl⟩

/-- Decode the payload of the leading self-delimiting block: read doubled bits
until the `[false, true]` separator. On a valid block `delimit x ++ y` this
returns `x` (see `fstBlock_pair`); on malformed input it returns the bits decoded
so far. This total, incremental form is what the `fstBlockTM` scanner computes. -/
def fstBlock : List Bool → List Bool
  | false :: false :: z => false :: fstBlock z
  | true :: true :: z => true :: fstBlock z
  | _ => []

/-- Take the suffix after the leading self-delimiting block (the second `unpair?`
component), or `[]` if the input is not a valid block. On `encodeVec` of a
nonempty vector this returns the head component `v 0`. -/
def sndBlock (z : List Bool) : List Bool :=
  match unpair? z with
  | some (_, s) => s
  | none => []

@[simp] theorem fstBlock_pair (x y : List Bool) : fstBlock (pair x y) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> (rw [pair_cons_eq]; simp [fstBlock, ih])

@[simp] theorem sndBlock_pair (x y : List Bool) : sndBlock (pair x y) = y := by
  simp [sndBlock]

/-- Stripping the head component of an encoded vector yields the encoded tail.
(Not a `simp` lemma: `simp` already reaches this via `encodeVec_succ` and
`fstBlock_pair`.) -/
theorem fstBlock_encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    fstBlock (encodeVec v) = encodeVec (Fin.tail v) := by
  simp

/-- The suffix of an encoded vector is its head component.
(Not a `simp` lemma: `simp` already reaches this via `encodeVec_succ` and
`sndBlock_pair`.) -/
theorem sndBlock_encodeVec_succ {n : ℕ} (v : Fin (n + 1) → List Bool) :
    sndBlock (encodeVec v) = v 0 := by
  simp

/-! ### Block-decoding scanners

Machines that parse the leading self-delimiting block of the input. The scanner
reads the doubled payload two bits at a time until the `[false, true]` separator.
`sndBlockTM` then copies the suffix to the output (`sndBlock`); `fstBlockTM` emits
the decoded payload bits during the scan (`fstBlock`). Both are total: malformed
input halts with empty output, matching the `unpair?`-based definitions. -/

section BlockDecoders
open Complexity.TM

/-- Control states of the block-decoding scanners. -/
inductive ScanPhase where
  | skip | scanA | scanBfalse | scanBtrue | emit | done
  deriving DecidableEq

instance : Fintype ScanPhase where
  elems := {.skip, .scanA, .scanBfalse, .scanBtrue, .emit, .done}
  complete := fun x => by cases x <;> simp

/-- The suffix decoder: scan doubled payload bits until the `[false, true]`
separator, then copy the remaining input (the suffix `y` of `pair x y`) to the
output. On malformed input it halts with empty output. Computes `sndBlock`. -/
def sndBlockTM : TM 0 where
  Q := ScanPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.scanA, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .scanA =>
        match iHead with
        | Γ.zero =>
            (.scanBfalse, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | Γ.one =>
            (.scanBtrue, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanBfalse =>
        match iHead with
        | Γ.one =>
            (.emit, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | Γ.zero =>
            (.scanA, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanBtrue =>
        match iHead with
        | Γ.one =>
            (.scanA, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .emit =>
        if iHead = Γ.blank then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.emit, fun i => readBackWrite (wHeads i), readBackWrite iHead,
            Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .scanA =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .scanBfalse =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .scanBtrue =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .emit =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- A content-preserving idle step on a tape whose head is off the left marker:
writing back the read symbol and taking the idle direction is a no-op. -/
private theorem output_idle_eq {t : Tape} (h : t.read ≠ Γ.start) :
    t.writeAndMove (readBackWrite t.read) (idleDir t.read) = t := by
  rw [writeAndMove_readBack t h, idleDir, if_neg h, Tape.move]

/-- The copy phase of `sndBlockTM`: from `emit` with input cursor on suffix `y`
and output holding `acc`, the machine copies `y` after `acc` and halts. -/
private theorem sndBlockTM_emit_loop :
    ∀ (y acc : List Bool) (c : Cfg 0 sndBlockTM.Q),
      c.state = ScanPhase.emit →
      c.input.HasBinarySuffix y →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ y.length + 1 ∧ sndBlockTM.reachesIn t c c' ∧ sndBlockTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ y) := by
  intro y
  induction y with
  | nil =>
      intro acc c hstate hsuf hpre
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have hout : c.output.read = Γ.blank := hpre.read_blank
      have houtne : c.output.read ≠ Γ.start := by rw [hout]; decide
      refine ⟨{ state := ScanPhase.done
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, sndBlockTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from by
            rw [writeAndMove_readBack c.output houtne, idleDir, if_neg houtne, Tape.move]]
      simpa using hpre
  | cons bit y ih =>
      intro acc c hstate hsuf hpre
      have hread : c.input.read = Γ.ofBool bit := hsuf.read_cons
      have hne : c.input.read ≠ Γ.blank := by rw [hread]; cases bit <;> decide
      let c1 : Cfg 0 sndBlockTM.Q :=
        { state := ScanPhase.emit
          input := c.input.move Dir3.right
          work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
            (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
      have hstep : sndBlockTM.step c = some c1 := by
        simp [TM.step, hstate, sndBlockTM, hne, c1]
      have hpre1 : c1.output.HasBinaryPrefix (acc ++ [bit]) := by
        have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool bit := by
          rw [hread]; cases bit <;> rfl
        show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ) Dir3.right).HasBinaryPrefix
          (acc ++ [bit])
        rw [hco]; exact Tape.hasBinaryPrefix_write_bit bit hpre
      obtain ⟨c', t, ht, hreach, hhalt, hout⟩ :=
        ih (acc ++ [bit]) c1 rfl hsuf.move_right_cons hpre1
      refine ⟨c', t + 1, by simp; omega, .step hstep hreach, hhalt, ?_⟩
      rwa [List.append_assoc, List.cons_append, List.nil_append] at hout

/-- The scan phase of `sndBlockTM`: from `scanA` with input cursor on `w`, the
machine parses doubled pairs to the separator and copies the suffix, halting with
output `sndBlock w`. `fuel` bounds the recursion by the input length. -/
private theorem sndBlockTM_scan_loop :
    ∀ (fuel : ℕ) (w : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 sndBlockTM.Q),
      c.state = ScanPhase.scanA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix [] →
      ∃ c' t, t ≤ 2 * w.length + 2 ∧ sndBlockTM.reachesIn t c c' ∧ sndBlockTM.halted c' ∧
        c'.output.HasOutput (sndBlock w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have hout : c.output.read = Γ.blank := hpre.read_blank
      have houtne : c.output.read ≠ Γ.start := by rw [hout]; decide
      refine ⟨{ state := ScanPhase.done
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, sndBlockTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from by
            rw [writeAndMove_readBack c.output houtne, idleDir, if_neg houtne, Tape.move]]
      simpa [sndBlock] using hpre.hasOutput
  | succ fuel ih =>
      intro w hw c hstate hsuf hpre
      -- Halting helper for the malformed / end-of-input branches.
      have hout : c.output.read = Γ.blank := hpre.read_blank
      have houtne : c.output.read ≠ Γ.start := by rw [hout]; decide
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := ScanPhase.done
                    input := c.input.move (idleDir c.input.read)
                    work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                      (idleDir (c.work i).read)
                    output := c.output.writeAndMove (readBackWrite c.output.read)
                      (idleDir c.output.read) }, 1, by simp,
            .step (by simp [TM.step, hstate, sndBlockTM, hread]) .zero, rfl, ?_⟩
          rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
              = c.output from by
                rw [writeAndMove_readBack c.output houtne, idleDir, if_neg houtne, Tape.move]]
          simpa [sndBlock] using hpre.hasOutput
      | [false] =>
          -- scanA reads false → scanBfalse; next reads blank → done.
          have hread : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have hout1 : c1.output.read = Γ.blank := hpre1.read_blank
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hout1]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, sndBlockTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from by
                rw [writeAndMove_readBack c1.output houtne1, idleDir, if_neg houtne1, Tape.move]]
          simpa [sndBlock] using hpre1.hasOutput
      | [true] =>
          have hread : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have hout1 : c1.output.read = Γ.blank := hpre1.read_blank
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hout1]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, sndBlockTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from by
                rw [writeAndMove_readBack c1.output houtne1, idleDir, if_neg houtne1, Tape.move]]
          simpa [sndBlock] using hpre1.hasOutput
      | false :: true :: y =>
          -- separator: scanA false → scanBfalse → (reads true) → emit; copy y.
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.emit
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.output.read)
                (idleDir c1.output.read) }
          have hstepB : sndBlockTM.step c1 = some c2 := by
            simp [TM.step, sndBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix y := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix [] := by
            have hout1 : c1.output.read ≠ Γ.start := by
              rw [hpre1.read_blank]; decide
            rw [show c2.output = c1.output from output_idle_eq hout1]; exact hpre1
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            sndBlockTM_emit_loop y [] c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have : sndBlock (false :: true :: y) = y := by simp [sndBlock, unpair?]
          rw [this]
          simpa using hcout.hasOutput
      | false :: false :: z =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.output.read)
                (idleDir c1.output.read) }
          have hstepB : sndBlockTM.step c1 = some c2 := by
            simp [TM.step, sndBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix [] := by
            have hout1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
            rw [show c2.output = c1.output from output_idle_eq hout1]; exact hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have : sndBlock (false :: false :: z) = sndBlock z := by
            cases h : unpair? z <;> simp [sndBlock, unpair?, h]
          rw [this]; exact hcout
      | true :: true :: z =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.output.read)
                (idleDir c1.output.read) }
          have hstepB : sndBlockTM.step c1 = some c2 := by
            simp [TM.step, sndBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix [] := by
            have hout1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
            rw [show c2.output = c1.output from output_idle_eq hout1]; exact hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have : sndBlock (true :: true :: z) = sndBlock z := by
            cases h : unpair? z <;> simp [sndBlock, unpair?, h]
          rw [this]; exact hcout
      | true :: false :: rest =>
          -- malformed: scanA true → scanBtrue → reads false → done, empty output.
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 sndBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : sndBlockTM.step c = some c1 := by
            simp [TM.step, hstate, sndBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix [] := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          have hout1 : c1.output.read = Γ.blank := hpre1.read_blank
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hout1]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, sndBlockTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from by
                rw [writeAndMove_readBack c1.output houtne1, idleDir, if_neg houtne1, Tape.move]]
          have : sndBlock (true :: false :: rest) = [] := by simp [sndBlock, unpair?]
          rw [this]; simpa using hpre1.hasOutput

/-- `sndBlock` is polynomial-time, via the `sndBlockTM` scanner. -/
theorem sndBlock_mem_FP : sndBlock ∈ FP := by
  refine ⟨1, 0, sndBlockTM, (fun m => 2 * m + 3), ?_, ?_⟩
  · intro z
    -- Step 1: skip past ▷, positioning both cursors.
    let c1 : Cfg 0 sndBlockTM.Q :=
      { state := ScanPhase.scanA
        input := (Tape.init (z.map Γ.ofBool)).move Dir3.right
        work := fun _ => (Tape.init []).move Dir3.right
        output := (Tape.init []).move Dir3.right }
    have hstep1 : sndBlockTM.step (sndBlockTM.initCfg z) = some c1 := by
      simp [TM.step, sndBlockTM, c1, Tape.read, Tape.init, readBackWrite, idleDir,
        Tape.writeAndMove, Tape.write, Tape.move]
    have hsuf : c1.input.HasBinarySuffix z := Tape.init_move_right_hasBinarySuffix z
    have hpre : c1.output.HasBinaryPrefix [] := Tape.init_nil_move_right_hasBinaryPrefix_nil
    obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
      sndBlockTM_scan_loop z.length z le_rfl c1 rfl hsuf hpre
    exact ⟨c', t + 1, by show t + 1 ≤ 2 * z.length + 3; omega,
      .step hstep1 hreach, hhalt, hcout⟩
  · have hn : (fun m : ℕ => 2 * m) =O ((· ^ 1) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.refl (fun m : ℕ => m)).const_mul_left 2
    exact BigO.add hn (BigO.const_le_pow 3 1)

/-- The payload decoder: scan doubled payload bits, emitting each decoded bit to
the output, until the `[false, true]` separator or end of input. Computes
`fstBlock`. -/
def fstBlockTM : TM 0 where
  Q := ScanPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.scanA, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .scanA =>
        match iHead with
        | Γ.zero =>
            (.scanBfalse, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | Γ.one =>
            (.scanBtrue, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanBfalse =>
        match iHead with
        | Γ.zero =>
            (.scanA, fun i => readBackWrite (wHeads i), Γw.ofBool false,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .scanBtrue =>
        match iHead with
        | Γ.one =>
            (.scanA, fun i => readBackWrite (wHeads i), Γw.ofBool true,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .emit => allIdle .done iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .scanA =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .scanBfalse =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .scanBtrue =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .emit => exact rightOfStart_allIdle iHead wHeads oHead
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- The scan of `fstBlockTM`: from `scanA` on input `w` with output holding `acc`,
the machine emits the decoded payload of `w`, halting with `acc ++ fstBlock w`. -/
private theorem fstBlockTM_scan_loop :
    ∀ (fuel : ℕ) (w acc : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 fstBlockTM.Q),
      c.state = ScanPhase.scanA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ 2 * w.length + 2 ∧ fstBlockTM.reachesIn t c c' ∧ fstBlockTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ fstBlock w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w acc hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      refine ⟨{ state := ScanPhase.done
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, fstBlockTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from output_idle_eq houtne]
      simpa [fstBlock] using hpre
  | succ fuel ih =>
      intro w acc hw c hstate hsuf hpre
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := ScanPhase.done
                    input := c.input.move (idleDir c.input.read)
                    work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                      (idleDir (c.work i).read)
                    output := c.output.writeAndMove (readBackWrite c.output.read)
                      (idleDir c.output.read) }, 1, by simp,
            .step (by simp [TM.step, hstate, fstBlockTM, hread]) .zero, rfl, ?_⟩
          rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
              = c.output from output_idle_eq houtne]
          simpa [fstBlock] using hpre
      | [false] =>
          have hread : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, fstBlockTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [fstBlock] using hpre1
      | [true] =>
          have hread : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, fstBlockTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [fstBlock] using hpre1
      | false :: true :: y =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, fstBlockTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [fstBlock] using hpre1
      | true :: false :: rest =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ScanPhase.done
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, fstBlockTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [fstBlock] using hpre1
      | false :: false :: z =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBfalse
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool false) Dir3.right }
          have hstepB : fstBlockTM.step c1 = some c2 := by
            simp [TM.step, fstBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [false]) := by
            show (c1.output.writeAndMove ((Γw.ofBool false).toΓ) Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [Γw.ofBool_toΓ]; exact Tape.hasBinaryPrefix_write_bit false hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [false]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hfb : fstBlock (false :: false :: z) = false :: fstBlock z := rfl
          rw [hfb, List.append_assoc, List.cons_append, List.nil_append] at *
          exact hcout
      | true :: true :: z =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanBtrue
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : fstBlockTM.step c = some c1 := by
            simp [TM.step, hstate, fstBlockTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 fstBlockTM.Q :=
            { state := ScanPhase.scanA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool true) Dir3.right }
          have hstepB : fstBlockTM.step c1 = some c2 := by
            simp [TM.step, fstBlockTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [true]) := by
            show (c1.output.writeAndMove ((Γw.ofBool true).toΓ) Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [Γw.ofBool_toΓ]; exact Tape.hasBinaryPrefix_write_bit true hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [true]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hfb : fstBlock (true :: true :: z) = true :: fstBlock z := rfl
          rw [hfb, List.append_assoc, List.cons_append, List.nil_append] at *
          exact hcout

/-- `fstBlock` is polynomial-time, via the `fstBlockTM` scanner. -/
theorem fstBlock_mem_FP : fstBlock ∈ FP := by
  refine ⟨1, 0, fstBlockTM, (fun m => 2 * m + 3), ?_, ?_⟩
  · intro z
    let c1 : Cfg 0 fstBlockTM.Q :=
      { state := ScanPhase.scanA
        input := (Tape.init (z.map Γ.ofBool)).move Dir3.right
        work := fun _ => (Tape.init []).move Dir3.right
        output := (Tape.init []).move Dir3.right }
    have hstep1 : fstBlockTM.step (fstBlockTM.initCfg z) = some c1 := by
      simp [TM.step, fstBlockTM, c1, Tape.read, Tape.init, readBackWrite, idleDir,
        Tape.writeAndMove, Tape.write, Tape.move]
    have hsuf : c1.input.HasBinarySuffix z := Tape.init_move_right_hasBinarySuffix z
    have hpre : c1.output.HasBinaryPrefix [] := Tape.init_nil_move_right_hasBinaryPrefix_nil
    obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
      fstBlockTM_scan_loop z.length z [] le_rfl c1 rfl hsuf hpre
    refine ⟨c', t + 1, by show t + 1 ≤ 2 * z.length + 3; omega,
      .step hstep1 hreach, hhalt, ?_⟩
    simpa using hcout.hasOutput
  · have hn : (fun m : ℕ => 2 * m) =O ((· ^ 1) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.refl (fun m : ℕ => m)).const_mul_left 2
    exact BigO.add hn (BigO.const_le_pow 3 1)

end BlockDecoders

/-! ### The bit-successor transducer

A small machine computing `x ↦ b :: x`: skip the left marker, emit `b`, then copy
the input verbatim after it. Modelled on `TM.copyInputToOutputTM`. -/

section BitSuccessor
open Complexity.TM

/-- Control states of `consBitTM`: skip the `▷` marker, emit the fixed bit, copy
the input, halt. -/
inductive ConsPhase where
  | skip | emit | copy | done
  deriving DecidableEq

instance : Fintype ConsPhase where
  elems := {.skip, .emit, .copy, .done}
  complete := fun x => by cases x <;> simp

/-- The bit-successor machine: on input `x` it writes `b :: x` to the output tape
in `|x| + 3` steps. First `skip` advances past the left markers, `emit` writes `b`
into output cell 1, and `copy` copies the input bits after it. -/
def consBitTM (b : Bool) : TM 0 where
  Q := ConsPhase
  qstart := .skip
  qhalt := .done
  δ := fun state iHead wHeads oHead =>
    match state with
    | .skip =>
        (.emit, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .emit =>
        (.copy, fun i => readBackWrite (wHeads i), Γw.ofBool b, idleDir iHead,
          fun i => idleDir (wHeads i), Dir3.right)
    | .copy =>
        if iHead = Γ.blank then
          (.done, fun i => readBackWrite (wHeads i), readBackWrite oHead,
            idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
        else
          (.copy, fun i => readBackWrite (wHeads i), readBackWrite iHead,
            Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
    | .done => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .skip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .emit =>
        exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .copy =>
        dsimp only []
        split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .done => exact rightOfStart_allIdle iHead wHeads oHead

/-- The copy phase of `consBitTM`: from a configuration whose output already holds
`b :: x.take k` and whose input head is at the first uncopied cell, the remaining
`rem = |x| - k` bits are copied and the machine halts with output `b :: x`. -/
private theorem consBitTM_copy_loop (b : Bool) (x : List Bool) :
    ∀ rem k (c : Cfg 0 (consBitTM b).Q),
      rem = x.length - k →
      c.state = ConsPhase.copy →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      c.output.HasBinaryPrefix (b :: x.take k) →
      k ≤ x.length →
      ∃ c',
        (consBitTM b).reachesIn (rem + 1) c c' ∧
        (consBitTM b).halted c' ∧
        c'.output.HasBinaryPrefix (b :: x) := by
  intro rem
  induction rem with
  | zero =>
      intro k c hrem hstate hcells hhead hprefix hk_le
      have hk_eq : k = x.length := by omega
      subst hk_eq
      have hread : c.input.read = Γ.blank := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge x x.length le_rfl]
      have hprefix_full : c.output.HasBinaryPrefix (b :: x) := by
        simpa using hprefix
      have houtput_blank : c.output.read = Γ.blank := hprefix_full.read_blank
      let c1 : Cfg 0 (consBitTM b).Q :=
        { state := ConsPhase.done
          input := c.input.move (idleDir c.input.read)
          work := fun i =>
            (c.work i).writeAndMove (readBackWrite (c.work i).read)
              (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.output.read)
            (idleDir c.output.read) }
      have hinput_keep : c.input.move (idleDir c.input.read) = c.input := by
        simp [idleDir, hread, Tape.move]
      have houtput_keep :
          c.output.writeAndMove (readBackWrite c.output.read)
              (idleDir c.output.read) = c.output := by
        rw [writeAndMove_readBack c.output (by simp [houtput_blank]),
          idleDir, if_neg (by simp [houtput_blank]), Tape.move]
      have hstep : (consBitTM b).step c = some c1 := by
        simp [TM.step, hstate, consBitTM, hread, c1]
      refine ⟨c1, .step hstep .zero, rfl, ?_⟩
      rw [show c1.output = c.output by simpa [c1] using houtput_keep]
      exact hprefix_full
  | succ rem ih =>
      intro k c hrem hstate hcells hhead hprefix hk_le
      have hk_lt : k < x.length := by omega
      have hread : c.input.read = Γ.ofBool (x[k]'hk_lt) := by
        simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt x k hk_lt]
      have hread_ne : c.input.read ≠ Γ.blank := by
        rw [hread]; cases x[k]'hk_lt <;> simp [Γ.ofBool]
      have hprefix_next :
          (c.output.writeAndMove (Γ.ofBool (x[k]'hk_lt)) Dir3.right).HasBinaryPrefix
            (b :: x.take (k + 1)) := by
        have hwrite := Tape.hasBinaryPrefix_write_bit (x[k]'hk_lt) hprefix
        have heq : (b :: x.take k) ++ [x[k]'hk_lt] = b :: x.take (k + 1) := by
          rw [List.cons_append, List.take_concat_get' x k hk_lt]
        rwa [heq] at hwrite
      let c1 : Cfg 0 (consBitTM b).Q :=
        { state := ConsPhase.copy
          input := c.input.move Dir3.right
          work := fun i =>
            (c.work i).writeAndMove (readBackWrite (c.work i).read)
              (idleDir (c.work i).read)
          output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
      have hstep : (consBitTM b).step c = some c1 := by
        simp [TM.step, hstate, consBitTM, hread_ne, c1]
      have hcells1 : c1.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
        simpa [c1, Tape.move_cells] using hcells
      have hhead1 : c1.input.head = (k + 1) + 1 := by simp [c1, Tape.move, hhead]
      have hprefix1 : c1.output.HasBinaryPrefix (b :: x.take (k + 1)) := by
        have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool (x[k]'hk_lt) := by
          rw [hread]; cases x[k]'hk_lt <;> rfl
        show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ) Dir3.right).HasBinaryPrefix
          (b :: x.take (k + 1))
        rw [hco]; exact hprefix_next
      obtain ⟨c', hreach, hhalt, hprefix'⟩ :=
        ih (k + 1) c1 (by omega) rfl hcells1 hhead1 hprefix1 (by omega)
      exact ⟨c', .step hstep hreach, hhalt, hprefix'⟩

/-- `consBitTM b` computes `x ↦ b :: x` within the linear bound `|x| + 3`. -/
theorem consBitTM_computesInTime (b : Bool) :
    (consBitTM b).ComputesInTime (fun x => b :: x) (fun m => m + 3) := by
  intro x
  -- Step 1: `skip` advances past the left markers.
  let c1 : Cfg 0 (consBitTM b).Q :=
    { state := ConsPhase.emit
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).writeAndMove (readBackWrite (Tape.init []).read)
        (idleDir (Tape.init []).read)
      output := (Tape.init []).move Dir3.right }
  have hstep1 : (consBitTM b).step ((consBitTM b).initCfg x) = some c1 := by
    simp [TM.step, consBitTM, c1, Tape.read, Tape.init, idleDir, Tape.writeAndMove,
      Tape.write, Tape.move]
  -- The input head after `skip` reads a data/blank cell, never the marker.
  have hne : c1.input.read ≠ Γ.start := by
    cases x with
    | nil => simp [c1, Tape.read, Tape.move, Tape.init]
    | cons a t => cases a <;> simp [c1, Tape.read, Tape.move, Tape.init, Γ.ofBool]
  -- Step 2: `emit` writes `b` into output cell 1.
  let c2 : Cfg 0 (consBitTM b).Q :=
    { state := ConsPhase.copy
      input := c1.input.move (idleDir c1.input.read)
      work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
        (idleDir (c1.work i).read)
      output := c1.output.writeAndMove (Γw.ofBool b) Dir3.right }
  have hstep2 : (consBitTM b).step c1 = some c2 := by
    simp [TM.step, consBitTM, c1, c2]
  have hc2_input_cells : c2.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
    simp [c2, c1, Tape.move_cells]
  have hc2_input_head : c2.input.head = 0 + 1 := by
    show (c1.input.move (idleDir c1.input.read)).head = 0 + 1
    rw [idleDir, if_neg hne]
    simp [Tape.move, c1, Tape.init]
  have hc2_output : c2.output.HasBinaryPrefix (b :: x.take 0) := by
    have hbase : ((Tape.init []).move Dir3.right).HasBinaryPrefix [] :=
      Tape.init_nil_move_right_hasBinaryPrefix_nil
    have hw := Tape.hasBinaryPrefix_write_bit (t := (Tape.init []).move Dir3.right) b hbase
    show (c1.output.writeAndMove ((Γw.ofBool b).toΓ) Dir3.right).HasBinaryPrefix (b :: x.take 0)
    rw [Γw.ofBool_toΓ, show c1.output = (Tape.init []).move Dir3.right from rfl]
    simpa using hw
  obtain ⟨c', hreach, hhalt, hprefix⟩ :=
    consBitTM_copy_loop b x x.length 0 c2 (by simp) rfl hc2_input_cells
      hc2_input_head hc2_output (Nat.zero_le _)
  refine ⟨c', x.length + 3, le_rfl, ?_, hhalt, (hprefix.hasOutput)⟩
  have : (consBitTM b).reachesIn (x.length + 1 + 1 + 1) ((consBitTM b).initCfg x) c' :=
    .step hstep1 (.step hstep2 hreach)
  simpa [Nat.add_assoc] using this

/-- Prepending a fixed bit is polynomial-time — the string-successor underlying
the `bit` constructor. Witnessed by `consBitTM`. -/
theorem cons_mem_FP (b : Bool) : (fun x : List Bool => b :: x) ∈ FP := by
  refine ⟨1, 0, consBitTM b, (fun m => m + 3), consBitTM_computesInTime b, ?_⟩
  have hn : (fun m : ℕ => m) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun m : ℕ => m)
  exact BigO.add hn (BigO.const_le_pow 3 1)

end BitSuccessor

/-- `proj` case: extracting the `i`-th component of an encoded vector is `FP`.

The extraction is `sndBlock` after `i`-fold `fstBlock`: peel `i` leading blocks to
reach the encoding of components `i, i+1, …`, then read its head with `sndBlock`.
Proved here by induction on the arity; each atomic step is `FP`
(`fstBlock_mem_FP`, `sndBlock_mem_FP`) and `FP` is closed under composition
(`mem_FP_comp`), so only those two machine lemmas remain open. -/
theorem fpn_proj {n : ℕ} (i : Fin n) : FPn (fun v : Fin n → List Bool => v i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      induction i using Fin.cases with
      | zero =>
          exact ⟨sndBlock, sndBlock_mem_FP, fun v => sndBlock_encodeVec_succ v⟩
      | succ j =>
          obtain ⟨g, hg, hgf⟩ := ih j
          refine ⟨g ∘ fstBlock, mem_FP_comp fstBlock_mem_FP hg, fun v => ?_⟩
          show g (fstBlock (encodeVec v)) = v j.succ
          rw [fstBlock_encodeVec_succ, hgf]
          rfl

/-- `bit` case: prepending a fixed bit is `FPn` at arity one. On the arity-one
encoding `encodeVec ![x] = pair [] x`, the head component `x` is `sndBlock`, so the
witness is `(b :: ·) ∘ sndBlock`; both factors are `FP`. -/
theorem fpn_bit (b : Bool) :
    FPn (fun v : Fin 1 → List Bool => b :: v 0) := by
  refine ⟨(fun x => b :: x) ∘ sndBlock,
    mem_FP_comp sndBlock_mem_FP (cons_mem_FP b), fun v => ?_⟩
  show b :: sndBlock (encodeVec v) = b :: v 0
  rw [sndBlock_encodeVec_succ]

/-- Drop the third component of a right-nested triple. Copy doubled payload bits
verbatim until the `[false, true]` separator, then decode the *next* block's
payload (`fstBlock`). On a valid triple this satisfies
`reorder (pair A (pair B C)) = pair A B` (`reorder_pair_pair`). The incremental
recursion (writing before knowing validity) is what the `reorderTM` scanner
computes; it is total and needs no sub-machines. -/
def reorder : List Bool → List Bool
  | false :: false :: z => false :: false :: reorder z
  | true :: true :: z => true :: true :: reorder z
  | false :: true :: z => false :: true :: fstBlock z
  | c :: _ => [c]
  | [] => []

theorem reorder_pair_pair (A B C : List Bool) :
    reorder (pair A (pair B C)) = pair A B := by
  induction A with
  | nil =>
      show false :: true :: fstBlock (pair B C) = false :: true :: B
      rw [fstBlock_pair]
  | cons a A ih =>
      rw [pair_cons_eq]
      cases a
      · show false :: false :: reorder (pair A (pair B C)) = pair (false :: A) B
        rw [ih, pair_cons_eq]
      · show true :: true :: reorder (pair A (pair B C)) = pair (true :: A) B
        rw [ih, pair_cons_eq]

section ReorderMachine
open Complexity.TM

/-- Control states of `reorderTM`: skip the marker; phase 1 (`rcopyA`/`rcopyBf`/
`rcopyBt`) copies doubled pairs verbatim until the separator; phase 2
(`rdecA`/`rdecBf`/`rdecBt`) decodes the next block's payload; then halt. -/
inductive ReorderPhase where
  | rskip | rcopyA | rcopyBf | rcopyBt | rdecA | rdecBf | rdecBt | rdone
  deriving DecidableEq

instance : Fintype ReorderPhase where
  elems := {.rskip, .rcopyA, .rcopyBf, .rcopyBt, .rdecA, .rdecBf, .rdecBt, .rdone}
  complete := fun x => by cases x <;> simp

/-- The reorder transducer computing `reorder`: copy the leading block verbatim
(phase 1) up to and including the `[false,true]` separator, then decode and emit
the payload of the following block (phase 2). -/
def reorderTM : TM 0 where
  Q := ReorderPhase
  qstart := .rskip
  qhalt := .rdone
  δ := fun state iHead wHeads oHead =>
    match state with
    | .rskip =>
        (.rcopyA, fun i => readBackWrite (wHeads i), readBackWrite oHead, Dir3.right,
          fun i => idleDir (wHeads i), Dir3.right)
    | .rcopyA =>
        match iHead with
        | Γ.zero =>
            (.rcopyBf, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | Γ.one =>
            (.rcopyBt, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rcopyBf =>
        match iHead with
        | Γ.zero =>
            (.rcopyA, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | Γ.one =>
            (.rdecA, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rcopyBt =>
        match iHead with
        | Γ.one =>
            (.rcopyA, fun i => readBackWrite (wHeads i), readBackWrite iHead,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rdecA =>
        match iHead with
        | Γ.zero =>
            (.rdecBf, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | Γ.one =>
            (.rdecBt, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rdecBf =>
        match iHead with
        | Γ.zero =>
            (.rdecA, fun i => readBackWrite (wHeads i), Γw.ofBool false,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rdecBt =>
        match iHead with
        | Γ.one =>
            (.rdecA, fun i => readBackWrite (wHeads i), Γw.ofBool true,
              Dir3.right, fun i => idleDir (wHeads i), Dir3.right)
        | _ =>
            (.rdone, fun i => readBackWrite (wHeads i), readBackWrite oHead,
              idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .rdone => allIdle .rdone iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .rskip => exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .rcopyA =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rcopyBf =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rcopyBt =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rdecA =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rdecBf =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rdecBt =>
        cases iHead <;>
          exact ⟨by first | exact fun _ => rfl | exact idleDir_right_of_start,
            fun _ => idleDir_right_of_start,
            by first | exact fun _ => rfl | exact idleDir_right_of_start⟩
    | .rdone => exact rightOfStart_allIdle iHead wHeads oHead

/-- Phase 2 of `reorderTM`: from `rdecA` on input `w` with output holding `acc`,
decode and emit `fstBlock w`, halting with `acc ++ fstBlock w`. Identical in shape
to `fstBlockTM_scan_loop`. -/
private theorem reorderTM_dec_loop :
    ∀ (fuel : ℕ) (w acc : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 reorderTM.Q),
      c.state = ReorderPhase.rdecA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ 2 * w.length + 2 ∧ reorderTM.reachesIn t c c' ∧ reorderTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ fstBlock w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w acc hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      refine ⟨{ state := ReorderPhase.rdone
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, reorderTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from output_idle_eq houtne]
      simpa [fstBlock] using hpre
  | succ fuel ih =>
      intro w acc hw c hstate hsuf hpre
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := ReorderPhase.rdone
                    input := c.input.move (idleDir c.input.read)
                    work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                      (idleDir (c.work i).read)
                    output := c.output.writeAndMove (readBackWrite c.output.read)
                      (idleDir c.output.read) }, 1, by simp,
            .step (by simp [TM.step, hstate, reorderTM, hread]) .zero, rfl, ?_⟩
          rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
              = c.output from output_idle_eq houtne]
          simpa [fstBlock] using hpre
      | [false] =>
          have hread : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, reorderTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [fstBlock] using hpre1
      | [true] =>
          have hread : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstep : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, reorderTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [fstBlock] using hpre1
      | false :: true :: y =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [fstBlock] using hpre1
      | true :: false :: rest =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [fstBlock] using hpre1
      | false :: false :: z =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool false) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [false]) := by
            show (c1.output.writeAndMove ((Γw.ofBool false).toΓ) Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [Γw.ofBool_toΓ]; exact Tape.hasBinaryPrefix_write_bit false hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [false]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hfb : fstBlock (false :: false :: z) = false :: fstBlock z := rfl
          rw [hfb, List.append_assoc, List.cons_append, List.nil_append] at *
          exact hcout
      | true :: true :: z =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.output.read)
                (idleDir c.output.read) }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix acc := by
            rw [show c1.output = c.output from output_idle_eq houtne]; exact hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (Γw.ofBool true) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [true]) := by
            show (c1.output.writeAndMove ((Γw.ofBool true).toΓ) Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [Γw.ofBool_toΓ]; exact Tape.hasBinaryPrefix_write_bit true hpre1
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [true]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hfb : fstBlock (true :: true :: z) = true :: fstBlock z := rfl
          rw [hfb, List.append_assoc, List.cons_append, List.nil_append] at *
          exact hcout

/-- Phase 1 of `reorderTM`: from `rcopyA` on input `w` with output holding `acc`,
copy `w`'s leading block verbatim and decode the following block, halting with
`acc ++ reorder w`. The separator case hands off to `reorderTM_dec_loop`. -/
private theorem reorderTM_copy_loop :
    ∀ (fuel : ℕ) (w acc : List Bool), w.length ≤ fuel → ∀ (c : Cfg 0 reorderTM.Q),
      c.state = ReorderPhase.rcopyA →
      c.input.HasBinarySuffix w →
      c.output.HasBinaryPrefix acc →
      ∃ c' t, t ≤ 3 * w.length + 3 ∧ reorderTM.reachesIn t c c' ∧ reorderTM.halted c' ∧
        c'.output.HasBinaryPrefix (acc ++ reorder w) := by
  intro fuel
  induction fuel with
  | zero =>
      intro w acc hw c hstate hsuf hpre
      have hwnil : w = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)
      subst hwnil
      have hread : c.input.read = Γ.blank := hsuf.read_nil
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      refine ⟨{ state := ReorderPhase.rdone
                input := c.input.move (idleDir c.input.read)
                work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                  (idleDir (c.work i).read)
                output := c.output.writeAndMove (readBackWrite c.output.read)
                  (idleDir c.output.read) }, 1, by simp,
        .step (by simp [TM.step, hstate, reorderTM, hread]) .zero, rfl, ?_⟩
      rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
          = c.output from output_idle_eq houtne]
      simpa [reorder] using hpre
  | succ fuel ih =>
      intro w acc hw c hstate hsuf hpre
      have houtne : c.output.read ≠ Γ.start := by rw [hpre.read_blank]; decide
      -- The `rcopyA` step emits the first bit `c1` verbatim.
      match w with
      | [] =>
          have hread : c.input.read = Γ.blank := hsuf.read_nil
          refine ⟨{ state := ReorderPhase.rdone
                    input := c.input.move (idleDir c.input.read)
                    work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                      (idleDir (c.work i).read)
                    output := c.output.writeAndMove (readBackWrite c.output.read)
                      (idleDir c.output.read) }, 1, by simp,
            .step (by simp [TM.step, hstate, reorderTM, hread]) .zero, rfl, ?_⟩
          rw [show c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)
              = c.output from output_idle_eq houtne]
          simpa [reorder] using hpre
      | [false] =>
          have hread : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstep : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [false]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool false := by rw [hread]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit false hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, reorderTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [reorder] using hpre1
      | [true] =>
          have hread : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstep : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hread, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix [] := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [true]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool true := by rw [hread]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit true hpre
          have hread1 : c1.input.read = Γ.blank := hsuf1.read_nil
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstep (.step (by simp [TM.step, reorderTM, hread1, c1]) .zero), rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          simpa [reorder] using hpre1
      | false :: true :: y =>
          -- separator: copy `false` then `true`, then decode `y`.
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: y) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [false]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool false := by rw [hreadA]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit false hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rdecA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.input.read) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix y := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [false, true]) := by
            have hco : (readBackWrite c1.input.read).toΓ = Γ.ofBool true := by rw [hreadB]; rfl
            show (c1.output.writeAndMove ((readBackWrite c1.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false, true])
            rw [hco]
            have := Tape.hasBinaryPrefix_write_bit true hpre1
            rwa [List.append_assoc] at this
          have hyfuel : y.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            reorderTM_dec_loop fuel y (acc ++ [false, true]) hyfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hr : reorder (false :: true :: y) = false :: true :: fstBlock y := rfl
          rw [hr]
          rwa [List.append_assoc] at hcout
      | false :: false :: z =>
          have hreadA : c.input.read = Γ.ofBool false := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBf
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [false]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool false := by rw [hreadA]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit false hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.input.read) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [false, false]) := by
            have hco : (readBackWrite c1.input.read).toΓ = Γ.ofBool false := by rw [hreadB]; rfl
            show (c1.output.writeAndMove ((readBackWrite c1.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [false, false])
            rw [hco]
            have := Tape.hasBinaryPrefix_write_bit false hpre1
            rwa [List.append_assoc] at this
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [false, false]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hr : reorder (false :: false :: z) = false :: false :: reorder z := rfl
          rw [hr]
          rwa [List.append_assoc] at hcout
      | true :: true :: z =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (true :: z) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [true]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool true := by rw [hreadA]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit true hpre
          have hreadB : c1.input.read = Γ.ofBool true := hsuf1.read_cons
          let c2 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyA
              input := c1.input.move Dir3.right
              work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                (idleDir (c1.work i).read)
              output := c1.output.writeAndMove (readBackWrite c1.input.read) Dir3.right }
          have hstepB : reorderTM.step c1 = some c2 := by
            simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1, c2]
          have hsuf2 : c2.input.HasBinarySuffix z := hsuf1.move_right_cons
          have hpre2 : c2.output.HasBinaryPrefix (acc ++ [true, true]) := by
            have hco : (readBackWrite c1.input.read).toΓ = Γ.ofBool true := by rw [hreadB]; rfl
            show (c1.output.writeAndMove ((readBackWrite c1.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [true, true])
            rw [hco]
            have := Tape.hasBinaryPrefix_write_bit true hpre1
            rwa [List.append_assoc] at this
          have hzfuel : z.length ≤ fuel := by
            simp only [List.length_cons] at hw; omega
          obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
            ih z (acc ++ [true, true]) hzfuel c2 rfl hsuf2 hpre2
          refine ⟨c', t + 1 + 1, by simp only [List.length_cons]; omega,
            .step hstepA (.step hstepB hreach), hhalt, ?_⟩
          have hr : reorder (true :: true :: z) = true :: true :: reorder z := rfl
          rw [hr]
          rwa [List.append_assoc] at hcout
      | true :: false :: rest =>
          have hreadA : c.input.read = Γ.ofBool true := hsuf.read_cons
          let c1 : Cfg 0 reorderTM.Q :=
            { state := ReorderPhase.rcopyBt
              input := c.input.move Dir3.right
              work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
                (idleDir (c.work i).read)
              output := c.output.writeAndMove (readBackWrite c.input.read) Dir3.right }
          have hstepA : reorderTM.step c = some c1 := by
            simp [TM.step, hstate, reorderTM, hreadA, Γ.ofBool, c1]
          have hsuf1 : c1.input.HasBinarySuffix (false :: rest) := hsuf.move_right_cons
          have hpre1 : c1.output.HasBinaryPrefix (acc ++ [true]) := by
            have hco : (readBackWrite c.input.read).toΓ = Γ.ofBool true := by rw [hreadA]; rfl
            show (c.output.writeAndMove ((readBackWrite c.input.read).toΓ)
                Dir3.right).HasBinaryPrefix
              (acc ++ [true])
            rw [hco]; exact Tape.hasBinaryPrefix_write_bit true hpre
          have hreadB : c1.input.read = Γ.ofBool false := hsuf1.read_cons
          have houtne1 : c1.output.read ≠ Γ.start := by rw [hpre1.read_blank]; decide
          refine ⟨{ state := ReorderPhase.rdone
                    input := c1.input.move (idleDir c1.input.read)
                    work := fun i => (c1.work i).writeAndMove (readBackWrite (c1.work i).read)
                      (idleDir (c1.work i).read)
                    output := c1.output.writeAndMove (readBackWrite c1.output.read)
                      (idleDir c1.output.read) }, 2, by simp,
            .step hstepA (.step (by simp [TM.step, reorderTM, hreadB, Γ.ofBool, c1]) .zero),
            rfl, ?_⟩
          rw [show c1.output.writeAndMove (readBackWrite c1.output.read) (idleDir c1.output.read)
              = c1.output from output_idle_eq houtne1]
          have hr : reorder (true :: false :: rest) = [true] := rfl
          rw [hr]
          exact hpre1

/-- `reorder` is polynomial-time, via the `reorderTM` scanner. -/
theorem reorder_mem_FP : reorder ∈ FP := by
  refine ⟨1, 0, reorderTM, (fun m => 3 * m + 4), ?_, ?_⟩
  · intro z
    let c1 : Cfg 0 reorderTM.Q :=
      { state := ReorderPhase.rcopyA
        input := (Tape.init (z.map Γ.ofBool)).move Dir3.right
        work := fun _ => (Tape.init []).move Dir3.right
        output := (Tape.init []).move Dir3.right }
    have hstep1 : reorderTM.step (reorderTM.initCfg z) = some c1 := by
      simp [TM.step, reorderTM, c1, Tape.read, Tape.init, readBackWrite, idleDir,
        Tape.writeAndMove, Tape.write, Tape.move]
    have hsuf : c1.input.HasBinarySuffix z := Tape.init_move_right_hasBinarySuffix z
    have hpre : c1.output.HasBinaryPrefix [] := Tape.init_nil_move_right_hasBinaryPrefix_nil
    obtain ⟨c', t, ht, hreach, hhalt, hcout⟩ :=
      reorderTM_copy_loop z.length z [] le_rfl c1 rfl hsuf hpre
    refine ⟨c', t + 1, by show t + 1 ≤ 3 * z.length + 4; omega,
      .step hstep1 hreach, hhalt, ?_⟩
    simpa using hcout.hasOutput
  · have hn : (fun m : ℕ => 3 * m) =O ((· ^ 1) : ℕ → ℕ) := by
      simpa [pow_one] using (BigO.refl (fun m : ℕ => m)).const_mul_left 3
    exact BigO.add hn (BigO.const_le_pow 4 1)

end ReorderMachine

/-- Pairing two `FP` functions of the same input is `FP`.

Built without a two-output machine: `mem_FP_pairWithInput` gives the nested triple
`z ↦ pair (a z) (pair (b z) z)` (pairing each computed value against the raw
input, then again), and the self-contained `reorder` drops the trailing input
copy to leave `pair (a z) (b z)`. This is what lets `fpn_comp` avoid a bespoke
tuple-assembly machine. -/
theorem pairFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => pair (a z) (b z)) ∈ FP := by
  have h1 : (fun z => pair (b z) z) ∈ FP := mem_FP_pairWithInput hb
  have h2 : (fun w => pair (a (sndBlock w)) w) ∈ FP :=
    mem_FP_pairWithInput (mem_FP_comp sndBlock_mem_FP ha)
  have h12 := mem_FP_comp h1 h2
  have heq : ((fun w => pair (a (sndBlock w)) w) ∘ fun z => pair (b z) z)
      = fun z => pair (a z) (pair (b z) z) := by
    funext z; simp [Function.comp, sndBlock_pair]
  rw [heq] at h12
  have hr := mem_FP_comp h12 reorder_mem_FP
  have heq2 : (reorder ∘ fun z => pair (a z) (pair (b z) z))
      = fun z => pair (a z) (b z) := by
    funext z; simp [Function.comp, reorder_pair_pair]
  rwa [heq2] at hr

/-- Emitting `|a z| · |b z|` copies of `false` is `FP` when `a, b` are. Built as
the self-contained `mulUnpair` (see `Complexitylib.Classes.P.Cobham.Internal.MulLen`)
after `pairFn a b`, avoiding a bespoke length-arithmetic machine over two
sub-machines. -/
theorem mulLenFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => List.replicate ((a z).length * (b z).length) false) ∈ FP := by
  have hc := mem_FP_comp (pairFn_mem_FP ha hb) mulUnpair_mem_FP
  have heq : (mulUnpair ∘ fun z => pair (a z) (b z))
      = fun z => List.replicate ((a z).length * (b z).length) false := by
    funext z; simp [Function.comp, mulUnpair_pair]
  rwa [heq] at hc

/-- `smash` case: the smash function is `FPn`. On `encodeVec ![x, y]` the two
components are `sndBlock` and `sndBlock ∘ fstBlock`; `smash x y` is
`|x| · |y|` copies of `false`, so the witness is `mulLenFn_mem_FP` of the two
decoders. Rests only on `mulLenFn_mem_FP` and the block decoders. -/
theorem fpn_smash :
    FPn (fun v : Fin 2 → List Bool => Complexity.smash (v 0) (v 1)) := by
  refine ⟨fun z =>
      List.replicate ((sndBlock z).length * (sndBlock (fstBlock z)).length) false,
    mulLenFn_mem_FP sndBlock_mem_FP (mem_FP_comp fstBlock_mem_FP sndBlock_mem_FP),
    fun v => ?_⟩
  show List.replicate
      ((sndBlock (encodeVec v)).length *
        (sndBlock (fstBlock (encodeVec v))).length) false
    = Complexity.smash (v 0) (v 1)
  rw [sndBlock_encodeVec_succ, fstBlock_encodeVec_succ, sndBlock_encodeVec_succ,
    Complexity.smash]
  rfl

/-- Assembling an encoded vector out of `FP` component functions of a common input
is `FP`. Proved by induction on the arity: the empty vector is the constant `[]`,
and the successor step is one `pairFn_mem_FP`. -/
theorem assembleVec_mem_FP {m : ℕ} (w : Fin m → (List Bool → List Bool))
    (hw : ∀ i, w i ∈ FP) :
    (fun z => encodeVec fun i => w i z) ∈ FP := by
  induction m with
  | zero =>
      have : (fun z : List Bool => encodeVec fun i : Fin 0 => w i z)
          = fun _ => [] := by funext z; rfl
      rw [this]; exact const_nil_mem_FP
  | succ m ih =>
      have htail : (fun z => encodeVec fun i : Fin m => Fin.tail w i z) ∈ FP :=
        ih (Fin.tail w) fun i => hw i.succ
      have h0 : w 0 ∈ FP := hw 0
      have hpair := pairFn_mem_FP htail h0
      have heq : (fun z => encodeVec fun i : Fin (m + 1) => w i z)
          = fun z => pair (encodeVec fun i : Fin m => Fin.tail w i z) (w 0 z) := by
        funext z; rw [encodeVec_succ]; rfl
      rw [heq]; exact hpair

/-- `comp` case: `FPn` is closed under Cobham composition. On `encodeVec v`, each
inner `gs i` is computed by its `FP` witness `G i`, the results are assembled into
`encodeVec (fun i => gs i v)` (`assembleVec_mem_FP`), and the outer `f`'s witness
is applied; `FP` is closed under composition. Rests only on `pairFn_mem_FP`. -/
theorem fpn_comp {m n : ℕ} {f : (Fin m → List Bool) → List Bool}
    {gs : Fin m → (Fin n → List Bool) → List Bool}
    (ihf : FPn f) (ihgs : ∀ i, FPn (gs i)) :
    FPn (fun v => f fun i => gs i v) := by
  obtain ⟨F, hF, hFf⟩ := ihf
  choose G hG hGf using ihgs
  refine ⟨F ∘ fun z => encodeVec fun i => G i z,
    mem_FP_comp (assembleVec_mem_FP G hG) hF, fun v => ?_⟩
  show F (encodeVec fun i => G i (encodeVec v)) = f fun i => gs i v
  have hinner : (fun i => G i (encodeVec v)) = fun i => gs i v := by
    funext i; exact hGf i v
  rw [hinner, hFf]

/-- One step of recursion on notation viewed as a fold operation: extend the
running suffix `p.1` by the bit `b` and update the running recursive value `p.2` by
the bit-selected step function. Folding this over a string with `List.foldr`
reproduces `recNotation` (see `recNotation_eq_foldr`); it is the per-iteration
body a loop machine runs. -/
def recNotationStep {n : ℕ} (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool)
    (w : Fin n → List Bool) (b : Bool) (p : List Bool × List Bool) :
    List Bool × List Bool :=
  (b :: p.1, (bif b then h₁ else h₀) (Fin.cons p.1 (Fin.cons p.2 w)))

/-- The first component of the recursion-on-notation fold accumulates exactly the
bits processed so far — i.e. it rebuilds the input string. -/
theorem recNotationStep_foldr_fst {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool} (s : List Bool)
    (w : Fin n → List Bool) :
    (s.foldr (recNotationStep h₀ h₁ w) ([], g w)).1 = s := by
  induction s with
  | nil => rfl
  | cons b x ih => simp [List.foldr_cons, recNotationStep, ih]

/-- **Recursion on notation is a fold.** `recNotation g h₀ h₁ s w` is the second
component of folding `recNotationStep` over `s` from the empty suffix and base
value `g w`. This reduces the `boundedRec` case to iterating a single step
function over the bits of `s` — exactly what a loop machine computes — and is the
target identity for `fpn_boundedRec`. -/
theorem recNotation_eq_foldr {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool) (s : List Bool)
    (w : Fin n → List Bool) :
    recNotation g h₀ h₁ s w =
      (s.foldr (recNotationStep h₀ h₁ w) ([], g w)).2 := by
  induction s with
  | nil => rfl
  | cons b x ih =>
      rw [recNotation_cons, List.foldr_cons]
      simp only [recNotationStep]
      rw [recNotationStep_foldr_fst g x w, ih]

/-! ### The `boundedRec` loop

The `boundedRec` case runs the recursion as a loop on *encoded* arguments:
`recFold A B e W s` threads a running suffix `t` of `s` and the running
accumulator `a` through the argument encoding `pair (pair W a) t`, which is
exactly `encodeVec (Fin.cons t (Fin.cons a w))` when `W = encodeVec w`.

A machine cannot run `recFold` as written: nothing stops the accumulator from
doubling in length at every iteration, so intermediate values would need
exponential space. `recFoldClamp` truncates every intermediate value to a
prescribed width, which makes the loop unconditionally polynomial-time
(`recFoldClamp_mem_FP`); Cobham's limited-recursion side condition is then
exactly what shows the truncation never fires (`recFoldClamp_eq_recFold`). -/

/-- The recursion-on-notation loop on encoded arguments: fold the bit-selected
step functions `A` (bit `false`) and `B` (bit `true`) over `s`, threading the
running suffix and accumulator through the argument encoding. -/
def recFold (A B : List Bool → List Bool) (e W : List Bool) :
    List Bool → List Bool
  | [] => e
  | b :: t => (bif b then B else A) (pair (pair W (recFold A B e W t)) t)

/-- `recFold` with every intermediate value truncated to `bound` bits. This is
the loop a machine can actually run: each iteration's state is length-bounded,
so the whole loop takes polynomial time. -/
def recFoldClamp (A B : List Bool → List Bool) (bound : ℕ) (e W : List Bool) :
    List Bool → List Bool
  | [] => e.take bound
  | b :: t =>
      ((bif b then B else A)
        (pair (pair W (recFoldClamp A B bound e W t)) t)).take bound

/-- **The loop of the `boundedRec` case** — the one machine-level fact the
soundness direction still needs.

*Construction (TODO):* run `forBinaryWorkTM` over a work tape holding `sndBlock z`
reversed. The loop state is a work tape holding the current pair
`pair (pair (fstBlock z) a) t`; one iteration appends the driver bit to `t`,
runs the `FP` machine for `A` or `B` on the state tape (via `retargetInput` and
`retargetOutput`, with the sub-machine's tapes cleared between iterations), and
truncates the result to `bound` bits. Because `bound` is a polynomial in `|z|`
and there are at most `|z|` iterations, the total time is polynomial. -/
theorem recFoldClamp_mem_FP {A B E : List Bool → List Bool}
    (hA : A ∈ FP) (hB : B ∈ FP) (hE : E ∈ FP) (p : Polynomial ℕ) :
    (fun z => recFoldClamp A B (p.eval z.length) (E z) (fstBlock z) (sndBlock z))
      ∈ FP := by
  sorry

/-- Truncation is a no-op as soon as every intermediate value already fits. -/
theorem recFoldClamp_eq_recFold {A B : List Bool → List Bool} {bound : ℕ}
    {e W : List Bool} (s : List Bool)
    (hle : ∀ t : List Bool, t.length ≤ s.length →
      (recFold A B e W t).length ≤ bound) :
    recFoldClamp A B bound e W s = recFold A B e W s := by
  induction s with
  | nil =>
      show e.take bound = e
      exact List.take_of_length_le (hle [] (by simp))
  | cons b t ih =>
      have htail : recFoldClamp A B bound e W t = recFold A B e W t :=
        ih fun u hu => hle u (by simp only [List.length_cons]; omega)
      show ((bif b then B else A)
        (pair (pair W (recFoldClamp A B bound e W t)) t)).take bound = _
      rw [htail]
      exact List.take_of_length_le (hle (b :: t) le_rfl)

/-- On encoded arguments the loop computes recursion on notation: `recFold` over
the `FP` witnesses of `g`, `h₀`, `h₁` reproduces `recNotation`. -/
theorem recFold_eq_recNotation {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool}
    {G H₀ H₁ : List Bool → List Bool}
    (hG : ∀ u : Fin n → List Bool, G (encodeVec u) = g u)
    (hH₀ : ∀ u : Fin (n + 2) → List Bool, H₀ (encodeVec u) = h₀ u)
    (hH₁ : ∀ u : Fin (n + 2) → List Bool, H₁ (encodeVec u) = h₁ u)
    (w : Fin n → List Bool) (s : List Bool) :
    recFold H₀ H₁ (G (encodeVec w)) (encodeVec w) s = recNotation g h₀ h₁ s w := by
  -- The encoded step argument is exactly the vector `Fin.cons t (Fin.cons a w)`.
  have henc : ∀ (t a : List Bool),
      pair (pair (encodeVec w) a) t = encodeVec (Fin.cons t (Fin.cons a w)) := by
    intro t a
    rw [encodeVec_succ, encodeVec_succ]
    simp [Fin.tail_cons]
  induction s with
  | nil => exact hG w
  | cons b t ih =>
      show (bif b then H₁ else H₀)
        (pair (pair (encodeVec w) (recFold H₀ H₁ (G (encodeVec w)) (encodeVec w) t)) t)
        = _
      rw [ih, henc, recNotation_cons]
      cases b
      · simp only [cond_false]; exact hH₀ _
      · simp only [cond_true]; exact hH₁ _

/-- Every `FP` function has polynomially bounded output length: a time bound is
also an output-length bound (`TM.ComputesInTime.output_length_le`). -/
theorem output_length_poly_of_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    ∃ p : Polynomial ℕ, ∀ x, (f x).length ≤ p.eval x.length := by
  obtain ⟨k, tm, p, hcomp⟩ := mem_FP_iff_computesInTime_polynomial.mp hf
  exact ⟨p, fun x => hcomp.output_length_le x⟩

/-- `boundedRec` case: `FPn` is closed under limited recursion on notation.

By `recFold_eq_recNotation` the value is the encoded-argument loop `recFold` run
over the bits of `v 0`. Cobham's limited-recursion side condition `hbound` caps
every intermediate accumulator by `|j (…)|`, which is polynomial in `|encodeVec v|`
(`output_length_poly_of_mem_FP`), so the clamped loop `recFoldClamp` — which a
machine can run in polynomial time (`recFoldClamp_mem_FP`) — never truncates and
therefore agrees with `recFold`. -/
theorem fpn_boundedRec {n : ℕ} {g : (Fin n → List Bool) → List Bool}
    {h₀ h₁ : (Fin (n + 2) → List Bool) → List Bool}
    {j : (Fin (n + 1) → List Bool) → List Bool}
    (ihg : FPn g) (ih0 : FPn h₀) (ih1 : FPn h₁) (ihj : FPn j)
    (hbound : ∀ x v, (recNotation g h₀ h₁ x v).length ≤ (j (Fin.cons x v)).length) :
    FPn (fun v : Fin (n + 1) → List Bool =>
      recNotation g h₀ h₁ (v 0) (Fin.tail v)) := by
  obtain ⟨G, hGFP, hG⟩ := ihg
  obtain ⟨H₀, hH0FP, hH0⟩ := ih0
  obtain ⟨H₁, hH1FP, hH1⟩ := ih1
  obtain ⟨J, hJFP, hJ⟩ := ihj
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hJFP
  have hE : (fun z => G (fstBlock z)) ∈ FP := mem_FP_comp fstBlock_mem_FP hGFP
  refine ⟨fun z => recFoldClamp H₀ H₁ (p.eval z.length) (G (fstBlock z)) (fstBlock z)
      (sndBlock z), recFoldClamp_mem_FP hH0FP hH1FP hE p, fun v => ?_⟩
  show recFoldClamp H₀ H₁ (p.eval (encodeVec v).length) (G (fstBlock (encodeVec v)))
      (fstBlock (encodeVec v)) (sndBlock (encodeVec v))
    = recNotation g h₀ h₁ (v 0) (Fin.tail v)
  rw [fstBlock_encodeVec_succ, sndBlock_encodeVec_succ]
  rw [recFoldClamp_eq_recFold (v 0) ?_]
  · exact recFold_eq_recNotation hG hH0 hH1 (Fin.tail v) (v 0)
  · -- Cobham's limited-recursion bound caps every intermediate accumulator.
    intro t ht
    rw [recFold_eq_recNotation hG hH0 hH1 (Fin.tail v) t]
    refine le_trans (hbound t (Fin.tail v)) ?_
    have hJt : (j (Fin.cons t (Fin.tail v))).length
        ≤ p.eval (encodeVec (Fin.cons t (Fin.tail v))).length := by
      rw [← hJ (Fin.cons t (Fin.tail v))]
      exact hp _
    refine le_trans hJt (polynomial_eval_mono_nat p ?_)
    have e1 : (encodeVec (Fin.cons t (Fin.tail v))).length
        = 2 * (encodeVec (Fin.tail v)).length + 2 + t.length := by
      simp [encodeVec_succ, Fin.tail_cons]
    have e2 : (encodeVec v).length
        = 2 * (encodeVec (Fin.tail v)).length + 2 + (v 0).length := by
      simp [encodeVec_succ]
    omega

/-- **Soundness induction.** Every function of Cobham's algebra is polynomial
time on encoded argument vectors. -/
theorem cobham_imp_FPn : ∀ {n : ℕ} {f : (Fin n → List Bool) → List Bool},
    Cobham f → FPn f := by
  intro n f h
  induction h with
  | proj i => exact fpn_proj i
  | empty => exact fpn_empty
  | bit b => exact fpn_bit b
  | smash => exact fpn_smash
  | comp _ _ ihf ihgs => exact fpn_comp ihf ihgs
  | boundedRec _ _ _ _ hbound ihg ih0 ih1 ihj =>
      exact fpn_boundedRec ihg ih0 ih1 ihj hbound

/-- Arity-one specialization: from the multi-arity soundness induction, the
unary fragment `CobhamFP` lands in `FP`. -/
theorem CobhamFP_subset_FP_of_FPn : CobhamFP ⊆ FP := by
  intro f hf
  obtain ⟨g, hg, hgf⟩ := cobham_imp_FPn hf
  -- `hgf` specialized to `![x]`: `g (pair [] x) = f x`.
  have hval : ∀ x : List Bool, g (pair [] x) = f x := by
    intro x
    have := hgf ![x]
    rwa [encodeVec_one] at this
  -- Hence `f = g ∘ (x ↦ pair [] x)`, a composition of `FP` functions.
  have hfeq : f = g ∘ fun x : List Bool => pair [] x := by
    funext x; simp [Function.comp, hval x]
  rw [hfeq]
  exact mem_FP_comp pairLeftNil_mem_FP hg

/-! ## Completeness: `FP ⊆ CobhamFP` -/

/-- **Completeness direction.** Every polynomial-time function belongs to
Cobham's algebra.

*Construction (TODO — the major remaining task):* simulate a polynomial-time
Turing machine inside the algebra.
1. Encode a full configuration (state, input tape, work tapes, output tape, head
   positions) as a bitstring, each tape split at its head so that head moves are
   bit-successor operations.
2. Show the one-step transition function is `Cobham`: it is a finite case split
   (finite `Q`, 4-symbol alphabet), each case realized by recursion on notation
   on single bits together with the block/concatenation operations already shown
   to be `Cobham` (`Cobham.append`, and analogous select/index helpers to add).
3. Iterate the step function `T(n)` times by limited recursion on notation over a
   clock string of length `T(n)` built from `smash` (`T` polynomial, via the
   normal form `mem_FP_iff_computesInTime_polynomial`).
4. Read the output off the halting configuration.
The length bounds throughout are polynomial, so every `boundedRec` side condition
is met. -/
theorem FP_subset_CobhamFP_internal : FP ⊆ CobhamFP := by
  sorry

end Cobham

end Complexity
