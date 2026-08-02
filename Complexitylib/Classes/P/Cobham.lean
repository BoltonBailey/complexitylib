/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Complexitylib.Classes.P.Cobham.Defs
public import Complexitylib.Classes.P.Cobham.Internal
public import Complexitylib.Classes.P.Defs
public import Complexitylib.Classes.P.NormalForm
public import Complexitylib.Classes.P.Composition

/-!
# Cobham's characterization of FP — surface layer

Cobham's theorem (1965): the machine-independent function algebra `Cobham` of
`Complexitylib.Classes.P.Cobham.Defs` carves out exactly the polynomial-time computable
string functions. The headline statement is `CobhamFP_eq_FP`.

## Main results

- `CobhamFP_eq_FP` — Cobham's algebra equals `FP` *(draft: proof in progress —
  see the reduction status below)*
- `Cobham.of_eq`, `Cobham.const`, `Cobham.append` — basic members and congruence,
  validating that the algebra is usable

## Reduction status (draft)

The equivalence is reduced in `Complexitylib.Classes.P.Cobham.Internal` to a small
work-list of named lemmas via a multi-arity bridge (`Cobham.encodeVec`,
`Cobham.FPn`).

**Soundness (`CobhamFP ⊆ FP`)** is the induction `Cobham f → FPn f`
(`Cobham.cobham_imp_FPn`) specialized to arity one. All six constructor cases are
discharged at the structural level:

- `fpn_empty`, `fpn_proj`, `fpn_bit`, `fpn_smash`, `fpn_comp` — fully proved,
  modulo the atomic machine lemmas below;
- `fpn_boundedRec` — reduced to `recNotation_eq_foldr` (proved: recursion on
  notation is a `List.foldr` of `recNotationStep`) plus the loop machine.

The `empty`, `proj`, and `bit` cases are now fully axiom-clean; their underlying
**atomic machine lemmas** are proved as bespoke Turing-machine transducers bridged
to `ComputesInTime`:

- `cons_mem_FP` — prepend a fixed bit (string successor), via `consBitTM`;
- `sndBlock_mem_FP` — decode the block suffix, via the `sndBlockTM` scanner;
- `fstBlock_mem_FP` — decode the block payload, via the `fstBlockTM` scanner.
  (The existing `pairSplitCoreTM` only handles valid pair inputs, so the *total*
  decoders needed their own machines.)

The `comp` case is now fully axiom-clean too: `pairFn_mem_FP` (pair two `FP`
outputs) is reduced via `mem_FP_pairWithInput` to the self-contained `reorderTM`
scanner (copy the leading block verbatim, then decode the next block's payload),
which is built and verified. So four of the six constructor cases — `empty`,
`proj`, `bit`, `comp` — are complete.

The `smash` case is complete as well: `mulUnpair_mem_FP`
(`Complexitylib.Classes.P.Cobham.Internal.MulLen`) counts the leading block's
payload into a unary work register and then emits that many `false` bits once
per remaining input symbol, giving `|A|·|B|` zeros from `pair A B`; `fpn_smash`
follows via `mulLenFn_mem_FP`. So five of the six constructor cases — `empty`,
`proj`, `bit`, `comp`, `smash` — are complete.

The last constructor case, `fpn_boundedRec`, is proved modulo a single
machine-level loop lemma, `Cobham.recFoldClamp_mem_FP`: iterating a
width-clamped `FP` step function once per bit of `sndBlock z`. Everything else
in that case — that recursion on notation is the encoded-argument loop
`recFold` (`Cobham.recFold_eq_recNotation`), and that Cobham's
limited-recursion side condition makes the width clamp vacuous
(`Cobham.recFoldClamp_eq_recFold`) — is proved.

**Completeness (`FP ⊆ CobhamFP`)**, `Cobham.FP_subset_CobhamFP_internal`, is still
a single `sorry`: it simulates a polynomial-time machine inside the algebra —
configurations encoded as bitstrings with each tape split at the head (so head
moves are bit-successor operations), the transition function a finite case split
via recursion on notation on single bits, and the run `T(n)` iterations of the
step function via recursion on notation on a clock string of length `T(n)` built
from `smash`.
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-- The class respects pointwise equality of functions. Useful because the constructors
of `Cobham` produce syntactically specific lambda terms. -/
theorem of_eq {n : ℕ} {f g : (Fin n → List Bool) → List Bool} (hf : Cobham f)
    (h : ∀ v, f v = g v) : Cobham g :=
  (funext h : f = g) ▸ hf

/-- Every constant function is in the class: build the constant string bit by bit from
`empty` and the successors. -/
theorem const {n : ℕ} (s : List Bool) : Cobham fun _ : Fin n → List Bool => s := by
  induction s with
  | nil => exact .empty
  | cons b s ih => exact (Cobham.comp (.bit b) fun _ : Fin 1 => ih).of_eq fun v => rfl

/-- Concatenation is in the class, by limited recursion on notation on the first
argument with bound `smash (true :: x) (true :: y)`. -/
theorem append : Cobham fun v : Fin 2 → List Bool => v 0 ++ v 1 := by
  -- Recursion on notation computing `x ++ y`: base `y`, step `b :: ·` on the
  -- recursive value.
  have hrec : ∀ (x : List Bool) (v : Fin 1 → List Bool),
      recNotation (fun v : Fin 1 → List Bool => v 0)
        (fun w : Fin 3 → List Bool => false :: w 1)
        (fun w : Fin 3 → List Bool => true :: w 1) x v = x ++ v 0 := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih => cases b <;> simp [ih]
  -- The bit-prepending step functions are in the class.
  have hstep : ∀ b : Bool, Cobham fun w : Fin 3 → List Bool => b :: w 1 := fun b =>
    (Cobham.comp (.bit b) fun _ : Fin 1 => .proj 1).of_eq fun v => rfl
  -- The length bound `smash (true :: x) (true :: y)` is in the class.
  have hj : Cobham fun w : Fin 2 → List Bool =>
      Complexity.smash (true :: w 0) (true :: w 1) :=
    (Cobham.comp .smash fun i : Fin 2 =>
      (Cobham.comp (.bit true) fun _ : Fin 1 => .proj i).of_eq fun v => rfl).of_eq
        fun v => rfl
  refine (Cobham.boundedRec (.proj 0) (hstep false) (hstep true) hj ?_).of_eq fun v => ?_
  · intro x v
    rw [hrec]
    have h1 : (Fin.cons x v : Fin 2 → List Bool) 1 = v 0 := rfl
    have hexp : (x.length + 1) * ((v 0).length + 1) =
        x.length * (v 0).length + x.length + (v 0).length + 1 := by ring
    simp only [Fin.cons_zero, h1, smash_length, List.length_append, List.length_cons]
    omega
  · rw [hrec]
    rfl

end Cobham

/-- Cobham's algebra is sound for polynomial time: every function of the (unary
fragment of the) algebra is computable by a deterministic TM in polynomial time.

Proof via the multi-arity soundness induction `Cobham.cobham_imp_FPn` specialized
to arity one; see `Complexitylib.Classes.P.Cobham.Internal` for the reduction and
its remaining open constructor cases. -/
theorem CobhamFP_subset_FP : CobhamFP ⊆ FP :=
  Cobham.CobhamFP_subset_FP_of_FPn

/-- Cobham's algebra is complete for polynomial time: every polynomial-time computable
function belongs to the algebra.

Proof by simulating the machine inside the algebra; see
`Complexitylib.Classes.P.Cobham.Internal`. -/
theorem FP_subset_CobhamFP : FP ⊆ CobhamFP :=
  Cobham.FP_subset_CobhamFP_internal

/-- **Cobham's theorem**: the machine-independent function algebra of
`Complexitylib.Classes.P.Cobham.Defs` characterizes exactly the polynomial-time
computable string functions. -/
theorem CobhamFP_eq_FP : CobhamFP = FP :=
  Set.Subset.antisymm CobhamFP_subset_FP FP_subset_CobhamFP

end Complexity
