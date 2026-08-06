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

- `CobhamFP_eq_FP` — Cobham's algebra equals `FP`
- `Cobham.of_eq`, `Cobham.comp₂`, `Cobham.comp₃` — congruence and usable
  composition at small arities
- `Cobham.const`, `Cobham.append`, `Cobham.appendFn`, `Cobham.pairing`,
  `Cobham.tail`, `Cobham.dispatch`, `Cobham.dropPrefix`, `Cobham.takePrefix`,
  `Cobham.lengthPad` — the working toolkit: constants, concatenation,
  self-delimiting pairing, bit peeling, branching on a bit, prefix/suffix
  splitting at a given length, and unary length. These are the operations a
  machine interpreter written inside the algebra needs, and each is a single
  limited recursion on notation.
- `Cobham.takeFn`, `Cobham.dropFn`, `Cobham.zeroBlockFn`, `Cobham.padFn`,
  `Cobham.repeatFn`, `Cobham.blockFn` — fixed-width block packing and
  addressing: pad every field of a configuration to one ruler's width and field
  `i` is `blockFn … i`, so the algebra never needs a self-delimiting decoder
- `Cobham.tableFn` — finite table dispatch, the shape of a machine's transition
  function: finitely many constant patterns, first match wins
- `Cobham.dispatch₀`, `Cobham.iteFn`, `Cobham.andFn`, `Cobham.orFn`,
  `Cobham.notFn`, `Cobham.bitAtFn`, `Cobham.headFlagFn`, `Cobham.matchPrefixFn` —
  the Boolean layer in which a machine's finite transition table gets written:
  total dispatch, if-then-else, the connectives, bit extraction, and testing a
  string against a fixed constant. `matchPrefixFn` is a *finite* composition for
  each constant — the induction is at the meta level, not inside the algebra
- `Cobham.iterFn`, `Cobham.exists_pow_clock` — **the class is closed under
  clocked iteration**, and polynomial clocks are available. Iterating a step
  function once per bit of a clock string is a single limited recursion on
  notation whose step ignores the bit it peels and applies `f` to its own
  recursive value; the clock's *length* is the iteration count, and `smash`
  builds clocks of any polynomial length. This is the skeleton of the
  completeness direction: encode configurations, show one machine step is in the
  class, then iterate under a polynomial clock.

Two of these carry the weight. `dispatch` shows that branching is free: the step
functions of `recNotation` are already selected by the bit being peeled, so a
one-step recursion on `v 0` *is* an if-then-else on its leading bit.
`dropPrefix` shows how to move an argument that changes along a recursion —
`recNotation` fixes its parameters, so the changing value has to live in the
recursion's *value*, and iterating `tail` there gives `drop`. With `drop` in
hand, `takePrefix` reads off successive bits, and fixed-width pairing with
projections follows.

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

The last constructor case, `fpn_boundedRec`, rests on a general closure
property of `FP` alone, `Cobham.iterate_mem_FP`: `FP` is closed under iterating
an `FP` function once per bit of an `FP` ruler, given an `FP` bound on the width
of the intermediate states.

Everything between that lemma and the constructor case is proved. Recursion on
notation is the encoded-argument loop `recFold`
(`Cobham.recFold_eq_recNotation`); Cobham's limited-recursion side condition
makes the width clamp vacuous (`Cobham.recFoldClamp_eq_recFold`); and the
clamped loop is that iteration on a packed state
(`Cobham.loopStep_mem_FP`, `Cobham.loopStep_iterate`), giving
`Cobham.recFoldClamp_mem_FP`. Realizing one iteration inside `FP` needed three
closure properties the library did not have, all proved here:
`Cobham.appendFn_mem_FP` (concatenation, via the `Cobham.catTM` scanner),
`Cobham.selectHeadFn_mem_FP` (branching on a bit — every other `FP` primitive
fixes its output length from its inputs' lengths, so `Complexity.headFlag`
turns the bit test into a length), and `Cobham.exists_exact_ruler` (a ruler of
length *exactly* `p.eval |z|`, which is the width the clamp names).

**Completeness (`FP ⊆ CobhamFP`)**, `Cobham.FP_subset_CobhamFP_internal`, is now
fully proved: a polynomial-time machine is simulated inside the algebra. A whole
configuration is one block-aligned bitstring with each tape split at its head, so
a head move is a two-bit shift (`Cobham.cfgCode`); the transition function is the
finite table `Cobham.stepFn`, dispatching on the constant key patterns
(`Cobham.keyPattern`) with each branch a short composition of the toolkit; the
run is `Cobham.iterFn` over a clock string built from `smash`
(`Cobham.exists_pow_clock`); and the output is read off the output tape after a
second iteration walks its head back to cell `0` (`Cobham.rewindFn`,
`Complexity.cellBits`, `Complexity.runTrue`). The assembly is
`Cobham.simFn_mem` / `Cobham.simFn_eq`.

`Cobham.iterate_mem_FP` itself is the one machine-level construction of the
soundness direction, assembled in
`Complexitylib.Classes.P.Cobham.Internal.Iterate`: `TM.forRegTM_hoareTime`
drives a body that runs `F`'s machine on the state tape as a virtual input
(`TM.applyTM`), moves the result back with `Complexity.copyToVirtualInputTM`,
and blanks the witness machine's scratch between iterations with
`Complexity.resetTapesTM` — a content-agnostic wipe, since an opaque witness
machine may leave gaps that a content-driven eraser would stop at.
-/


@[expose] public section

namespace Complexity


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
