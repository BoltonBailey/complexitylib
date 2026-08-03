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

The last constructor case, `fpn_boundedRec`, is proved modulo a single
machine-level loop lemma, `Cobham.recFoldClamp_mem_FP`: iterating a
width-clamped `FP` step function once per bit of `sndBlock z`. Everything else
in that case — that recursion on notation is the encoded-argument loop
`recFold` (`Cobham.recFold_eq_recNotation`), and that Cobham's
limited-recursion side condition makes the width clamp vacuous
(`Cobham.recFoldClamp_eq_recFold`) — is proved. The two `FP` primitives that
loop needs are also in place: `Complexity.reverse_mem_FP` (to consume the
recursion string back to front) and `Complexity.takeLen_mem_FP` together with
`Cobham.exists_ruler` (to carry the width clamp as a string rather than a
number).

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

So the only remaining gap in `CobhamFP_eq_FP` is the soundness-side loop lemma
`Cobham.recFoldClamp_mem_FP`.
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
