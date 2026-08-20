/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive
public import Complexitylib.Classes.Containments.Internal.IPSubsetPSPACE
public import Complexitylib.Classes.P.Defs

/-!
# `IP ⊆ PSPACE`

⚠️ Unreviewed by Bolton

The easy half of `IP = PSPACE`.

The value of an interactive protocol on an input is the acceptance probability against an optimal
prover, and that value is the root of a finite game tree: the prover's moves maximize, the
verifier's coins average. Polynomial space evaluates the tree depth-first, holding one path of
messages at a time — the tree is exponentially wide but only polynomially deep, since both the
round count and the message lengths are polynomially bounded.

## Progress

The quantifier over prover strategies is now known to be finite. A strategy is a function on
*all* transcripts, of which there are infinitely many, so the supremum `IP` quantifies is a
priori a supremum over an infinite set — nothing a machine can search. `Protocol.transcript_congr`
and `Protocol.acceptEvent_congr` show that a run of `rounds n` rounds consults the strategy only
on transcripts of length at most `2 · rounds n`; together with the message-length bound carried
by `ProverStrategy.Bounded`, that cuts the search to a finite game tree of polynomial depth.

## What the proof still needs

- The optimal-prover value as a recursion over `Protocol.transcript` on that finite tree, and the
  fact that deterministic strategies suffice to attain it.
- Rational arithmetic in polynomial space for the averaging step.

## Main results

- `Protocol.transcript_length` — a run of `n` rounds produces `2 n` messages
- `Protocol.transcript_congr` — strategy extensionality for the transcript
- `Protocol.accepts_congr`, `Protocol.acceptEvent_congr` — and for acceptance

## TODO

- Evaluate the game tree; with `PSPACESubsetIP` this gives Shamir's theorem.
-/

@[expose] public section

namespace Complexity

/-- **`IP ⊆ PSPACE`**: the optimal prover's acceptance probability is the value of a
polynomially deep game tree, evaluated depth-first in polynomial space. -/
def IPSubsetPSPACE : Prop := IP ⊆ PSPACE

end Complexity
