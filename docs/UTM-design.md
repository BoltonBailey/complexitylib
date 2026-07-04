# Universal Turing Machine — Design

Status: M1 (desc encoding + interpreter) done. This document specifies M2/M3:
the machine `utmTM : TM 6` and its semantic/time theorems.

## Overview

The UTM simulates **single-work-tape** machines only. Multi-tape machines are
handled by composing with the existing `NTM.singleTapeSim` quadratic
reduction (M3b). Because the simulated machine has exactly three heads
(input, work, output) and the UTM has six tapes, each simulated head is
shadowed by a dedicated UTM tape at the *same* position — so a simulated
step costs O(|description|) UTM steps (one table scan), not O(T). Total:
`C(α) · (T + |x| + 1)` for the whole run — *linear* in T.

The specification of the UTM is `TMDesc.toTM` (`UTM/Interp.lean`): for every
binary string `α`, `utmTM` on input `pair α x` behaves like
`(decodeDesc α).toTM` on input `x`. Well-formed descriptions round-trip
(`decodeDesc_encodeDesc_append`), and every `TM 1` has one (`descOfTM`).

## Tape layout (`utmTM : TM 6`)

| # | name    | contents                                   | head between iterations |
|---|---------|--------------------------------------------|------------------------|
| 0 | vInput  | `▷ x □ □ ⋯` — copy of `x`                  | simulated input head   |
| 1 | vWork   | simulated work tape                        | simulated work head    |
| 2 | vOut    | simulated output tape                      | simulated output head  |
| 3 | state   | `▷ q(w bit-syms) □ ⋯` — current state      | 0                      |
| 4 | desc    | `▷ translate(α) □ ⋯` — description         | 0                      |
| 5 | scratch | blank                                      | 0                      |

`translate(α)` = the `Γw`-symbol string decoded from α by 2-bit groups
(`00→0, 01→1, 10→□, 11→□` — must match `symOfPair` in `UTM/Desc.lean`).
Layout (from `TMDesc.syms`): `qstart-field □ qhalt-field □ entry □ ⋯ □ □`.
Width `w` := length of the qstart field = length of the state-tape content.

The `pair` encoding (`Classes/Pairing.lean`): `pair α x` = each bit of α
doubled, then `[0,1]`, then `x` verbatim. So the UTM input tape holds:
cells `2i+1, 2i+2` = `bᵢ bᵢ` (α's bits, doubled), then `0 1`, then `x`.
One desc symbol = 2 α-bits = 4 input cells.

## Simulation invariant

For a desc `d` (with `d = decodeDesc α`) and a config
`mc : Cfg 1 d.toTM.Q` of the interpreted machine:

```
SimInv α x mc :=
  vInput.cells = (initTape x.map(Γ.ofBool)).cells ∧ vInput.head = mc.input.head
  vWork  = mc.work 0
  vOut   = mc.output
  state:  cells 1..w = toBits w mc.state (as bit-syms), cell w+1 = □, head 0
  desc:   cells 1..|t| = translate(α), cell |t|+1 = □, head 0
  scratch: all-blank, head 0
```

Note `mc.input.cells = initTape(x).cells` always (input is read-only), so
vInput ≡ mc.input as a tape value.

State-tape content is exactly `w` bit-symbols where `w = (decodeDesc α).w`;
state values stay `< 2^w` because transition targets are the `q'` fields
(`toTM` reduces mod `2^w`; for in-range fields this is the identity, and the
UTM only ever copies `w`-bit fields).

## Phases

`utmTM = seqTM initTM (seqTM (loopTM bodyTM haltTestTM) extractTM)`
(exact nesting may adapt to the combinators' conventions).

### initTM
One left-to-right scan of the input:
- α-region: read input cells in pairs. `(b,b)` → one α-bit; every two α-bits
  emit one desc symbol (via `symOfPair`) onto tape 4. `(0,1)` → separator,
  switch to x-phase. `(1,0)` or odd/blank end → *malformed input*: go to
  halt with output `0` (totality; the semantic theorem only covers
  well-formed `pair α x` inputs).
  - odd trailing α-bit (pending bit at separator) is dropped — matches
    `groupPairs`.
- x-region: copy each cell verbatim to tape 0 (writes bits; blank ends scan).
Then: rewind tapes 0 and 4; copy desc field 1 (cells 1.. up to first □) onto
tape 3 (the state tape ← qstart); rewind tapes 3, 4.

Postcondition: `SimInv α x (toTM.initCfg x)` — all virtual heads at 0.
Time: O(|input|) + O(w) ≤ O(|input| + const).

### bodyTM (one simulated step)
Precondition: `SimInv α x mc ∧ mc.state ≠ qhalt`.
Postcondition: `SimInv α x (step mc)`.
Sub-phases (seq-composed or one machine):

1. **seek**: move desc head right past two fields (two □s) — now at start
   of entry region.
2. **match loop** over entries: for each segment,
   a. lockstep-compare state tape (cells 1..) with segment prefix: advance
      both heads; state hits □ and desc continues ⇒ need symbol compare of
      6 more desc cells against `Γ.encode` of the three virtual reads
      (2 cells each, vInput/vWork/vOut reads are available to δ at every
      step — no head movement needed to "read" them);
   b. on any mismatch: rewind state head to 0, skip desc head to next □;
      if the cell after that □ is □ ⇒ **no-match** → go to (4);
      else continue with next segment;
   c. on full key match (w state syms + 6 symbol syms): **copy phase** —
      copy the next w+10 desc cells to scratch (cells 1..w+10); if a □
      appears early ⇒ malformed entry ⇒ erase scratch (blank it), treat as
      mismatch (b). After w+10 cells, skip to next □ (excess ignored —
      matches `parseEntry` prefix semantics). Go to (3).
3. **apply**: scratch holds `q'(w) ww(2) wo(2) di(2) dw(2) dOut(2)`.
   a. copy scratch cells 1..w onto state tape (overwrite; state had exactly
      w cells, same width ⇒ no residue);
   b. read the five 2-cell groups; for each, decode
      (`00→0/left, 01→1/right, 10→□/stay, 11→□/stay` — must match
      `decΓw`/`decDir` in Desc.lean) and act on the virtual tapes:
      write `ww` on vWork, `wo` on vOut, then move vInput/vWork/vOut by
      `di/dw/dOut` — **sanitized**: if the virtual head reads `▷`, move
      right instead (matches `toTM`).
   c. blank scratch (cells 1..w+10), rewind scratch/state/desc heads.
4. **no-match default**: blank the state tape, copy desc field 2 (the
   qhalt field, verbatim, any width) onto it, rewind. The next halt-test
   compares the state tape against that same field and exits.
   **Alignment requirement**: `toTM` must make the abstract default
   transition also reach its halt state, *including* when the qhalt field
   is malformed (decoded sentinel `d.qhalt = 2^w`). With the original
   `q' % 2^w` target map the default would land on state `0` and keep
   running — a genuine mismatch. Fix (implemented): `toTM` maps transition
   targets via `min a.q' (2^w)` instead of `a.q' % 2^w`. In-range targets
   (< 2^w, i.e. every table-entry field) are unaffected; the default's
   target `d.qhalt` clamps to exactly `toTM.qhalt = min d.qhalt (2^w)` in
   all cases, matching the UTM's behavior. The invariant's state-width
   clause is suspended in this final halted configuration (correspondence
   treats no-match as a direct transition-to-halt).
5. Rewind state/desc/scratch heads to 0.

Time per iteration: O(|desc| + w) — each desc cell visited O(1) times in
the match loop (state rewinds cost ≤ w per segment, segments ≥ 1 cell;
generous bound `C₁·(|α| + w + 10)` per iteration is fine — constants are
absorbed per-machine).

### haltTestTM
Skip desc field 1 (qstart); lockstep-compare desc field 2 (qhalt) against
state tape; match (simultaneous □) ⇒ signal HALT to the loop combinator
(per `loopTM`'s convention). Rewind state/desc. No virtual tape changes.

### extractTM
Copy vOut cells 1.. verbatim (bits and blanks: copy-until-□) onto the
output tape cells 1... This preserves both `output.cells 1` (deciding) and
`hasOutput y` (function computation). Rewind nothing (done).

## Main theorems (M3)

```
utm_simulates_halting :
  ∀ α x (mc : Cfg) T, (decodeDesc α).toTM.reachesIn T (initCfg x) mc →
    mc halted →
    ∃ t ≤ C(α)·(T + |x| + w + 10) + D(α,x),
      utmTM.reachesIn t (utmTM.initCfg (pair α x)) (halted cfg with
        output cell 1 = mc.output cell 1 ∧ (hasOutput y → hasOutput y))

utm_decidesInTime-style corollary:
  (decodeDesc α).toTM.DecidesInTime L T ⇒
    utmTM decides {pair α x | x ∈ L}-ish on the pair-image within
    C(α)·(T ∘ len + len + const)   (precise statement in Lean)
```

Plus (M3b): composition with `descOfTM` and `singleTapeSim` for arbitrary
`TM k`.

## Simplifications / conventions

- Deciding-only extract would suffice for hierarchy theorems, but
  copy-until-blank is barely harder and supports function computation.
- The UTM never needs `w` explicitly: the state tape length IS `w`.
- Malformed pair input ⇒ halt with output 0 (semantic theorems only cover
  `pair α x` inputs).
- All per-α constants (desc length, w) are absorbed into `C(α)`;
  the hierarchy proof only needs: for FIXED α, simulation overhead is a
  constant factor + linear additive term.

## M2 prep changes to earlier layers

1. `TMDesc.toTM`: transition target `⟨min a.q' (2^w), _⟩` (was `% 2^w`) —
   aligns the no-match default with the UTM's "copy qhalt field" behavior.
   Fidelity proofs (`descOfTM_*`) adapt: in-range targets unaffected.
