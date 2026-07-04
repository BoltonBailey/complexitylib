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

## Fundamental constraint: heads cannot rest on ▷

`δ_right_of_start` forces every head reading `▷` to move right on **every**
step of **every** machine. A simulated head can legitimately sit at cell 0
(reading `▷`) for many UTM steps, so virtual heads cannot be shadowed at the
same position. **Resolution: the +1 shift.** Each virtual tape stores the
simulated tape shifted one cell right:

```
VShift sim utm :=
  utm.cells = (fun k => if k = 0 then ▷ else if k = 1 then □ else sim.cells (k-1))
  utm.head  = sim.head + 1
```

Consequences (all exact, no corner cases):
- UTM virtual head ≥ 1 always — stable across phase transitions (`Parked`).
- Simulated position 0 ⟺ UTM head at cell 1 ⟺ a left-peek sees `▷` —
  detectable in 2 steps (all three virtual tapes peek simultaneously).
- Sanitized moves: at sim-0 the interpreted machine always moves right
  (sanitization), which is a plain UTM right move 1→2. A left move from
  sim-1 to sim-0 is a plain UTM left move 2→1 (cell 1 = `□` ≠ `▷`, stable).
  Virtual heads never touch UTM cell 0.
- Writes at sim-0 are simulated no-ops; the UTM suppresses them using the
  at-zero booleans (in control state during the body).

## Tape layout (`utmTM : TM 6`)

| # | name    | contents                                    | head between iterations |
|---|---------|---------------------------------------------|------------------------|
| 0 | vInput  | `▷ □ x □ ⋯` — x shifted by 1                | sim input head + 1     |
| 1 | vWork   | simulated work tape, shifted by 1           | sim work head + 1      |
| 2 | vOut    | simulated output tape, shifted by 1         | sim output head + 1    |
| 3 | state   | `▷ q(w bit-syms) □ ⋯` — current state       | 1                      |
| 4 | desc    | `▷ translate(α) □ ⋯` — description          | 1                      |
| 5 | scratch | blank                                       | 1                      |

The real output tape carries the loop verdict (cell 1, `Γ.one` = halt) —
`loopTM`/`ifTM` read their tests' verdicts there. `extractTM` overwrites it
at the end.

`translate(α)` = the `Γw`-symbol string decoded from α by 2-bit groups
(must match `symOfPair`). Layout (`TMDesc.syms`):
`qstart-field □ qhalt-field □ entry □ ⋯ □ □`. Width `w` := qstart-field
length = state-tape content length.

`pair α x` (`Classes/Pairing.lean`): α's bits doubled, then `[0,1]`, then
`x` verbatim — one desc symbol = 2 α-bits = 4 input cells.

## Simulation invariant

For `d = decodeDesc α` and `mc : Cfg 1 d.toTM.Q`:

```
SimInv α x mc :=
  VShift mc.input  vInput      (mc.input.cells = initTape(x)-cells always)
  VShift (mc.work 0) vWork
  VShift mc.output vOut
  state:  cells 1..w = bit-syms of toBits w mc.state, cell w+1 = □, head 1
          — OR (mc halted ∧ cells 1.. = qhalt-field verbatim) after a
          no-match default transition (widths may differ; test still exits)
  desc:   cells 1..|t| = translate(α), cell |t|+1 = □, head 1
  scratch: cells 1.. all □, head 1
  real output: cell 1 ∈ {0,1} verdict, no stray ▷, head small/parked
```

## Combinator conventions (from the API survey)

- `loopTM tmBody tmTest`: **body runs first**, then test; test's verdict =
  real output cell 1 (`Γ.one` ⇒ exit). Iteration cost: body + 1 + test + 1
  + (output-head rewind p+1) + 1.
- Phase transitions apply `transitionTape` (identity iff head ≥ 1 and read
  ≠ ▷ — the `Parked` predicate). All six work tapes + input stay parked at
  all phase boundaries.
- `h_iter` obligations built from: `loopTM_body_simulation`,
  `loopTM_body_to_test`, `loopTM_test_simulation`, `loopTM_test_to_rewind`,
  `loopTM_rewind_loop`, `loopTM_check_halt` / `loopTM_check_continue`;
  halt disjunct packaged as `loopTM_iteration_halt`.
- `seqTM` composition via `seqTM_hoareTime` with `transitionTape` mid-shift.

## Phases

`utmTM = seqTM initTM (seqTM (loopTM bodyTM haltTestTM) extractTM)`.

### initTM
Single left-to-right input scan: α-region (cell pairs: `(b,b)` → α-bit;
two α-bits → one desc symbol via `symOfPair` written to tape 4; `(0,1)` →
separator; `(1,0)`/odd end → malformed: halt with output 0); x-region
(copy verbatim to tape 0 **starting at cell 2**). Then rewind tapes 0, 4;
copy desc field 1 (qstart) to state tape (tape 3); rewind 3, 4; position
all virtual heads at cell 1; write 0-verdict at output cell 1.
Post: `SimInv α x (toTM.initCfg x)`. Time O(|pair α x| + w).

### bodyTM (one simulated step) — single hand-written machine
Pre: `SimInv α x mc`. Post: `SimInv α x (if halted then mc else step mc)`.
Sub-phases (control states thread 3 at-zero booleans after peek):
0. **own halt check**: compare state tape vs desc field 2 (qhalt); on
   match rewind and exit (no-op body) — handles the body-runs-first
   convention when the machine is already halted.
1. **peek** (2 steps): all three virtual tapes move left, read (▷ ⟺ at
   sim-0), move back right. Records booleans (b_in, b_work, b_out).
2. **seek**: desc head right past two □s (to entry region).
3. **match loop** per segment: lockstep state-tape/desc compare (w cells),
   then 6 desc cells vs `Γ.encode` of the three *live* virtual reads
   (sim-read = at-zero ? ▷ : current cell — heads stationary during
   match); mismatch ⇒ rewind state head, desc to next □; □□ ⇒ no-match;
   full key match ⇒ copy next w+10 desc cells to scratch (early □ ⇒ blank
   scratch, treat as mismatch), skip to next □, go to apply.
4. **apply**: copy scratch 1..w → state tape; decode five 2-cell groups
   (`00→0/left, 01→1/right, 10→□/stay, 11→□/stay` — matches
   `decΓw`/`decDir`); write ww on vWork, wo on vOut (suppressed if the
   tape's at-zero boolean is set); move vInput/vWork/vOut by di/dw/dOut
   (at-zero ⇒ forced right, matching sanitization).
5. **no-match default**: blank state tape, copy qhalt field verbatim onto
   it (next test exits; `toTM`'s `min`-clamped target matches — see
   alignment note below).
6. **cleanup**: blank scratch, rewind state/desc/scratch heads to 1.
Time per iteration ≤ C₁·(|α| + 20) (each desc cell O(1) visits + state
rewinds ≤ w per segment ≤ segment length + const).

### haltTestTM
Compare state tape vs desc field 2 (skip field 1 first); write verdict to
real output cell 1 (`Γ.one` iff match); rewind state/desc to 1.
Correctness: state tape = toBits w q matches qhalt field iff
q = d.qhalt < 2^w (via toBits/fromBits bijection on w-bit fields);
malformed qhalt field (≠ w width) never matches a running state; after a
default transition the state tape holds the field verbatim ⇒ matches ⇒
exits. Time O(|α| + w).

### extractTM
Copy vOut cells 2,3,… (i.e. sim cells 1,2,…) verbatim to real output
cells 1,2,… up to and including the first `□`. Preserves both
`cells 1` (deciding) and `hasOutput y` (function computation).

### no-match alignment (implemented in Interp.lean)
`toTM` maps transition targets via `min a.q' (2^w)` so the default action's
target `d.qhalt` clamps exactly to `toTM.qhalt` even for the malformed-
qhalt sentinel `2^w`. Table-entry targets (< 2^w) unaffected.

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
