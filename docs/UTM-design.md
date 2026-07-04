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

## Appendix: bodyTM state machine (full design)

All match/apply states carry `f : Bool × Bool × Bool` — the at-zero flags
for (vInput, vWork, vOut), i.e. "simulated head at position 0", captured by
the peek. Sim-read of tape t = `if f_t then ▷ else live UTM read of t`
(virtual heads are stationary throughout match, so live reads stay valid).

Key implementation tricks (all verified by hand-analysis):

1. **q'-field length sync**: the value's `q'` field has exactly `w` cells,
   and `w` is not statically known. During the key compare (`cmpQ`) the
   state head advances 1..w+1 in lockstep with desc. On key match the state
   head sits at cell w+1 (reading `□`). To copy exactly `w` value cells to
   scratch, move the state head LEFT in lockstep with the copy (one
   pre-step at the `cmpS→copyQ'` transition puts it at cell w): copy while
   the state head reads non-`▷`; when it reads `▷` (position 0) exactly `w`
   cells are copied and the forced bounce lands the state head at cell 1 —
   no separate rewind. Edge w = 0 works (pre-step hits `▷` immediately).
2. **appQ' length sync**: overwriting the state tape with the new state
   reads the OLD state cell before writing — stop when the old cell is `□`
   (old content had exactly w cells, and the q' in scratch has exactly w
   cells by construction). Scratch head then sits at the first action cell.
3. **Uniform mismatch path**: every mismatch (key compare fail, early `□`
   during value copy) goes: `skipSeg f` (desc right past next `□`) →
   `segCheck f` (reads `□` ⇒ no-match/default path; else this cell is the
   next segment's first cell) → `mmScr f` (blank-rewind scratch — harmless
   when clean) → `rewindSt f` (state left to `▷`, bounce) → `cmpQ f` with
   desc waiting at the new segment start.
4. **Default path needs f**: `toTM` sanitizes the default action's `stay`
   directions to `right` when a sim head reads `▷` — so the default
   transition moves virtual heads right-if-flag. Apply these three moves on
   one designated step (the `segCheck→default` transition). Writes are
   `readBackWrite` on all tapes in the default case (identity; at-zero the
   UTM reads `□` at cell 1 and writes `□` — exactly VShift.write_origin).
5. **Default must blank the state tape first**: the qhalt field may be
   shorter than w; stale tail cells would make the loop's halt test miss
   forever. Blank rightward until `□`, then copy the qhalt field.
6. **Action decoding**: value action cells are always bits (segments are
   `□`-free), read in 5 groups of 2 with a pending-bit in the state:
   g0 write ww on vWork (at-zero ⇒ write `□`, preserving the permanent `□`
   at cell 1), g1 write wo on vOut (same suppression), g2 move vInput,
   g3 move vWork, g4 move vOut (each move: at-zero ⇒ right, matching
   sanitize; decode `00→0/left, 01→1/right, 10→□/stay, 11→□/stay` exactly
   matching `decΓw`/`decDir`). Write-before-move per tape holds (g0<g3,
   g1<g4). δ-totality on `□` action cells: use the same decΓw/decDir
   conventions (unreachable under the spec pre).
7. **Matched-segment excess tail**: never skipped explicitly — cleanup
   rewinds desc from wherever it stands (left to `▷`, bounce).

State families (× f where noted):
- Phase 0 own-halt-check: `hc0` (skip field 1), `hc1` (lockstep compare
  state vs field 2; both-`□` ⇒ halted), `haltRewS`, `haltRewD` → bodyDone;
  mismatch ⇒ `preRewS`, `preRewD` → peek.
- Phase 1: `peek1` (all three virtual heads left), `peek2` (read: flags;
  all three right, back to positions) → `seek1 f`.
- Phase 2: `seek1 f`, `seek2 f` (desc right past two `□`s) → `cmpQ f`.
- Phase 3: `cmpQ f` (state/desc lockstep; state-`□` ⇒ `cmpS f 0` without
  desc move), `cmpS f (idx : Fin 6)` (desc cell vs bit idx of
  `Γ.encode(sim-read)` for si/sw/so), `skipSeg f`, `segCheck f`, `mmScr f`,
  `rewindSt f`, `copyQ' f` (trick 1), `copyAct f (j : Fin 10)`.
- Phase 4: `appRewScr f` (scratch rewind), `appQ' f` (trick 2),
  `appAct f (g : Fin 5) (pending : Option Bool)` (trick 6) → cleanup.
- Phase 5 default: `dfMoves` (trick 4, one step) → `dfScr` (blank-rewind
  scratch) → `dfStRew` → `dfBlank` (blank state rightward to `□`) →
  `dfStRew2` → `dfDescRew` → `dfSkip` (past field 1) → `dfCopy` (field 2 →
  state) → `dfStRew3`, `dfDescRew2` → bodyDone.
- Phase 6 cleanup: `clScr` (blank-rewind scratch) → `clSt` → `clDesc` →
  `bodyDone` (= qhalt).

Body spec (ghost style): given `SimInv`-shaped tapes for config `mc`,
reach `bodyDone` within `(|dSyms| + 2) * (|stSyms| + 24) + 40`-ish steps
with tapes in `SimInv` shape for `if mc halted then mc else step mc`
(state-tape clause: `toBits w (step mc).state` in the running case; the
qhalt field verbatim in the default case — covered by the invariant's
disjunct since the machine is then halted).

Correctness of the match loop against `TMDesc.lookup`: the desc segments
between `□`s correspond to `parseEntries`' segment split (same `takeField`
semantics); a UTM full-key-match on a segment ⟺ that segment parses
(length ≥ 2w+16 up to prefix) with key (q, si, sw, so) where q is the
state-tape number and si/sw/so the sim reads — first UTM match = first
`find?` match (needs `toBits w`-injectivity: fields of equal width w match
symbol-wise iff their `fromBits` agree). No-match ⟺ `find? = none` ⇒
`defaultAct`.

## Appendix 2: match-loop ↔ lookup correspondence (statements to prove)

Setting: desc tape holds `groupPairs α = qsF ++ □ :: qhF ++ □ :: R` where
`R` is the entry region; `d := decodeDesc α`, `w := d.w = |qsF|`;
state tape holds `stSyms := bitsToSyms (Nat.toBits w q)` for the current
state `q < 2^w`; live sim reads `(si, sw, so) : Γ³`.

Machine-level segment predicate (what cmpQ/cmpS/copyQ'/copyAct decide on a
segment `seg` — the cells before the next `□`):
```
MachMatch seg :=
  w + 6 ≤ seg.length ∧
  (∀ i < w, seg[i] = stSyms[i]) ∧
  (∀ i < 6, seg[w+i] = keyCell-cell i) ∧
  2*w + 16 ≤ seg.length          -- value copy completes (no early □)
```
(The first three conjuncts are the key compare; the machine detects their
failure OR the value-length failure and skips the segment either way.)

Key bridging facts (all pure list/data, no machine reasoning):
1. `keyCell`-cells as a list = `bitsToSyms (Γ.encode si ++ Γ.encode sw ++
   Γ.encode so)` where si/sw/so are the SIM reads (Body.simRead of flags +
   live cells) — by cases on the six indices.
2. For a □-free segment: `MachMatch seg ↔ (parseEntry w seg = some e ∧
   e.q = q ∧ e.si = si ∧ e.sw = sw ∧ e.so = so)` for the parsed `e` —
   via prefix-slice arithmetic (parseEntry's sequential take/drop chain),
   `toBits_fromBits`/`fromBits_toBits` for the state field, and
   `Γ.encode`-injectivity + `decΓ_encode` for the symbol fields.
3. Segment structure: `R` splits as `seg₀ □ seg₁ □ ... □ tail` with the
   parse stopping at the first empty segment — `parseEntries` is literally
   this recursion (`takeField`). The machine's skipSeg/segCheck walk is the
   same split. Firstness: the first `i` with `MachMatch segᵢ` corresponds
   to the first parsed entry matching the key, i.e. to
   `d.lookup q si sw so` via `find?` — needs "parse-skipped segments can't
   MachMatch" (they're too short: ¬(2w+16 ≤ len) contradicts MachMatch's
   last conjunct) and "parsed but key-mismatched segments don't MachMatch"
   (conjunct 2/3 fail via the injectivity bridges).
4. No-match: no segment MachMatches ∧ table exhausted (empty segment hit)
   ⟺ `find? = none` ⟺ lookup returns `d.defaultAct sw so` — the default
   path (dfScr…) then implements exactly `toTM`'s clamped default
   transition (see Verdict.lean for the halt-field part).
5. On match: the copied value cells (2w+16-prefix slice positions
   w+6..2w+16) decode exactly to `(lookup …).q'/ww/wo/di/dw/dOut` via
   `parseEntry`'s field slices and `grpΓw = decΓw ∘ pair` /
   `grpDir = decDir ∘ pair` bridges.

Assembly note: the per-iteration body proof then chains
hc-check (Verdict.lean) → peek (honest flags = at-origin facts) → seek
(scanRight_loop twice, landing the desc head at |qsF| + |qhF| + 3 =
start of R) → match-loop induction over the segment split (each round:
cmpQ_loop + cmpS_loop + either copy path or skipSeg/segCheck/mmScr/rewindSt)
→ apply (appRewScr/appQ'_loop/appAct) or default path → cleanup loops; the
loop-level invariant tracks "segments consumed so far all fail MachMatch"
and the desc-head position at the current segment start.
