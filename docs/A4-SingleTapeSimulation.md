# A4 — Multi-Tape → Single-Tape Simulation Design Doc

**Status:** design phase. Scaffold in `Models/TuringMachine/SingleTape.lean`
composes (surface theorems real; 3 construction leaves `sorry`). This doc
pins down the construction so the ~1000-line implementation is not wasted.
**Branch:** `feat/np-completeness`
**Target:** the three construction leaves in `SingleTape.lean`:

```lean
noncomputable def singleTapeSim {k : ℕ} (N : NTM k) : NTM 1 := sorry
theorem singleTapeSim_allPathsHaltIn (N) (hN : N.AllPathsHaltIn T) :
    (singleTapeSim N).AllPathsHaltIn (singleTapeSimTime T) := sorry
theorem singleTapeSim_acceptsInTime_iff (N) (T) (x) :
    (singleTapeSim N).AcceptsInTime x (singleTapeSimTime T x.length)
      ↔ N.AcceptsInTime x (T x.length) := sorry
```

with `singleTapeSimTime T = fun n => (T n + n + 1)^2` (already fixed; its
polynomial bound `singleTapeSimTime_bigO` is **proved**).

**Unblocks:** `NTM.exists_singleTape_decider` → `cookLevin_reduction` (so
the Cook–Levin tableau only tracks one work tape). Also reusable for a UTM
(simulate a single-work-tape machine).

## 1. Goal

Given `N : NTM k` deciding `L` in time `T`, build `N' = singleTapeSim N : NTM 1`
that decides `L` in time `O((T + n + 1)²)`. The simulation is path-faithful:
for every choice sequence of `N` there is a corresponding (longer) choice
sequence of `N'` reaching the same accept/reject verdict, and conversely.

## 2. The two model constraints (and why they shape everything)

This model is **not** the textbook free-alphabet, two-sided-tape setting.

1. **Fixed 4-symbol alphabet** `Γ = {0,1,□,▷}`, write alphabet `Γw = {0,1,□}`.
   There is no room for the textbook "`2k`-track" super-alphabet, nor for a
   spare end-of-tape marker. A logical super-symbol must be **block-encoded**
   across several `Γ` cells.
2. **`δ_right_of_start`**: any head reading `▷` is *forced* to move right.
   Equivalently, a head cannot idle on cell 0. Cell 0 is permanently `▷`
   and writes there are no-ops.

A third, *simplifying* observation:

3. **Input/output tapes carry over for free.** `singleTapeSim N` and `N` are
   both started by `Cfg.init qstart x`, which sets `input = initTape (x.map ofBool)`,
   all work tapes `= initTape []`, `output = initTape []`. An `NTM 1` already
   has its own read-only input tape and its own output tape, with identical
   initial contents and identical semantics to `N`'s. So the simulator reads
   `N`'s input head directly, writes `N`'s output exactly as `N` does, and the
   accept bit (`output.cells 1`) needs no translation. **Only the `k` work
   tapes are consolidated onto the single work tape.**

## 3. Work-tape encoding (`encodeWork : (Fin k → Tape) → Tape`)

We encode the `k` work-tape *positions ≥ 1* position-major, in **binary only**,
reserving literal `□` as the end-of-used-region sentinel.

Let block width `w := 3*k`. The single work tape's cell 0 is `▷` (global).
For super-position `p ≥ 1`, block `p` occupies cells
`B(p) .. B(p)+w-1` where `B(p) := 1 + (p-1)*w`. Within block `p`, for each
tape `j ∈ {0,…,k-1}`:

| offset in block | meaning | code |
|---|---|---|
| `3j`, `3j+1` | symbol of tape `j` at position `p` | `00`=`□`, `01`=`0`, `10`=`1` |
| `3j+2` | head-present bit of tape `j` at position `p` | `0`=absent, `1`=present |

All active cells are in `{0,1}`; **a literal `□` never occurs inside an active
block.** A super-block `p` is *materialized* iff `p ≤ M`, where `M` is the
maximum work-tape position any head has ever reached. The used region is
exactly cells `1 .. w*M`; **cell `w*M + 1` is `□`** (the sentinel), and so is
everything past it. Reading rightward from cell 1, the first `□` marks the end.

Conventions / invariants:

- **Head at position 0.** Position 0 is the `▷` cell, never materialized. So
  "tape `j`'s head is at position 0" ⇔ "no head-present bit for tape `j` is set
  in any materialized block." Reading such a head yields `▷`.
- **Exactly one head per tape.** For each `j`, at most one head-present bit is
  set across all materialized blocks (none ⇔ head at 0).
- **Position-0 symbol is `▷`,** never stored (immutable).
- **`initTape []` is already valid.** Initially every head is at 0 and every
  symbol is `□`; that is `M = 0`, used region empty, cell 1 `= □`. The single
  work tape `initTape []` (▷ at 0, `□` elsewhere) encodes this with **zero
  initialization steps.**

`decodeWork`/`SimInv`: rather than a partial inverse, correctness is stated as
a relation `SimInv (w₁ : Tape) (w : Fin k → Tape) : Prop` ("`w₁` encodes the
`k` tapes `w`"), capturing the layout above (symbols, the unique head markers,
the `□` sentinel at `w*M+1`). Round-trip lemmas: `SimInv (encodeWork w) w`,
and `SimInv` is preserved by one simulated macro-step (§5).

## 4. Simulator state type

`(singleTapeSim N).Q` is a finite sum of phase-tagged records, all finite
because `k` is fixed and `N.Q`, `Γ`, `Fin k → Γ`, `Dir3` are finite:

- `run (q : N.Q)` — between macro-steps; about to simulate an `N`-step from `q`.
- `gather (q) (j : Fin k) (acc : Fin k → Γ) (iSym oSym : Γ) (sweepflags)` —
  sweeping right to read each head symbol into `acc`.
- `compute (q) (gathered : Fin k → Γ) (iSym oSym : Γ)` — apply `N.δ b …`
  (the choice bit `b` is the simulator's own nondeterministic choice at this
  step), producing `(q', workWrites, outWrite, inDir, workDirs, outDir)`.
- `scatter (q') (writes : Fin k → Γw) (dirs : Fin k → Dir3) (…sweep state…)`
  — sweeping to write new symbols and move each head marker, materializing one
  new block if a head steps past `M`.
- `commit (q') (outWrite) (inDir) (outDir) (…)` — apply input/output
  write+move, return head to cell 1, enter `run q'`.
- `halt` ↦ mapped to `N.qhalt` semantics. `qstart' := run N.qstart`,
  `qhalt' := dedicated halt state`.

The choice bit: `N'`'s `δ b …` uses `b` only at the `compute` transition (to
pick `N.δ b`), so a single `N`-step consumes exactly one *meaningful* choice;
the sweep sub-steps ignore `b`.

## 5. One macro-step (simulating one `N`-step)

From `run q` with single work head returned to cell 1:

1. **Read input/output, dodge `▷`.** Read `input.read =: iSym`, `output.read =: oSym`.
   If `iSym = ▷` (input at 0): `N` *must* move input right this step, so move
   input right now and mark "input committed." Else keep input stationary.
   Symmetric for output (`output` write at cell 0 is a no-op anyway).
2. **GATHER.** Sweep the work head right across materialized blocks to the `□`
   sentinel, recording each tape's head symbol into `acc : Fin k → Γ`
   (`acc j = ▷` for any `j` with no marker found). Keep input/output stationary
   (now off `▷`, so legal).
3. **COMPUTE.** `(q', wWr, oWr, inDir, wDirs, oDir) := N.δ b q iSym acc oSym`.
   Stash in state.
4. **SCATTER.** Sweep back/forth writing `wWr j` at each tape `j`'s marked
   block and moving its marker per `wDirs j` (a left/right move = clear current
   bit, set neighbor's bit). If some `wDirs j` moves a head to position `M+1`,
   append one fresh block (symbol `□`, that head's bit set), advancing the `□`
   sentinel by `w`. Writes at position 0 are dropped (no-op, matches model).
5. **COMMIT.** Apply `output.writeAndMove oWr oDir` and `input.move inDir`
   *unless already committed in step 1*; return work head to cell 1; go to
   `run q'`. If `q' = N.qhalt`, go to `qhalt'`.

Each macro-step touches `O(w*M) = O(k*M)` cells; with `k` fixed and
`M ≤ T(|x|)`, that is `O(T)` sub-steps. Returning the head to cell 1 is another
`O(T)`. Over `≤ T` macro-steps the total is `O(T²)`, plus an `O(n)` term to
first reach input positions — comfortably inside `(T + n + 1)²`.

## 6. Time bound

`singleTapeSimTime T n = (T n + n + 1)²`. Per §5 each of the `≤ T(|x|)`
macro-steps costs `≤ c·(T(|x|) + |x|)` sub-steps for a small constant `c`
(absorbed by widening the bound; `w = 3k` is a per-machine constant, and the
`AcceptsInTime`/`AllPathsHaltIn` statements quantify over a *single* bound, so
constant factors are folded into the squared bound exactly as
`singleTapeSimTime_bigO` already accounts for). The `+ n` covers input-head
travel; the `+ 1` keeps the base case (`T = n = 0`) non-degenerate.

## 7. Proof decomposition (the next scaffold layer)

Introduce `SingleTape/Internal.lean`:

1. `encodeWork`, `SimInv`, block-index helpers `B`, `blockOffset`, and the
   binary symbol codec, with arithmetic round-trip lemmas. *(pure data — real)*
2. `macroStep : Cfg 1 Q' → Cfg 1 Q'` correspondence:
   `simInv_macro : SimInv c₁.work c.work → (gathered/compute faithful) →
   SimInv (after macro) (N.step-image of c)` — the core invariant-preservation
   lemma, proved by tracing the sub-step sequence (GATHER, SCATTER, COMMIT).
3. `macro_reaches : N'.trace (cost of one macro) … = run q'` config-level
   correspondence, and its iterate `macro_reaches_iter` over `m` macro-steps.
4. **`singleTapeSim_acceptsInTime_iff`** assembled from (3): an accepting
   `N`-path of length `t ≤ T` maps to an accepting `N'`-path of length
   `≤ singleTapeSimTime T`, and conversely (`N'` halts ⇒ its `run`-state trace
   projects to an `N`-halt).
5. **`singleTapeSim_allPathsHaltIn`** from (3) + `N.AllPathsHaltIn T`: every
   `N'`-path completes `≤ T` macro-steps then halts.

`singleTapeSim_decides` and `exists_singleTape_decider` already compose these
(real, in `SingleTape.lean`).

## 8. Risks / open points

- **Index arithmetic.** `B(p) = 1 + (p-1)*3k` round-trips and the per-block
  offset reasoning are the tedious part; isolate in pure lemmas (`omega` after
  `Nat.div`/`Nat.mod` facts) before any tape reasoning.
- **Sub-step bookkeeping.** SCATTER needs a careful, *bounded* sweep protocol
  (go right to sentinel, then return), each direction a distinct phase tag, to
  keep the head-return cost `O(T)` and the state finite.
- **`▷` dodging.** The step-1 early-move for input/output must be matched
  exactly at COMMIT to avoid a double-move; proved by case-splitting on
  `iSym = ▷` / `oSym = ▷` and using `δ_right_of_start` for `N`.
- **Choice alignment.** `N'` consumes one meaningful choice bit per `N`-step
  (at COMPUTE) and ignores the rest; the `AcceptsInTime` translation pads the
  choice sequence to length `singleTapeSimTime …` (cf. `trace_mono`,
  `AcceptsInTime_mono`, already proved).

## 9. Scale

This is the largest single construction in the repo (comparable to, or larger
than, `verifyPairTM`). It is multi-session. The general-`k` Cook–Levin tableau
(`tableauCNF`, stated for `NTM k`) does **not** depend on this simulation for
*correctness* — only `reductionFn_mem_FP` is restricted to `NTM 1`, to keep the
poly-time emitter tracking one work tape. So the single-tape reduction's payoff
is (a) a simpler FP emitter and (b) UTM reuse; it is not on the critical path
for the *truth* of `tableauCNF_satisfiable_iff`.
