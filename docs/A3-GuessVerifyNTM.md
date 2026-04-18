# A3 — Guess-and-Verify NTM Design Doc

**Status:** design, pre-implementation
**Branch:** `feat/sat-verifier`
**Target theorem:** `NP.witness_ntm_of_dtm_verifier` in
`Complexitylib/Classes/NP/Witness.lean:92`
**Unblocks:** `SAT ∈ NP` (the headline of the branch) once the SAT-specific
verifier in P (task B) is also built.

## 1. Goal

Discharge the sorry at `Witness.lean:92`:

```lean
theorem witness_ntm_of_dtm_verifier
    {R : List Bool → List Bool → Prop}
    {p : Polynomial ℕ} {c k : ℕ}
    {M : TM k} {f : ℕ → ℕ}
    (hp : ∀ x y, R x y → y.length ≤ p.eval x.length)
    (hM : M.DecidesInTime (pairLang R) f)
    (hfO : f =O (· ^ c)) :
    ∃ (k' d : ℕ) (N : NTM k') (g : ℕ → ℕ),
      N.DecidesInTime (witnessLang R) g ∧ g =O (· ^ d)
```

i.e.: build an NTM `N` that decides `{x | ∃ y, R x y}` in polynomial time,
given a polynomial-time DTM `M` deciding `pairLang R = {pair x y | R x y}`
and a polynomial witness-length bound.

## 2. Given primitives

From the existing codebase (all proved, no sorries):

- **`pairBuildTM yIdx pIdx : TM k`** (`PairBuildTM.lean`, proved).
  Given input tape holding `x` and work tape `yIdx` holding `y`, writes
  `pair x y` onto work tape `pIdx`. Hoare spec:
  `pairBuildTM_hoareTime` with bound `pairBuildTime |x| |y| = 4·|x| + 2·|y| + 10`.
  Postcondition: `pIdx` head = 1, cell 0 = `▷`, cells 1..|pair| =
  `Γ.ofBool pair[i]`, cell |pair|+1 = `□`.
- **`retargetInput M : TM (k+1)`** (`Combinators.lean`, proved).
  Theorem `retargetInput_decidesVirtual`: given `M.DecidesInTime L T`, for
  any `z : List Bool` and any real input `realInput`, running
  `retargetInput M` from the initial config *where work tape k holds
  `initTape (z.map Γ.ofBool)`* reaches a halting config in `≤ T |z|` steps,
  outputting `1/0` per `z ∈ L`.
  → This gives us "simulate M on whatever is on work tape k, ignoring the
  input tape."
- **`TM.toNTM : TM n → NTM n`** (proved, `TuringMachine.lean:516`).
  Lifts a DTM into an NTM that ignores the choice bit. Both δ₀ and δ₁
  equal the DTM's δ.
- **`BigO.pow_polynomial_bound`** and **`BigO.of_polynomial_bound`**
  (`Asymptotics.lean`, proved). Convert between `f =O (·^c)` and
  `∀ n, f n ≤ p.eval n`.

**What does not exist:** any NTM-side Hoare framework, any NTM
combinator (`unionNTM`, `seqNTM`, …), any NTM-specific composition
reasoning infrastructure. Everything about the nondeterministic machine
must be proved directly against `NTM.trace`.

## 3. High-level architecture

The NTM `N` has **three phases** executed in sequence:

1. **Guess phase.** Nondeterministically write a witness `y` of length
   exactly `p.eval |x|` onto a dedicated work tape (the "witness tape"),
   then advance to the pair phase. One NTM step per guessed bit, plus a
   final "end-of-guess" transition.
2. **Pair phase.** Run the lifted DTM `pairBuildTM yIdx pIdx` (via
   `TM.toNTM`) to build `pair(x, y)` on the pair tape, reading `x` from
   the input tape and `y` from the witness tape.
3. **Verify phase.** Run `toNTM (retargetInput M)`, whose "virtual input"
   is the pair tape. Output whatever M outputs.

Each phase is sequenced by having the halting state of one phase coincide
with the starting state of the next, and by carefully crafting the
transition at the phase boundary so tape heads and contents are in the
right configuration for the next phase.

## 4. Tape layout and arity

Let `k'` be the total number of work tapes. We must budget for:

- M's own `k` work tapes (used internally by M during verification).
- The pair tape (call its index `pIdx`, holds `pair(x, y)` after phase 2).
- The witness tape (call its index `wIdx`, holds `y` after phase 1).

`retargetInput M : TM (k+1)` adds one work tape (index `k`) to M,
treating it as the virtual input tape. So when we wrap it, that work-tape
index must be the pair tape.

**Proposed layout:** `k' = k + 2` work tapes, with

- tapes `0..k-1` — M's internal work tapes.
- tape `k` — the **pair tape** (the virtual input for `retargetInput M`).
- tape `k+1` — the **witness tape** (holds `y` after the guess phase).

With this layout:
- `pIdx := ⟨k,   by omega⟩ : Fin k'`
- `wIdx := ⟨k+1, by omega⟩ : Fin k'`
- `wIdx ≠ pIdx` trivially (needed by `pairBuildTM_hoareTime`).

Phase 2 calls `pairBuildTM wIdx pIdx`, phase 3 treats tape `pIdx` as the
virtual input for M.

## 5. State type

The NTM's state `Q` is a disjoint union of three chunks:

```lean
inductive GuessPhase where
  | bit       -- currently guessing bit i
  | endGuess  -- guess done, transition to pair phase

-- Existing: PairBuildPhase (9 constructors) from pairBuildTM
-- Existing: (retargetInput M).Q ≅ M.Q

def Q : Type := GuessPhase ⊕ PairBuildPhase ⊕ (retargetInput M).Q
```

where:

- `qstart := .inl .bit` (start in guess phase).
- `qhalt  := .inr (.inr (retargetInput M).qhalt)` (halt when M halts).
- The guess-phase's final transition leads to `.inr (.inl .init)`
  (pairBuildTM's start state).
- PairBuildTM's halt state `.done` is remapped to transition into
  `.inr (.inr (retargetInput M).qstart)` — i.e., the guess-phase and
  pair-phase never *actually halt*; they transition into the next
  phase's start state instead.

**Technical wrinkle:** pairBuildTM's "done" state in isolation is its
`qhalt` and no step fires from there. In the composed NTM, δ on this
state must instead transition into the verify phase. Concretely, the
composed δ pattern-matches on the state: for the "done-of-pairBuildTM"
constructor, it computes the transition into the verify phase rather
than delegating to pairBuildTM's δ (which is irrelevant there because
no step fires in the standalone DTM). This is the standard pattern used
by `seqTM` for DTMs.

### Guess-phase transitions

The guess phase uses a single step per witness bit. At state
`.inl .bit` with choice bit `b`:

- **If the witness counter (tracked by the witness tape's head position)
  is `< p.eval |x|`:** write `b` to cell (head) of the witness tape,
  move witness-tape head right, stay in `.inl .bit`.
- **If the head has reached position `p.eval |x| + 1`:** transition to
  `.inl .endGuess`.

But: the state type has no counter. Two options:

**Option A: counter-free, use tape position.** The witness tape's head
position *is* the counter: cell `i+1` holds the guessed `y[i]`. When the
head reads a `□` (blank) at some position, we've reached the end of the
witness tape. But we're writing as we go, so the cell under the head is
always blank right before the write. Distinguishing "last bit of witness"
from "any other bit" requires external info.

**Option B: baked-in counter.** Parameterize the state type by a `Fin (p.eval |x|+1)`
counter. Problem: the polynomial `p` depends on `|x|`, so the state type
would depend on `x`, which is not allowed — `Q` is fixed at NTM
construction, not per-input.

**Option C: unary counter on a second tape.** Add a *guess-counter tape*
initialized with `p.eval |x|` tally marks (these must be produced before
the guess starts, e.g., by copying from the input tape or by computing
`p.eval |x|` in unary). Decrement on each guess step, halt guess when
counter hits zero.

Option C is clean but adds complexity: we need a pre-guess phase that
materializes `p.eval |x|` tally marks on a dedicated tape. Evaluating a
polynomial on `|x|` in unary on a TM is a well-studied primitive but
requires a nontrivial sub-construction.

**Recommended: hybrid Option A+B.** Guess *any* length, then at the
transition to the pair phase, cap witness length at `|x| + p.eval |x|`
*structurally* by bounding the step budget. Concretely, the overall
time bound `g(|x|)` includes `p.eval |x|` for the guess phase; if a
choice sequence tries to guess longer, it runs out of steps and fails
`AllPathsHaltIn`. For acceptance, we only need the *existence* of a
choice sequence that (a) guesses exactly the witness length |y|, (b)
runs pairBuildTM and M to completion within budget.

Let me sharpen this. The guess-phase state machine is:

- `.inl .bit`: on any input, with choice `b`:
  - if `b = false`: write `Γ.blank` (leave blank), move witness head
    left, transition to `.inl .endGuess` (i.e., "end of guess").
    Wait — we can't move a witness head with a blank under it without
    writing something. Let me redesign.

Revised guess-phase design:

- `.inl .writeBit`: on any input, with choice `b`:
  - write `Γ.ofBool b` to the witness tape, move witness head right,
    stay in `.inl .writeBit`.
- `.inl .endGuess`: on any input, with *both* choices, move witness
  head right one more step and transition to `.inl .rewindWitness`.

But we need a way to *enter* `.inl .endGuess`. How does the NTM decide
when to stop guessing? The choice bit selects "guess another bit" vs
"stop guessing":

- `.inl .chooseContinue`: choice bit determines next state.
  - δ₀ (choice = false, "stop"): transition to `.inl .rewindWitness`.
  - δ₁ (choice = true, "continue"): write nothing yet, transition to
    `.inl .writeBit`.
- `.inl .writeBit`: choice bit = witness bit b.
  - δ_b: write `Γ.ofBool b` to witness tape, move witness head right,
    transition back to `.inl .chooseContinue`.
- `.inl .rewindWitness`: DTM-like rewind phase. Move witness head left
  until reading `▷`. Similar structure to `rewindWorkTM` / pairBuildTM's
  rewindP1/P2.

When the witness tape is rewound (head = 0, then right to head = 1 on
the transition), transition to the pair phase's init state.

### Pair-phase and verify-phase transitions

Once in pair phase (`.inr (.inl .init)`), the composed NTM's δ delegates
to pairBuildTM's δ (ignoring the choice bit) until pairBuildTM reaches
its halt state. Then δ at the pairBuildTM-halt state transitions into
the verify phase (`.inr (.inr (retargetInput M).qstart)`).

Verify phase delegates to `(retargetInput M).δ`. It terminates at
M's original halt state.

## 6. Time analysis

Phase-by-phase:

1. **Guess:** `2 · |y| + 1` steps (one write + one choose per bit, plus
   one final stop). For the "right" choice sequence where `|y| ≤ p.eval |x|`,
   this is `≤ 2 · p.eval |x| + 1` steps.
2. **Rewind witness:** `|y| + 1` steps (one per tape cell plus a transition).
3. **Pair:** `4·|x| + 2·|y| + 10` (pairBuildTime).
4. **Verify:** `f (|pair x y|) = f (2·|x| + 2 + |y|)` steps.

Total for the accepting choice sequence, when `|y| ≤ p.eval |x|`:

```
g(|x|) := 2·p.eval|x| + 1 + p.eval|x| + 1 + 4·|x| + 2·p.eval|x| + 10 + f(2·|x| + 2 + p.eval|x|)
       ≤ c₁ · p.eval|x| + c₂ · |x| + f(c₃ · (|x| + p.eval|x|))
```

Since `f ≤ polynomial_of_c` (by `BigO.pow_polynomial_bound` on `hfO`),
and `p` is a polynomial, composing polynomials yields a polynomial.
Total bound: `g` is polynomially bounded, so `g =O (·^d)` for
`d := degree of composite` (via `BigO.of_polynomial_bound`).

**All-paths-halt requirement:** we need to choose `g(|x|)` such that
*every* choice sequence of length `g(|x|)` halts. This is where the
guess-phase design matters — the composed NTM must halt no matter what
choices are made. We achieve this by structuring the guess phase so that:

- if the choice sequence ever picks `chooseContinue → false` (stop), we
  enter rewind + pair + verify with whatever witness was guessed so far;
- if the choice sequence *never* picks stop, the machine runs out of
  steps before reaching the pair phase — but this violates
  `AllPathsHaltIn`.

Workaround: cap the guess-phase by structure. Add a "kill counter"
state `.inl .chooseContinue` that *forcibly* transitions to stop after
`2·p.eval|x| + 1` attempts. But again, the state type can't depend on
`|x|`. Alternative: add a counter-tape, as in Option C above.

**Cleanest fix:** bound the guess-phase length *externally* by the step
budget, and in the acceptance/`AllPathsHaltIn` proof, handle two cases:

- Case A (accepting, `x ∈ witnessLang R`): there exists `y`, `|y| ≤ p.eval |x|`,
  with `R x y`. Pick choices that guess `y` then stop. Machine halts
  in `g(|x|)` steps, outputs 1.
- Case B (non-accepting, `x ∉ witnessLang R`): for *every* choice
  sequence, either
  - the guess phase stops early with some `y'`, then pair+verify runs to
    halt; since `¬ R x y'`, M outputs 0.
  - the guess phase never stops — need to force halt here.

To force halt in Case B's infinite-guess subcase, the guess phase must
*structurally* cap. Without a per-input counter, the only mechanism is
**to have the guess phase unconditionally advance a bounded counter
that's encoded in the *tape contents* rather than the *state type*.**

**Final decision: Option C — use a counter tape.** Add one more tape
for the unary counter. This requires a pre-guess phase that writes
`p.eval |x|` tally marks, then the guess phase decrements the counter
per bit. When the counter hits zero, the guess phase is forced to stop.

So: `k' = k + 3` total work tapes (M's `k` + pair + witness + counter).

### Counter-tape construction

The counter tape starts empty. Before the guess phase, we need to
evaluate `p(|x|)` in unary on the counter tape. This is a polynomial
evaluation in unary, which requires:

- Computing `|x|` in unary (copy from input tape: one cell per input bit).
- Multiplication in unary (for `|x|^k` terms): `|x|^k` unary cells is
  `|x|^k` tape, which is polynomial.
- Addition in unary: trivial concatenation.

This is all standard TM stuff, but nontrivial. Alternatively, we can
sidestep polynomial evaluation entirely by computing an upper bound:

**Simplification:** replace `p.eval |x|` with `|x|^d + d` for some fixed
`d` from `hp` + `BigO.pow_polynomial_bound`. A unary upper bound
`|x|^d + d` can be laid down on the counter tape by `d` rounds of
"for each cell of `x`, copy the entire current counter tape." This is
still nontrivial.

**Further simplification (possibly used):** observe that any polynomial
`p` is dominated by `(|x| + 1)^d` for some `d`. In unary, `(|x| + 1)^d`
can be computed by `d - 1` multiplication passes, each of which is
itself a DTM subroutine.

→ This sub-construction is large enough to merit its own design doc
(call it **A3.1 — Unary Polynomial Evaluator**). It will likely
dominate the LOC of A3.

## 7. Proof strategy

Three layers of proof obligation:

### 7a. `AllPathsHaltIn g`

For every `x` and every choice sequence `choices : Fin (g |x|) → Bool`,
the final state after `g |x|` steps is `qhalt`.

Structure: phase-by-phase analysis.

- Guess phase halts deterministically once the counter hits zero, *regardless
  of choices*. Reason: counter decreases by 1 per step, counter-zero
  → transition to rewind. Steps ≤ `p.eval |x| · 2 + 1` (two steps per
  bit: write + choose).
  *Alternative:* choice bit picks stop → transition immediately.
  Either way, bounded.
- Rewind witness: DTM-like. Steps ≤ `|y'| + 1` where `|y'|` is the
  actual guessed length (≤ `p.eval |x|`).
- Pair: bounded by pairBuildTime.
- Verify: bounded by `f`.

Summed: `g(|x|)` as above.

### 7b. Acceptance direction (`x ∈ L → AcceptsInTime x (g |x|)`)

Given `y` with `R x y` and `|y| ≤ p.eval |x|`, construct the choice
sequence that:

1. Guesses `y`: alternates `chooseContinue := true, writeBit := y[i]`
   for i = 0..|y|-1, then `chooseContinue := false`. This takes
   `2·|y| + 1` steps.
2. Pads remaining steps with arbitrary bits (all zeros).

Show that this choice sequence drives the machine through the three
phases, each leaving the tapes in the configuration required by the
next phase, and ends with `output.cells 1 = Γ.one`.

This decomposes via three simulation lemmas:

- **Guess-simulates:** starting from `N.initCfg x`, after `2·|y| + 1`
  steps with the right choices, the config has state `.inl .rewindWitness`
  (or the appropriate initial state), witness tape holds `y`, pair tape
  is empty, other tapes unchanged.
- **Pair-simulates:** from the guess-phase-final config, after
  `pairBuildTime |x| |y| + 1` steps (one transition step + pairBuildTM's
  own runtime), the config has state `.inr (.inr (retargetInput M).qstart)`,
  pair tape holds `pair(x, y)`, other tapes unchanged.
  **This uses `pairBuildTM_hoareTime` via a DTM→NTM lifting lemma.**
- **Verify-simulates:** from the pair-phase-final config, after `≤ f(|pair x y|)`
  steps, machine halts with `output.cells 1 = Γ.one` (since `pair x y ∈ pairLang R`).
  **This uses `retargetInput_decidesVirtual` via the same lifting.**

Each simulation lemma requires a **DTM-inside-NTM simulation lemma**,
along the lines of:

```lean
lemma toNTM_trace_eq_iterate_step (tm : TM n) (c : Cfg n tm.Q) (t : ℕ)
    (choices : Fin t → Bool) :
    (tm.toNTM).trace t choices c = tm.iterateStep t c
```

which would reduce NTM trace reasoning about a lifted DTM into DTM
`reaches`/`reachesIn` reasoning. This **does not yet exist** and must
be written.

### 7c. Non-acceptance direction (`x ∉ L → ¬ AcceptsInTime x (g |x|)`)

For every choice sequence, after `g |x|` steps, `output.cells 1 ≠ Γ.one`.
Equivalent: every choice sequence ends with `output.cells 1 = Γ.zero`.

Case-split on what the guess phase produces:

- Guess produces some `y'` of length ≤ `p.eval |x|` (possibly < actual
  witness length). Then pair tape holds `pair(x, y')`. M decides
  `pair x y' ∈ pairLang R`. Since `x ∉ witnessLang R`, there's *no* `y`
  with `R x y`, so in particular `¬ R x y'`, so `pair x y' ∉ pairLang R`,
  so M outputs 0.

That's it — if `AllPathsHaltIn` (7a) is proved, then every path halts,
guess produces some `y'`, verify rejects.

## 8. Subtask breakdown

I'd build A3 in this order, committing after each:

1. **A3.0** — Add `NTM.HoareTime` / `NTM.Hoare` analogues in
   `Hoare/Defs.lean`. Pre/post predicates abstracted over choice
   sequences. Not strictly necessary if I'm willing to inline, but
   ~200 LOC up front saves ~1000 later.
2. **A3.1** — DTM-in-NTM simulation lemma:
   `toNTM_trace_eq_reachesIn` (roughly). Lifts DTM Hoare triples to
   NTM-trace reasoning.
3. **A3.2** — Unary polynomial evaluator DTM + Hoare triple.
   (Writes `p.eval |x|` tallies on a work tape.) Large — may warrant
   its own design doc.
4. **A3.3** — Guess-phase NTM + Hoare triple.
5. **A3.4** — Composed NTM: state type, δ/δ₀, phase-transition glue.
6. **A3.5** — Phase simulation lemmas (guess / pair / verify).
7. **A3.6** — `AllPathsHaltIn` proof.
8. **A3.7** — Acceptance + non-acceptance proofs.
9. **A3.8** — Polynomial time bound via `Asymptotics`.
10. **A3.9** — Assemble `witness_ntm_of_dtm_verifier`.

Estimated LOC: 2000–3000, comparable to the full combinators file plus
pairBuildTM.

## 9. Open questions

- **Unary poly evaluator feasibility.** Is it simpler to just use a
  counter that counts *in binary* and decrements? Binary counters are
  simpler to *maintain* (O(1) amortized per decrement, log n cells) but
  requires reading/writing multi-cell values per step, which needs more
  states. Unary is single-cell per step but needs polynomial tape
  setup. Need to prototype.
- **Can we avoid the counter tape entirely?** If instead we relax the
  step bound — say, set `g(|x|) := c · p.eval|x|` and structurally bound
  the guess phase to stop after `p.eval|x|` steps by *having it halt
  unconditionally on step overflow via the state machine*. But the state
  machine has no memory beyond Q; the counter *must* be on a tape.
- **State type size.** `GuessPhase ⊕ PairBuildPhase ⊕ M.Q` is fine as
  long as `M.Q` is a `Fintype` (which it is). Lean's `Fintype` instance
  for `Sum` is automatic.
- **`DecidableEq` for the state type.** Sum of decidable-eq types is
  decidable-eq; automatic.
- **Alphabet** — pairBuildTM writes `Γw ⊆ Γ` (no `▷`). The guess phase
  only writes `Γ.zero`/`Γ.one` to the witness tape. Counter tape writes
  tally marks (use `Γ.one`) + blanks. All within `Γw`.
- **Interaction with `retargetInput`'s readBackWrite.** `retargetInput`
  simulates M by reading the virtual-input tape and *writing back what
  it read* so the cells are preserved. This is already handled inside
  `retargetInput` — we just need the pair tape to be initialized
  correctly before the verify phase.

## 10. Recommendation

Start with **A3.0 (NTM Hoare)** and **A3.1 (DTM-in-NTM simulation)**,
get them compiling, then revisit whether to tackle A3.2 (polynomial
evaluator) or explore if an ordinal-like counter on a binary tape is
cleaner. The polynomial evaluator is the biggest unknown; prototyping
it early would de-risk the rest.
