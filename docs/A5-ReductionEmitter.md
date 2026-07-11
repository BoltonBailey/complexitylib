# A5 — Cook–Levin Reduction Emitter Design Doc

> **Completed — historical design document.** The emitter, its polynomial
> running-time proof, `reductionFn_mem_FP`, and the final Cook–Levin theorem
> are now proved under `Complexitylib/SAT/CookLevin/`, with final assembly in
> `Assembly.lean`. The status and “last `sorry`” target below are preserved as
> planning history, not as a description of the current library.

**Status:** design + foundation phase.
**Branch:** `feat/np-completeness`
**Target:** the library's last `sorry`:

```lean
theorem reductionFn_mem_FP (N : NTM 1) (p : Polynomial ℕ) :
    reductionFn N (fun n => p.eval n) ∈ FP
```

i.e. a concrete deterministic multi-tape machine `emitTM N p : TM K` with

```lean
(emitTM N p).ComputesInTime (reductionFn N (fun n => p.eval n)) T,   T =O (· ^ d)
```

where `reductionFn N T x = (tableauCNF N (T x.length) x).encode`. This is the
dominant cost of every mechanized Cook–Levin (most of Balbach's ~20k-line
Isabelle development); the design below reduces it to a disciplined grind.

## Why this is tractable here

1. **The encoding is unary.** `Lit.encodeRaw ℓ = ℓ.sign :: List.replicate ℓ.var true`,
   doubled bit-by-bit (`doubleBits`), with 2-bit separators (`[0,1]` after each
   literal, `[1,0]` after each clause). No binary arithmetic anywhere: the
   machine only needs unary counters, comparisons, and "emit a run of `2·v`
   trues".
2. **`encode` is a `++`-homomorphism.** `CNF.encode (φ ++ ψ) = φ.encode ++ ψ.encode`
   (immediate induction), so per-family emitters compose by `seqTM` with an
   *output-accumulator* postcondition.
3. **FP tolerates any polynomial.** `Nat.pair`-shaped variable indices are
   ~degree-16 in `steps = p.eval n`; the unary output is then a large
   polynomial. Irrelevant: `FP` existentially quantifies the degree.
4. **The Hoare layer exists.** `HoareTime pre post b` (state-abstracted tape
   triples), `seqTM_hoareTime` / `ifTM_hoareTime` / `loopTM_hoareTime`
   (invariant + variant), `AllTapesWF` discipline, `transitionTape` identity on
   stable tapes. Precedents: `GuessVerify.lean`, `VerifierTM.lean` (~5k lines
   each) drive real machines through this layer.
5. **Finite data lives in states.** `q : N.Q`, symbols `Γ` (4), the choice bit,
   and `N.δ`-lookups are finite — hardwired into the (parametric, `Fintype`)
   state space. Only `n`, `steps`, `P`, and loop counters `t, pi, pw, po` are
   unbounded — unary registers, one work tape each.

## Layers (bottom-up)

### R — Registers (`Models/TuringMachine/Registers.lean`)
Register predicate (reuse `CounterSubroutines` forms where possible):

```lean
def reg (v : ℕ) (t : Tape) : Prop :=        -- unary counter, head parked at cell 1
  t.cells 0 = Γ.start ∧ (∀ i < v, t.cells (i+1) = Γ.one) ∧
  (∀ j ≥ v + 1, t.cells j = Γ.blank) ∧ t.head = 1
```

Machines (all `TM K`, indices as parameters), each with a `HoareTime` spec
"registers `R` hold `vals`; afterwards `vals'`; other tapes preserved":
- `clearRegTM i` (≤ v+O(1) steps) — reuse `clearWorkTM`.
- `incRegTM i` — append one mark.
- `copyRegTM i j` — `reg v i ∧ reg w j → reg v i ∧ reg v j` (scan in lockstep).
- `addRegTM i j` — `reg v i ∧ reg w j → reg v i ∧ reg (w+v) j` (append v marks).
- `mulRegTM i j k` — `reg (v·w) k` via loop (variant = remaining marks of `i`),
  body = `addRegTM j k` + consume one mark of `i`; restore `i` afterwards.
- `cmpRegTM i j` — write `lt/ge` verdict to a fixed cell or branch via `ifTM`
  (used only inside `pairRegTM`).
- `inputLengthRegTM i` — `reg n i` (adapt `inputLengthPlusOneCounterTM`).

### E — Emission (`Models/TuringMachine/Emit.lean`)
The **output accumulator** (the campaign's central predicate):

```lean
def outAcc (ys : List Bool) (out : Tape) : Prop :=
  out.head = ys.length + 1 ∧ out.cells 0 = Γ.start ∧
  (∀ i (h : i < ys.length), out.cells (i+1) = Γ.ofBool ys[i]) ∧
  (∀ j ≥ ys.length + 1, out.cells j = Γ.blank)
```

Stable under `transitionTape` (head ≥ 1, reads blank ≠ `▷`), and
`outAcc ys out → out.hasOutput ys` — the bridge to `ComputesInTime` at the end.
Machines, specs of shape `{outAcc ys ∧ regs} tm {outAcc (ys ++ w) ∧ regs}`:
- `emitBitsTM (w : List Bool)` — fixed word, |w| steps (states = w's suffixes).
- `emitUnaryTM i` — `reg v i` ⊢ append `doubleBits (replicate v true)` = `2v`
  trues (loop over register marks, two writes per mark, restore head).
- `emitLitTM (sign) i` — `[sign,sign] ++ 2v trues ++ [false,true]` (compose).
- `emitClauseSepTM` — `[true,false]`.

### V — Variable computation (`SAT/CookLevin/EmitVar.lean`)
- `pairRegTM i j k` — `reg (Nat.pair v w) k` = `if v < w then w·w+v else v·v+v+w`:
  `ifTM` on `cmpRegTM` + `mulRegTM`/`addRegTM`. The only branching arithmetic.
- `encRegTM` — 4 nested `pairRegTM` for `enc tag a b c d`; tag and the constant
  components are state-hardwired emit-loops feeding fixed registers.
- `polyEvalTM p` — `reg n i ⊢ reg (p.eval n) j`: Horner over `p`'s (finitely
  many, hardwired) coefficients with `mulRegTM`/`addRegTM`.

### F — Family emitters (`SAT/CookLevin/EmitTableau.lean`)
One driver per `tableauCNF` family, *mirroring its `List.range`-`flatMap`
structure literally* so the loop-invariant is "output = encode of the emitted
prefix of the very same list expression":
- `emitOneHotStatesTM`, `emitOneHotCellsTM`, `emitOneHotHeadsTM` —
  loops over `t ≤ steps` (× `pos ≤ P`), inner finite one-hot templates
  (pairwise `atMostOne` over ≤ |Q| resp. 4 resp. positions — note
  `oneHotHeads`' at-most-one is over positions: a `pos × pos'` double loop).
- `emitStartClausesTM` — the only input-reading driver: scans `x` left-to-right
  emitting unit clauses per bit, then the work/output-tape start units.
- `emitFrameClausesTM` — `t × tp(3) × pos × s(4)` loop.
- `emitActiveTM` — `t × pi × pw × po` register loops; per tuple, a
  state-hardwired sequence over `(q, si, sw, so, b)` (≤ 128·|Q| finite cases,
  each emitting `activeClausesAt`'s ≤ 2 clauses of ≤ 9 literals via
  `emitLitTM`∘`encRegTM`).
- `emitAcceptTM` — two unit clauses at `t = steps`.

Each `HoareTime`: `{outAcc ys ∧ regs(n, steps, P)} … {outAcc (ys ++ (family …).encode) ∧ regs}`,
glued with `encode_append`. Loop invariants quantify the emitted list prefix
through `List.range` prefixes (`range_succ`, `flatMap_append`).

### A — Assembly (`SAT/CookLevin/EmitTableau.lean`)
`emitTM N p := seqTM (init: inputLengthReg; polyEvalTM p; P := steps+n+1) (7 family emitters)`.
Final spec at `initCfg x` (all-blank tapes ⊢ `outAcc []`), giving
`hasOutput ((tableauCNF N (p.eval n) x).encode)`, halting in
`T n = poly(n)` steps; `T =O (·^d)` via `BigO.of_polynomial_bound`-style bounds.
Then `reductionFn_mem_FP := ⟨d, K, emitTM N p, T, …⟩`. Zero sorries.

## Order of work (each step commits sorry-free)
1. `Emit.lean`: `outAcc` + stability + `hasOutput` bridge + `emitBitsTM` (validates
   the spec discipline against the combinator boundary effects). **← start here**
2. `Registers.lean`: `reg`, clear/inc/copy/add (+ specs).
3. `emitUnaryTM`/`emitLitTM` (first register×output composite).
4. `mulRegTM`, `cmpRegTM`, `pairRegTM`, `encRegTM`, `polyEvalTM`.
5. Family emitters, simplest first: `emitAcceptTM` → `emitStartClausesTM` →
   one-hots → frame → active (hardest, do last with patterns established).
6. Assembly + FP closure.

## Risks / notes
- The combinators' phase transitions (`transitionTape`) must be identity on all
  our predicates: `outAcc`/`reg` keep heads ≥ 1 off `▷` everywhere — maintain
  `AllTapesWF` in every pre/post.
- `loopTM_hoareTime`'s body obligation is stated against
  `(loopTM …).reachesIn` — follow `GuessVerify`'s usage patterns.
- Work-tape count `K`: fix once for the whole campaign (registers: n, steps, P,
  t, pi, pw, po, scratch a/b/c + pair temps) — `K = 12` with room to spare;
  unused tapes are harmless.
- Time accounting: keep bounds sloppy-generous (`≤ poly`), only the final
  `=O (·^d)` matters.
