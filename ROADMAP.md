# Complexitylib roadmap

This roadmap is a contribution guide for extending Complexitylib from its current
machine- and circuit-level foundations into a broad, reusable formalization of
computational complexity theory. It is intentionally ambitious, but it is not a
list of promises. Each headline theorem is decomposed into intermediate artifacts
that are independently useful and small enough to review.

The ordering below is dependency-driven. A later track may be explored early, but
its final class-level theorem should normally wait for the shared encodings,
resource accounting, and finite-probability infrastructure on which it depends.

## Current baseline

The library already contains substantial foundations:

- A concrete Arora--Barak-style model of deterministic, nondeterministic, and
  probabilistic Turing machines over a fixed four-symbol alphabet, with explicit
  time and space predicates.
- Reusable machine combinators, Hoare-style specifications, unary registers,
  emitters, counters, pairing machines, multi-tape-to-single-tape simulation, and
  a universal-machine development.
- Definitions of major classes including `DTIME`, `NTIME`, `DSPACE`, `NSPACE`,
  `P`, `PPoly`, `NP`, `BPP`, `RP`, `ZPP`, `PP`, `PSPACE`, `EXP`, `NEXP`, `SC`,
  `FNP`, and `TFNP`, together with selected containments and closure results.
- A deterministic time-hierarchy theorem in a concrete, clock-constructible
  formulation.
- A bit-level SAT encoding, polynomial-time verifier, computation tableaux, and a
  full Cook--Levin reduction culminating in SAT NP-completeness.
- A typed Boolean-circuit model with size and depth, AND/OR bases, CNF and DNF,
  Shannon bounds, essential-input and gate-elimination lower bounds, Schnorr's XOR
  lower bound, nondeterministic quantification bounds, and a Valiant-style depth
  reduction theorem.
- A growing collection of concrete languages that exercise the machine API and
  witness nontrivial class membership.
- A logarithmic-cost random access machine model with a soundness theorem
  distinguishing it from the unsound unit-cost measure.
- A Fourier-analysis-of-Boolean-functions subtheory (`Complexitylib.BooleanAnalysis`,
  after Ryan O'Donnell): Chapter 1, with the parity functions as an orthonormal
  basis, Fourier coefficients/weights, and the mean/variance/convolution API — the
  analytic foundation for small-depth-circuit lower bounds and natural proofs.

This baseline is not yet a single unified theory. In particular, machine
encodings, circuit families, uniformity, advice, oracle access, interactive
protocols, and cryptographic security need common interfaces before their
headline equivalences can be stated cleanly.

## Guiding principles

1. **State the exact theorem variant.** Resource conventions, uniformity notions,
   error constants, zero-length inputs, promise behavior, and encoding choices
   belong in theorem statements or immediately adjacent documentation.
2. **Separate definitions, proof machinery, and surface theorems.** Definitions
   and public theorem statements should remain short enough to audit; large
   simulations and arithmetic proofs belong in `Internal` modules.
3. **Prefer reusable bridges over isolated headline proofs.** A verified circuit
   evaluator, transcript encoding, or finite counting lemma is more valuable than
   a one-off proof that bypasses the shared API.
4. **Account for resources compositionally.** Every construction should expose a
   concrete bound first and an asymptotic corollary second.
5. **Use finite counting before importing heavier probability machinery.** The
   current PTM semantics already counts functions `Fin T -> Bool`; exact finite
   arguments are often easier to compute with and audit.
6. **Preserve executable witnesses where practical.** Machines, circuits,
   reductions, encoders, and protocol verifiers should be definitions, not merely
   existential objects.
7. **Keep textbook abstractions honest about representations.** Complexity is
   measured on encodings. Parsing, malformed inputs, output length, and conversion
   between `List Bool` and `Fin n -> Bool` must be explicit.
8. **Land small steps.** A contribution should ideally add one definition, one
   structural lemma family, or one theorem layer and leave the repository building
   without errors or warnings.

## Dependency overview

```text
core API and encodings
  +-- deterministic/probabilistic finite counting
  +-- machine and circuit evaluators
  |     +-- nonuniform TM/circuit bridge + advice
  |     |     +-- BPP subset P/poly
  |     +-- uniform circuits <-> TMs
  |     |     +-- NC/AC uniformity
  |     |           +-- Barrington and bounded-depth lower bounds
  |     +-- canonical complete problems and reductions
  +-- protocol/transcript infrastructure
  |     +-- interactive-proof classes
  |           +-- sum-check and IP = PSPACE
  +-- oracle machines and security games
        +-- relativized worlds
        +-- pseudorandom functions
              +-- natural-proofs barrier
```

## Near-term tracks

### N0. Core API consolidation and proof ergonomics

**Goal.** Make foundational tape, run, encoding, and asymptotic facts available
from stable public modules so later work does not duplicate local lemmas.

**Prerequisites.** None beyond the existing library.

**Current progress.** The core model now exposes alphabet separation facts,
`Tape.ext`, initialized/started-tape cell and read lemmas, `Tape.move_cells`,
`Tape.write_head`, canonical register-cell facts, and DTM time-bound
monotonicity. Several large consumers have been migrated away from private
copies; endpoint/run lemmas and a few older local tape helpers remain.

**Staged milestones.**

- [ ] Add a canonical extensionality and simplification API for `Tape`, `Cfg`,
  `Tape.init`, `Γ.ofBool`, `TM.reachesIn`, and `NTM.trace`.
- [ ] Consolidate repeated endpoint-determinism, run-concatenation, halting, and
  time-bound monotonicity lemmas.
- [ ] Give all major constructions a named concrete time/space bound and a
  separate `BigO` theorem.
- [ ] Audit aggregation modules so public imports do not need to name proof-only
  implementation files.
- [ ] Add lightweight regression examples for core simplification behavior.

**Formalization hazards.** Broad `[simp]` attributes can make machine-step goals
explode or loop. Prefer projection lemmas and narrowly oriented rewrite rules over
marking full transition definitions as simp lemmas. Moving a theorem must preserve
its public name or provide a compatibility alias.

**Small entry tasks.**

- [x] Centralize tape extensionality, write-head/move-cell projections,
  initialized Boolean/blank tape facts, and canonical register-cell lemmas.
- [S] Add the remaining narrowly oriented projections for `write`, `move`, and
  `writeAndMove` as concrete consumers demonstrate the need.
- [S] Migrate the remaining older modules to the shared initialized-tape and
  Boolean-symbol lemmas, deleting their local wrappers where this stays clear.
- [x] Add `TM.reachesIn_snoc`, endpoint uniqueness (`TM.reachesIn_right_unique`),
  and `TM.step_eq_none_iff_halted`.
- [S] Refresh module documentation that still describes completed proofs as
  skeletons.

### N1. Canonical bit-string, finite-function, and encoding bridges

**Goal.** Establish one shared representation layer between languages
(`List Bool`), fixed-length circuit inputs (`Fin n -> Bool`), natural-number
indices, and serialized objects.

**Prerequisites.** N0 is helpful but not required.

**Current progress.** Fixed-length Boolean strings now have a canonical
`List Bool` bridge. Fan-in-two AND/OR circuits also have a canonical proof-free
codec with exact decoding, explicit malformed-input rejection, a polynomial
bit-length bound, and a tagged family wrapper covering the empty input. The
remaining milestones below concern reusable codec abstractions and encodings for
other object types.

**Staged milestones.**

- [x] Define lossless conversions between lists of known length and
  `BitString n`, with round-trip, length, map, append, and indexing lemmas.
- [x] Give fan-in-two AND/OR circuits a canonical proof-free encoding with an
  exact partial decoder and a concrete polynomial bit-length bound.
- [x] Separate encoded circuit validity from evaluation, with explicit rejection
  of truncation, trailing data, bad tags, and non-topological references.
- [ ] Define a reusable `Encodable`-style interface specialized to binary strings:
  encoder, partial decoder, round-trip theorem, and size bound.
- [ ] Give canonical encodings to finite functions, machine states,
  configurations, and bounded transcripts.
- [ ] Add pairing and tagged-sum codecs compatible with the existing pairing
  language and polynomial-time machines.

**Formalization hazards.** Dependent equality between `Fin n -> Bool` values and
lists with proof-carrying lengths can dominate proofs. Keep conversions
computational, isolate casts behind named lemmas, and avoid making proof fields
part of extensional encodings. Size bounds must count bits rather than rely only on
injectivity.

**Small entry tasks.**

- [S] Add analogous `List.ofFn` bridge lemmas for a non-Boolean alphabet when a
  second consumer demonstrates the need for a generic API.
- [S] Add a codec for `Fin n` with an explicit `Nat.log2`-style length bound.
- [x] Encode/decode the four tape symbols and three directions, including malformed
  bit patterns (`Complexitylib.Models.TuringMachine.UTM.Encoding`: `Γ`, `Γw`, `Dir3`
  two-bit codecs with round-trip, length, injectivity, and `[true, true]` rejection
  lemmas).
- [M] Define a generic length-bounded codec combinator for lists.

### N2. Finite counting and error amplification toolkit

**Goal.** Build exact lemmas for random bit strings, bad-event counts, independent
blocks, majority, and union bounds. This is the common prerequisite for BPP,
interactive proofs, and cryptographic games.

**Prerequisites.** Existing `NTM.acceptCount`, `acceptProb`, and rational
probability definitions; N1 for encoded experiments.

**Current progress.** `Complexitylib.Classes.FiniteCounting` has the sample-space
cardinality `card (Fin T -> Bool) = 2^T`, the prefix/suffix block split packaged
as an `Equiv` (projection and concatenation maps inverse by construction), the
finite union bound `card_filter_exists_le`, and a strict-`majority` function with
its odd-length negation antisymmetry `majority_not_of_odd`. The remaining
milestones concern finite event probability, amplification, and permutations.

**Staged milestones.**

- [x] Develop cardinality lemmas for `Fin T -> Bool`, restriction to prefixes,
  concatenation into blocks, and permutations of random bits (`card_finArrowBool`,
  `blockEquiv`/`blockFst`/`blockAppend`, `eventProb_map`).
- [x] Define finite event probability once and relate it to `Finset.card` and the
  existing rational PTM probabilities (`Complexitylib.Classes.EventProb`:
  `eventProb`, its basic laws, and `NTM.acceptProb_eq_eventProb`).
- [~] Prove union, complement, conditioning-by-partition, and product lemmas.
  *(`eventProb_union_le`, `eventProb_compl`, and the `popCount` complement count
  done; conditioning-by-partition and product remain.)*
- [ ] Formalize binomial coefficients and majority failure counts in the exact
  finite sample space used by machines.
- [ ] Prove a concrete amplification theorem from error `1/3` to `2^-k` (or another
  explicit exponentially small bound) with a fully specified repetition count.
- [ ] Lift the combinatorial theorem to a reusable PTM repetition construction.

**Formalization hazards.** Independence should not be smuggled in through an
informal product argument: the bijection between one long choice string and blocks
must be explicit. Rational inequalities involving powers and floors can be harder
than the counting argument. A crude but sufficient exponential bound is preferable
to formalizing an optimal Chernoff constant first.

**Small entry tasks.**

- [x] Prove `Fintype.card (Fin T -> Bool) = 2^T` in the form needed by
  `acceptProb`.
- [x] Define block projection and concatenation maps and prove they are inverse.
- [x] Prove the finite union bound for a list of predicates by card counting.
- [x] Implement a majority function on `Fin k -> Bool` and prove its complement
  symmetry.

### N3. Canonical complete problems and reduction infrastructure

**Goal.** Turn Cook--Levin into a reusable ecosystem of complete problems rather
than a single endpoint.

**Prerequisites.** Existing SAT semantics, encodings, verifier, and polynomial
many-one reduction.

**Staged milestones.**

- [~] Prove transitivity, identity, composition-time, and class-closure lemmas for
  polynomial reductions in their most reusable forms. *Decomposed:*
  - [x] `≤ₚ` reflexivity/transitivity *modulo* two `FP` facts
    (`Classes/NP/Reduction.lean`: `MapReducesPoly.refl_of_id_mem`,
    `MapReducesPoly.trans_of_comp`) — isolates exactly what remains.
  - [ ] `id ∈ FP` — build a copy TM (input tape → output tape) with a linear
    `ComputesInTime` proof; then `≤ₚ` is reflexive.
  - [ ] `FP` closed under `∘` — a sequential-composition TM (run `f`'s machine,
    pipe its output tape to `g`'s input tape, run `g`'s machine) with a
    `poly ∘ poly = poly` time bound; then `≤ₚ` is transitive.
- [ ] Define and relate SAT, CNF-SAT, and 3SAT encodings; prove a size-controlled
  Tseitin transformation.
- [ ] Add standard NP-complete graph languages such as CLIQUE, VERTEX-COVER, and
  INDEPENDENT-SET with explicit codecs.
- [~] Add TQBF/QBF syntax and semantics as the canonical PSPACE problem.
  *(`Complexitylib.SAT.QBF`: `QBF` syntax, `QBF.eval` semantics, quantifier
  substitution lemmas, `freeVars` + semantic locality `eval_eq_of_agree`, and the
  closed-formula TQBF layer `Closed`/`IsTrue`/`eval_closed_eq` all done; only the
  PSPACE-completeness theorem itself remains.)*
- [ ] Prove one PSPACE-completeness route only after the space-simulation API is
  stable.

**Formalization hazards.** Textbook reductions often silently assume random-access
arrays, fresh-variable generation, or unary/binary number encodings. The reduction
machine must produce the exact language encoding, and output length bounds must be
proved before polynomial-time membership.

**Small entry tasks.**

- [S] Add reduction identity and transitivity lemmas with concrete composed time
  bounds.
- [x] Define 3CNF syntax as either a refinement or a predicate on the existing CNF
  (`Complexitylib.SAT.ThreeCNF`: `CNF.Is3CNF` predicate, decidable, with cons
  characterization and renaming-preservation).
- [x] Implement clause padding and prove equisatisfiability
  (`Complexitylib.SAT.ThreeCNF`: `Clause.padTo3`/`CNF.padTo3`, `padTo3_eval`,
  `padTo3_satisfiable_iff`, `is3CNF_padTo3` for width `1…3`; wide-clause Tseitin
  splitting still open).
- [x] Add graph adjacency-matrix encoding with decode/encode and size lemmas
  (`Complexitylib.Classes.FiniteCounting`: `card_adjMatrix` — `2^(n·n)` directed
  graphs on `n` vertices — and `adjMatrixEquivBitVec`, the row-major
  adjacency-matrix ↔ `n²`-bit-string bijection, encode/decode inverse by
  construction; compose with the existing `BitString`→`List Bool` bridge for the
  serialized form).

## Mid-term tracks

### M1. Circuit families, uniformity, and the TM--circuit bridge

**Goal.** Connect the existing finite circuit model to language classes and prove
machine/circuit characterizations with explicit uniformity.

**Headline theorem: `P = P-uniform SIZE(poly)`.** A language is in `P` iff it is
decided by a P-uniform polynomial-size circuit family. This is the central M1
payoff and factors into the two simulation directions:

- **Circuits → TMs (`P-uniform P/poly ⊆ P`).** A polynomial-time DTM, given `1^n`,
  runs the uniform generator to produce the length-`n` circuit code, then evaluates
  that code on the input with a memoized topological evaluator — all in polynomial
  time. *Decomposed:*
  - [ ] Poly-time DTM circuit-code evaluator: validate and memoized-evaluate a
    tagged family code paired with its input, with a polynomial running-time bound
    (the fan-in-two encoding, exact decoder, topological validator, and array-backed
    iterative evaluator already exist as pure functions — this is their DTM
    realization and timing).
  - [ ] Compose the uniform generator with the evaluator; prove the resulting DTM
    decides the family's language in polynomial time.
- **TMs → uniform circuits (`P ⊆ P-uniform P/poly`).** Unroll a `T(n)`-time DTM into
  a computation-tableau circuit of size `poly(T(n))` computing its output bit, and
  show the code map `1^n ↦ C_n` is itself computable in polynomial time (P-uniform).
  *Decomposed:*
  - [ ] Compile one deterministic transition step (configuration → next
    configuration, over the fixed-width tape window a step touches) into a Boolean
    circuit block; prove it computes `step`.
  - [ ] Tile the step block over a `T(n) × space(n)` tableau into a full circuit;
    prove semantic correctness (output bit = acceptance) and a `poly(T(n))` size
    bound.
  - [ ] Prove the tableau-circuit emitter runs in polynomial time (in `FP`), giving
    P-uniformity, and conclude `P ⊆ P-uniform P/poly`.

**Definitions to settle for the headline.** A `UniformPPoly` (P-uniform `P/poly`)
class: languages decided by a polynomial-size family whose code map `1^n ↦ (code of
C_n)` lies in `FP`. Keep it separate from the nonuniform `PPoly` already defined
(`UniformPPoly ⊆ PPoly` is immediate; the headline is `UniformPPoly = P`). The
Cook–Levin tableau infrastructure already in the library (`SAT` reduction emitters)
is related but is a CNF *satisfiability* encoding, not a deterministic
output-computing circuit — the functional unrolling needs its own construction and
correctness theorem (see hazards).

**Prerequisites.** The N1 list/`BitString` bridge, the existing typed
`Circuit.eval` semantics, and stable machine composition/time accounting from
N0. The proof-free circuit codec and polynomial-time DTM evaluator are M1
deliverables, not prerequisites.

**Current progress.** `BitString` now has a canonical `List.ofFn` serialization
with round trips. `CircuitFamily` handles positive lengths with ordinary typed
circuits and records the empty-input answer explicitly. The library also has
total family size/depth functions, pointwise bounds, a concrete polynomial-size
predicate, `SIZE`, and the nonuniform class `PPoly`, together with its big-O
power characterization. Fan-in-two circuits now have a canonical proof-free
terminated-unary encoding, exact decoder, topological validator, array-backed
iterative evaluator, semantic equivalence with `Circuit.eval`, and a concrete
polynomial bit-length bound.

**Settled conventions.**

- A circuit family has one Boolean output, a typed circuit `C_n` at each positive
  length, and an explicit bit at length zero.
- Size and depth have total pointwise bound predicates; polynomial size has both
  a concrete natural-polynomial definition and a `BigO` power characterization.
- `PPoly` is the nonuniform polynomial-size circuit class over `Basis.andOr2`.
  Its asymptotic meaning matches the literature, while exact `SIZE(s)` uses the
  library convention that excludes input vertices and makes negation flags free.

**Remaining convention.** **P-uniformity** will mean that a deterministic
polynomial-time generator maps unary `1^n` to a tagged family encoding: the tag
distinguishes the length-zero output bit from a positive-arity circuit code. This
is the accessible first theorem variant.

- Later, direct-connection or DLOGTIME uniformity for `NC`/`AC`. It should not be
  conflated with P-uniformity.

The existing `Circuit` type assumes nonzero input and output arities. The family
API resolves this deliberately: positive lengths use typed circuits, while the
unique empty input has an explicit `emptyOutput` bit. That convention must be
preserved by serialized encodings and uniform generators.

**Staged milestones.**

- [x] Define circuit-family semantics for `Language`, including conversion between
  lists of length `n` and `BitString n`.
- [x] Encode positive-arity circuits, reject malformed or non-topological codes,
  evaluate them iteratively, and prove agreement with typed circuit semantics
  plus a concrete encoding-length bound.
- [x] Add the tagged family wrapper and prove functional correctness at every
  length, including the explicit empty-input answer.
- [ ] Build a DTM that validates and evaluates a tagged family code paired with
  its input in polynomial time, including the explicit length-zero case.
- [ ] Prove the easy direction: a P-uniform polynomial-size family yields a
  polynomial-time DTM decider.
- [ ] Build a functional computation-tableau/unrolling construction from a
  time-bounded DTM to a bounded-fan-in circuit computing its output bit.
- [ ] Prove semantic correctness and a concrete polynomial size bound for the
  nonuniform unrolling construction.
- [ ] Define advice TMs and prove equivalence between polynomial advice and
  nonuniform polynomial-size circuits. This can proceed before the uniform
  emitter and unblocks M2.
- [ ] Implement the circuit emitter in `FP`, then prove `P` equals P-uniform
  polynomial-size circuit families.
- [x] Introduce `SIZE` and `PPoly` (`P/poly`) using the stable family conventions.
- [ ] Introduce `DEPTH`, `NC^i`, and `AC^i` after uniformity and zero-length
  conventions have been propagated through the existing `AC0` definition.

**Formalization hazards.**

- A Cook--Levin CNF expressing an accepting computation is not yet a circuit that
  computes the unique output of a deterministic run; the functional construction
  needs its own correctness theorem.
- The circuit generator's input length is `log n` if `n` is binary. Standard
  P-uniformity usually measures generator time polynomial in `n`, so encode `1^n`
  or state the convention explicitly.
- Circuit evaluation time depends on encoding validity, gate order, and fan-in.
- The evaluator consumes one machine input, so use the existing `pair code x`
  representation and account for its exact length rather than treating code and
  data as two implicit inputs.
- The current recursive typed evaluator can recompute shared subcircuits
  exponentially. Runtime theorems must use a validated topological encoding and
  a memoized/streaming evaluator instead of assuming `Circuit.eval` is linear.
- Dependent gate indices and proof-carrying acyclicity should not leak into every
  simulation lemma.
- Arora--Barak count input vertices and explicit NOT gates, unlike the library's
  exact size convention. Prove additive/linear simulations before transporting
  exact `SIZE` bounds or claiming basis invariance; polynomial-size `PPoly` is
  insensitive to those overheads.

**Small entry tasks.**

- [S] Package a well-formed raw circuit as a typed `Circuit` if a later proof
  needs the reverse bridge; the executable evaluator itself does not require it.
- [M] Implement a DTM realizing the topological memoized evaluator for serialized
  circuits and prove a polynomial running-time bound.
- [M] Define polynomial advice and basic monotonicity/containment lemmas.
- [L] Compile one fixed deterministic transition layer into a Boolean circuit as a
  local precursor to full unrolling.

### M2. BPP is contained in P/poly

**Goal.** Prove the classical nonuniform derandomization theorem
`BPP subset P/poly` using amplification and the probabilistic method.

**Prerequisites.** N2 amplification, M1 nonuniform circuit/advice equivalence, and
the PTM all-paths-halting discipline already present in the library.

**Target theorem variant.** Start with the library's concrete `BPP` definition and
the circuit-family definition of `P/poly`. The proof should not claim a uniform
derandomization. The fixed advice/random tape may depend on the input length but
not on the individual input.

**Staged milestones.**

- [ ] Normalize a BPP witness to explicit completeness at least `2/3` and
  soundness at most `1/3`, if the existing definition permits other constants.
- [ ] Construct repeated independent runs and majority output with error below
  `2^-(n+1)` on each input of length `n`.
- [ ] Prove by a union bound over all `2^n` inputs that some single random string is
  correct for every input of that length.
- [ ] Hardwire that string into the deterministic simulation/circuit for length
  `n`.
- [ ] Prove the resulting family has polynomial size and concludes
  `BPP subset P/poly`.
- [ ] Derive the advice-TM formulation as a corollary, or conversely use it as the
  main proof if the advice bridge is cleaner.

**Formalization hazards.** The amplified machine consumes a length-dependent
number of random bits, and early halting must not change the block layout. A strict
inequality below `1/2^n` is needed to conclude that the number of bad seeds is less
than the total number of seeds. Majority ties require an odd repetition count.
Hardwiring must preserve the exact acceptance bit, not merely the existence of an
accepting NTM path.

**Small entry tasks.**

- [S] Define the bad-seed set for a fixed input and rewrite its cardinality in terms
  of `acceptCount`.
- [S] Enumerate all `BitString n` inputs and prove its cardinality is `2^n`.
- [x] Prove the “expected bad inputs below one implies a perfect seed exists”
  counting lemma independently of machines
  (`Complexitylib.Classes.FiniteCounting.exists_good_seed`).
- [x] Prove block independence, in exact-counting form
  (`Complexitylib.Classes.FiniteCounting.card_filter_block`, via `blockEquiv`) and in
  probability form (`Complexitylib.Classes.EventProb.eventProb_block`): a
  prefix/suffix-separable event's probability is the product of the two block
  probabilities. The core for relating a repeated machine's acceptance to its single
  run (`k` independent runs multiply their success probabilities).
- [M] Define a PTM repetition wrapper with an explicit choice-block schedule (the
  `blockEquiv`/`card_filter_block` seed-splitting machinery is now in place).
- [M] Add a circuit/advice hardwiring operation and prove evaluation correctness.

### M3. Small-depth circuits and Barrington's theorem

**Goal.** Develop robust `NC^1` infrastructure and prove Barrington's width-5
branching-program characterization.

**Prerequisites.** M1 circuit families and depth, finite group/permutation support
from Mathlib, and basic formula/circuit compilation.

**Target theorem variants.** The first technically clean result should be the
finite theorem:

> A fan-in-two Boolean formula of depth `d` can be computed by a width-5
> permutation branching program of length at most `4^d`.

From this, depth `O(log n)` gives polynomial length. A full class equality also
needs the converse simulation of constant-width polynomial-length branching
programs by log-depth circuits and a clearly stated uniformity convention.

**Staged milestones.**

- [ ] Define Boolean formulas with literals, depth, evaluation, and compilation
  from a selected circuit output by recursively unfolding its DAG.
- [x] Define width-`w` permutation branching programs: instructions selected by
  one input bit, ordered product semantics, length, and acceptance convention.
  (`Circuits/BranchingProgram.lean`: `BPInstr`, `BP`, `eval`, `eval_append`,
  `eval_cons`, `eval_rename`.)
- [~] Specialize to permutations of `Fin 5` and prove the explicit conjugation and
  commutator identities used by Barrington's induction. (Abstract core done in
  `Circuits/Barrington.lean`: `BP.inverse`/`eval_inverse`, the representation
  predicate `BP.Computes`, and the closure lemmas `Computes_conj`,
  `Computes_not`, and `Computes_and` — the commutator trick `⁅σ, τ⁆` for the AND
  gate — hold at any width. The `S₅` input is now proven in
  `Circuits/BarringtonS5.lean`: `exists_fiveCycle_commutator` exhibits two
  `5`-cycles (`finRotate 5` and `(0 2 4 3 1)`) whose commutator is again a
  `5`-cycle — verified by kernel `decide` (0 axioms, no `native_decide`) — and
  `every_fiveCycle_is_commutator` upgrades this to *every* `5`-cycle via the
  single-conjugacy-class fact (`isConj_iff_cycleType_eq`) plus conjugation
  distributing over `⁅·,·⁆`. So the full `S₅` target-cycle freedom Barrington's
  induction consumes is proven. What remains is threading it through the
  formula→BP induction with the `4^d` length bookkeeping.)
- [x] Compile literals and negation, then the AND/OR induction, tracking target
  cycles and a length bound. (The abstract move-set is functionally complete in
  `Circuits/Barrington.lean`: base cases `Computes_false`, `Computes_true`,
  `Computes_var` (literals), negation `Computes_not`, AND `Computes_and`, OR
  `Computes_or` (De Morgan). `Circuits/BarringtonBridge.lean` joins these to the
  `S₅` algebra: `BP.Computes_retarget` re-aims a program to any target `5`-cycle,
  and `BP.Computes_and5` gives the `AND` gate with full target-cycle freedom. The
  full formula recursion is done in `Circuits/BarringtonRepr.lean`
  (`Computes_formula`). Length is now tracked in `Circuits/BarringtonLength.lean`:
  `Computes_formula_len` + `barrington_representation_len` give a program of length
  `≤ 13 ^ (size φ)`. The tighter textbook `4 ^ depth` constant is NOT yet
  attained — it needs a construction avoiding the retargeting overhead.)
- [~] State and prove the finite Barrington theorem. (Representation form
  **proven**: `Circuits/BarringtonRepr.lean` `barrington_representation` — every
  Boolean formula is computed by a width-`5` permutation branching program (some
  nonidentity `σ ∈ S₅` with program-value `= σ ↔ φ` true).
  `Circuits/BarringtonLength.lean` adds length bounds: `barrington_representation_len`
  (`≤ 13 ^ size`), `barrington_representation_depth` (`≤ 17 ^ depth`), and
  `barrington_poly_of_log_depth` — the **concrete `NC¹ ⟹` poly-size** statement: a
  formula of depth `≤ log₂ n` compiles to a width-`5` program of length `≤ n⁵` (via
  `17^{log₂ n} ≤ n⁵`). All 0 custom axioms. Remaining: the tight base `4 ^ depth`
  (vs `17 ^ depth`), and a *uniform family-level* class statement (`FormulaFamily`
  / poly-size-BP-family definitions) rather than the per-formula bound proved
  here.)
- [~] Lift it to nonuniform `NC^1`; then prove the converse by balanced composition
  of constant-size permutation transition matrices/functions. (Forward direction at
  the family level **done**: `Circuits/BarringtonFamily.lean`
  `FormulaFamily.logDepth_polyLength_bp` — a logarithmic-depth (`NC¹`) formula family
  is computed formula-by-formula by a family of width-`5` branching programs of
  polynomial length `C·(n+1)^p`, 0 custom axioms. The converse — poly-size width-`5`
  BPs give `NC¹` formulas by balanced composition — remains.)
- [ ] Add a uniform version only after instruction-generation uniformity is
  formalized.

**Formalization hazards.** Permutation multiplication order differs between texts
and libraries; fix it with executable examples before proving the induction.
Barrington's theorem is not true for arbitrary width-5 monoid programs without the
specific non-solvable group construction. The formula-to-program theorem and the
class-level circuit theorem are distinct, and sharing in a circuit must be handled
without an unjustified formula-size claim.

**Small entry tasks.**

- [x] Define branching-program evaluation and prove append/product semantics
  (`Complexitylib.Circuits.BranchingProgram`: `BPInstr`, `BP`, `BP.eval`,
  `BP.eval_append`, `BP.eval_cons`).
- [x] Encode a program instruction and prove evaluation is invariant under a
  semantics-preserving rename of input variables (`BPInstr.rename`, `BP.rename`,
  `BP.eval_rename` in `Complexitylib.Circuits.BranchingProgram`).
- [M] Search for and verify concrete `S_5` permutations with the required
  commutator identity, initially by `native_decide` if appropriate.
- [M] Implement literal and NOT programs with exact length bounds.
- [M] Prove balanced product evaluation has logarithmic circuit depth for fixed
  width.

### M4. Space complexity, alternation, and QBF

**Goal.** Supply the space and alternation results needed by oracle and interactive
proof tracks.

**Prerequisites.** N1 encodings, existing auxiliary-space semantics, and N3 QBF
syntax.

**Staged milestones.**

- [ ] Prove closure and normal-form lemmas for deterministic and nondeterministic
  space, including configuration counting.
- [ ] Formalize Savitch's theorem with an explicit recursive reachability machine:
  `NSPACE(S) subset DSPACE(S^2)` under suitable constructibility and lower-bound
  hypotheses.
- [ ] Derive `NPSPACE = PSPACE` in the library's polynomial-union convention.
- [ ] Define alternating machines or an equivalent bounded game semantics.
- [ ] Prove polynomial-time alternation equals PSPACE, or first prove a bounded
  configuration-game characterization.
- [ ] Prove TQBF is PSPACE-complete.
- [ ] Add deterministic and nondeterministic space hierarchy theorems with exact
  constructibility assumptions.

**Formalization hazards.** Space bounds do not automatically bound time unless
configurations are finite and repetitions are removed. The library's output tape
is excluded from space, so transducer restrictions matter. Savitch's recursion
needs careful termination and an encoded midpoint enumeration whose own workspace
is accounted for.

**Small entry tasks.**

- [S] Define bounded configurations and prove they form a finite type after tapes
  are truncated to the relevant cells.
- [M] Bound the number of bounded configurations in terms of state count, tape
  count, and space.
- [x] Define QBF evaluation and prove elementary substitution lemmas
  (`Complexitylib.SAT.QBF`: `QBF.eval`, `eval_ex_iff`, `eval_all_iff`).
- [M] Implement the recursive reachability predicate before implementing its TM.

### M5. Interactive-proof foundations

**Goal.** Define interactive protocols in a way that supports both finite
information-theoretic soundness proofs and polynomial-time complexity classes.

**Prerequisites.** N1 transcript codecs, N2 finite probability, and eventually M4
for the `IP = PSPACE` endpoint.

**Definitions to settle first.**

- A fixed-round protocol with bounded prover/verifier messages.
- An unbounded prover strategy as a function of the visible transcript.
- A verifier with private random bits and explicit work/time bounds.
- Completeness and soundness quantified over inputs and prover strategies.
- Public-coin protocols as a separate restriction, not the default semantics.

Start with fixed finite alphabets and rational probabilities. Only then package
families of protocols with polynomial bounds into `IP`, `AM`, and related classes.

**Staged milestones.**

- [ ] Define transcripts, legal interaction, deterministic prover strategies, and
  verifier acceptance counts.
- [ ] Prove strategy extensionality: only responses on reachable transcripts
  affect acceptance.
- [ ] Define completeness/soundness and prove monotonicity in thresholds.
- [ ] Formalize sequential repetition and one soundness-amplification theorem.
- [ ] Define polynomially bounded protocol families and `IP`.
- [ ] Prove elementary containments such as `NP subset IP` and
  `IP subset EXP` before attempting the sharp upper bound.

**Formalization hazards.** A prover is adaptive, so it cannot be represented by a
single witness string without encoding a potentially exponential strategy tree.
The verifier's private coins must not be exposed in the prover's transcript.
Message-length bounds are essential to keep the strategy space finite for counting
and exhaustive-search upper bounds.

**Small entry tasks.**

- [S] Define alternating transcript extension and prove prefix/round-index lemmas.
- [S] Define acceptance probability for a fixed prover and verifier random tape.
- [M] Embed an NP verifier as a one-message interactive protocol.
- [M] Prove that deterministic prover strategies suffice for maximizing acceptance
  in the finite classical model.

### M6. Random access machines and machine-model robustness

**Goal.** Relate the Turing-machine model to a Random Access Machine (RAM) — a
register machine with indirect addressing — so that the polynomial-time and
polynomial-space classes are provably model-independent, and so later
algorithm-design work has an honest cost model closer to real computation.

**Prerequisites.** The core Turing-machine model and its time/space predicates,
N0 run/time-accounting lemmas, and the multi-tape → single-tape simulation.

**Current progress.** The model is defined in
`Complexitylib.Models.RandomAccessMachine`: an instruction set with immediate,
`add`/`sub`/`mul`, indirect `load`/`store`, and jumps; an executable step and
fuel-bounded run; a **logarithmic-cost** time measure charging each instruction
the bit-length of the numbers it manipulates; a matching space measure; and the
classes `RAM.DTIME`, `RAM.DSPACE` over the shared `Language` interface. The
operational metatheory (run/cost additivity, stationarity after halt, monotonic
cost, step count `≤` log time, finite register support) is proved. The **cost
convention is justified by a theorem**, `RAM.logGap_squaring`: the squaring
program family runs in unit time `k + 1` but logarithmic time at least `2 ^ k`,
so a unit-cost measure would make the RAM super-polynomially stronger than a
Turing machine. This settles the model, its resource conventions, and its
soundness; the simulations below are the remaining work.

**Settled conventions.**

- Register file `ℕ → ℕ`, with input length in `R₀` and bits in `R₁ … Rₙ`, and
  the decision verdict read back from `R₀`.
- Time is logarithmic cost, never unit cost; the `+ 1` base cost makes every
  step cost `≥ 1`. Direct register indices are program constants and not charged;
  runtime (indirect) addresses are charged their bit-length.
- Space is the peak, over the run, of the bit-length needed to name and store
  every nonzero register; finiteness of register support keeps it well defined.

**Staged milestones.**

- [x] Define the instruction set, executable semantics, and logarithmic time
  and space measures with explicit input/output conventions.
- [x] Prove the run/cost algebra, halting stationarity, and finite support.
- [x] Prove the unit-vs-logarithmic gap theorem justifying logarithmic cost.
- [x] Define `RAM.DTIME`/`RAM.DSPACE` and prove monotonicity in the bound.
- [ ] Simulate a `T(n)`-time multi-tape Turing machine by a RAM in logarithmic
  time `O(T(n) · log T(n))`, giving `DTIME(T) ⊆ RAM.DTIME(T · log T)` and
  `P ⊆ RAM-P`.
- [ ] Simulate a `T(n)`-time logarithmic-cost RAM by a multi-tape Turing machine
  in time `O(T(n)²)`, giving `RAM.DTIME(T) ⊆ DTIME(T²)` and `RAM-P ⊆ P`.
- [ ] Conclude `RAM-P = P` and, with the space simulations, `RAM-PSPACE = PSPACE`.
- [ ] Add register-machine and Boolean-program variants and relate them by
  explicit simulations rather than as disconnected class definitions.

**Formalization hazards.** Textbook RAM simulations quietly assume unit cost;
the logarithmic cost of every register access must be charged and bounded before
a polynomial-time claim. The RAM → TM direction must store the register file on a
tape as address/value pairs and pay for search; the number of registers touched
and their bit-lengths are bounded by the log-time budget, and this bound must be
proved, not assumed. Output-length and address-length accounting must be explicit
so that the simulation's own workspace is charged.

**Small entry tasks.**

- [S] Add a `sub`/`mul` smart-constructor library and basic register-transfer
  Hoare lemmas for common gadgets (copy, conditional set, counter).
- [M] Encode a Turing-machine configuration in RAM registers with a decode
  function and prove one TM step is simulated by a fixed RAM program block.
- [M] Encode a RAM configuration on a Turing tape with size accounting and prove
  one RAM step is simulated within a polynomial number of TM steps.

## Long-term tracks

### L1. Sum-check and `IP = PSPACE`

**Goal.** Formalize the algebraic core of interactive proofs and the theorem
`IP = PSPACE` in a clearly delimited classical, private-coin model.

**Prerequisites.** M4 TQBF/PSPACE infrastructure, M5 interactive protocols, N2
soundness amplification, and substantial finite-field polynomial support.

**Staged milestones.**

- [ ] Develop the required finite-field and low-degree polynomial evaluation API,
  including an appropriate Schwartz--Zippel theorem.
- [ ] State and prove sum-check completeness and soundness for a fixed number of
  variables and explicit individual-degree bounds.
- [ ] Arithmetize Boolean formulas over a finite field.
- [ ] Formalize the degree-reduction step needed during quantified-formula
  evaluation; naive recursive arithmetization has degree blow-up.
- [ ] Build the interactive protocol for TQBF and prove polynomial verifier time,
  polynomial communication, perfect/high completeness, and bounded soundness.
- [ ] Conclude `PSPACE subset IP` from TQBF completeness.
- [ ] Prove `IP subset PSPACE` by evaluating the finite game/acceptance recursion in
  polynomial space.

**Formalization hazards.** “Arithmetize QBF and apply sum-check” omits the central
degree-control argument. Field size must dominate all relevant degree and
soundness parameters and must itself admit a polynomial-size encoding. Mathlib's
polynomial representation may not align directly with an executable verifier, so
an evaluation-oriented layer may be needed. The theorem's completeness and
soundness constants should be explicit before class-level amplification.

**Small entry tasks.**

- [x] Prove Boolean multilinear-extension identities for one variable
  (`Complexitylib.Circuits.MultilinearExtension`: `mle₁`, `mle₁_zero`, `mle₁_one`,
  `mle₁_bool`).
- [M] Prove a univariate root-count probability bound over a finite field.
- [M] Define the sum-check verifier state and prove round-by-round invariant
  preservation.
- [L] Formalize sum-check soundness independently of TQBF.

### L2. Oracle machines and relativization

**Goal.** Make relativized complexity a mathematical part of the library and
formalize oracle worlds showing why relativizing techniques cannot settle `P` vs
`NP`.

**Prerequisites.** N1 codecs, M4 space/configuration machinery, universal-machine
enumeration, and hierarchy-style diagonalization.

**Target theorem variants.** The meaningful formal endpoints are oracle existence
theorems, for example:

- there exists an oracle `A` with `P^A = NP^A`;
- there exists an oracle `B` with `P^B != NP^B`.

The informal assertion “a proof technique relativizes” is meta-mathematical and
should not be encoded as a theorem without first defining a proof system or a
precise closure property of arguments.

**Staged milestones.**

- [ ] Define oracle TMs with a query mechanism, query-cost convention, and
  deterministic/nondeterministic execution semantics.
- [ ] Define relativized time/space classes and lift basic simulations and
  containments that genuinely relativize.
- [ ] Build clocked enumerations of oracle machines suitable for diagonalization.
- [ ] Construct a separating oracle using a unary language whose membership asks
  whether some string of a chosen length belongs to the oracle.
- [ ] Construct an equality oracle, likely via a PSPACE-complete oracle together
  with the necessary closure theorem showing both relativized classes collapse to
  PSPACE.
- [ ] State the Baker--Gill--Solovay-style barrier corollary only after both worlds
  are formalized.

**Formalization hazards.** Query length and query-tape space must be charged
consistently. Oracle constructions are stagewise and self-referential: later
stages must not alter answers used to diagonalize earlier machines. An oracle for
a complete class does not yield a collapse without proving the relevant oracle
closure and simulation results.

**Small entry tasks.**

- [S] Define a single oracle-query step and prove deterministic execution remains
  functional.
- [M] Embed ordinary machines as oracle machines that never query.
- [M] Define the standard existential unary oracle language and prove it belongs to
  `NP^A` for every oracle `A`.
- [L] Adapt the existing diagonal-machine infrastructure to clocked oracle DTMs.

### L3. Natural proofs and pseudorandomness barriers

**Goal.** Formalize a precise Razborov--Rudich-style implication connecting useful
large constructive properties to distinguishers against pseudorandom function
families.

**Prerequisites.** M1 circuit families and `P/poly`, N2 finite probability, a
cryptographic game/security layer, and explicit truth-table encodings.

**Definitions to settle first.**

- A property of `n`-input Boolean functions, represented by their `2^n`-bit truth
  tables.
- Largeness as an explicit density lower bound among all Boolean functions.
- Constructivity measured in the truth-table length `N = 2^n`, not accidentally in
  `n`.
- Usefulness against a specified circuit-size family and quantifier convention
  (“for all sufficiently large lengths” versus infinitely many lengths).
- Pseudorandom function security against a specified nonuniform circuit class,
  query model, advantage, and parameterization.

**Staged milestones.**

- [ ] Define natural properties and prove basic monotonicity/transport lemmas.
- [ ] Formalize oracle distinguishers that receive a truth table, then relate them
  to the intended PRF game.
- [ ] Prove the finite core: a large property excluding all functions in a PRF
  range yields a distinguisher with explicit advantage.
- [ ] Add constructive evaluation and circuit-size bounds to obtain a parameterized
  conditional barrier theorem.
- [ ] State a classical corollary under a clearly named strong PRF assumption. Do
  not present the PRF assumption as a proved fact.

**Formalization hazards.** There are several inequivalent “natural proof”
definitions in the literature. The strength of the PRF assumption must match the
constructivity and usefulness parameters exactly. A truth-table algorithm running
in `poly(2^n)` is exponential in `n` but is still the standard constructive scale.
Uniform algorithms, nonuniform circuits, oracle access, and sampling access should
not be silently interchanged.

**Small entry tasks.**

- [x] Define truth tables and prove there are `2^(2^n)` Boolean functions on `n`
  bits (`Complexitylib.Classes.FiniteCounting.card_boolFunc`).
- [x] Define property density as an exact rational and prove complement/union
  identities (`Complexitylib.Classes.PropertyDensity`: `density`, `density_compl`,
  `density_union_le`).
- [M] Define usefulness against `SIZE(s)` at one length.
- [M] Prove the abstract range-vs-uniform-distribution distinguisher lemma with no
  circuit assumptions.
- [L] Define a nonuniform PRF security game compatible with the existing
  negligible-function API.

### L4. Further circuit lower bounds and structural complexity

**Goal.** Extend the current Shannon, gate-elimination, Schnorr, and Valiant results
toward the major unconditional circuit lower-bound toolkit.

**Prerequisites.** M1 family classes, N2 counting, and track-specific combinatorics.

**Candidate milestones, roughly increasing in difficulty.**

- [ ] Formula-size measures and balancing; prove a Spira-style balancing theorem.
- [ ] Decision trees, restrictions, and switching operations with semantic
  preservation.
- [ ] Håstad-style switching lemma and parity not in nonuniform `AC^0`.
- [ ] Monotone circuits and an accessible monotone lower bound before attempting
  clique.
- [ ] Threshold circuits and majority gates, initially for upper-bound
  constructions.
- [ ] Karchmer--Wigderson communication relations and formula-depth equivalence.
- [ ] Pseudorandom restrictions/generators only after the probabilistic and
  cryptographic infrastructure is mature.

**Formalization hazards.** Switching lemmas are probability-heavy and indexing
conventions vary. Asymptotic class separations require converting finite lower
bounds into statements about families. Monotone lower bounds do not transfer to
general circuits. Valiant's depth-reduction lemma is not by itself a general
circuit lower bound.

**Small entry tasks.**

- [x] Define restriction composition and prove evaluation commutes with applying a
  restriction (`Complexitylib.Circuits.Restriction`: `Restriction`, `applyTo`,
  `comp`, `applyTo_comp`, `BoolFormula.restrict`, `BoolFormula.eval_restrict`).
- [x] Define formula size/leaves separately from DAG circuit size
  (`Complexitylib.Circuits.Formula`: `BoolFormula`, `size`, `leaves`,
  `leaves_le_size`).
- [x] Prove decision-tree evaluation and depth lemmas
  (`Complexitylib.Circuits.DecisionTree`: `DecisionTree`, `eval`, `depth`,
  `numLeaves`, `numLeaves_le_two_pow_depth`).
- [M] Formalize random restrictions as a finite sample space.

### L5. Counting, polynomial hierarchy, and proof complexity

**Goal.** Add the structural classes and complete problems that connect circuits,
randomness, interaction, and lower bounds.

**Prerequisites.** M1 circuits, M4 alternation/QBF, N3 reductions, and N2 counting.

**Staged directions.**

- [ ] Define the polynomial hierarchy both by alternating quantifiers and oracle
  levels, then prove equivalence at fixed levels.
- [~] Define `#P`, `GapP`, and parsimonious reductions using exact accepting-path
  counts. *(`#P` = `SharpP` and `GapP` (with `GapP.neg_mem`) in
  `Complexitylib.Classes.SharpP` done; parsimonious reductions remain.)*
- [ ] Prove elementary closure properties and relate PP to GapP sign.
- [ ] Formalize `PH subset P^#P`/Toda-style results only after polynomial
  interpolation and modular counting are available.
- [ ] Define propositional proof systems, proof length, and Cook--Reckhow
  polynomial verification.
- [~] Connect resolution proofs to CNF and establish basic width/size facts before
  attempting lower bounds. *(`Complexitylib.SAT.Resolution`: `CNF.Entails`,
  `entails_of_mem`, `entails_resolvent`. The resolution proof system is now a
  first-class inductive relation `CNF.Derives` with `entails_of_derives`
  (soundness), `refutation_sound` (a derivation of the empty clause proves
  unsatisfiability), and `derives_cons` (weakening). `resolvent_length_le` gives
  the one-step width bound; fuller width/size measures over derivations remain.)*

**Formalization hazards.** Counting paths depends on a clock and on a canonical
number of nondeterministic choices; early halting must be padded consistently.
Oracle characterizations of PH depend on the exact query model. Proof-complexity
lower bounds need a clean distinction between semantic unsatisfiability and the
syntactic derivation system.

**Small entry tasks.**

- [S] Define a clocked accepting-path count and prove invariance after halted-path
  padding.
- [x] Define `#P` functions using the existing NTM path semantics
  (`Complexitylib.Classes.SharpP`: `SharpP` class, `NTM.acceptCount_le`,
  `SharpP.le_two_pow`).
- [x] Define quantified Boolean formulas with a bounded alternation counter
  (`Complexitylib.SAT.QBF`: `QBF`, `QBF.quantDepth`, `QBF.QuantifierFree`).
- [x] Define resolution clauses and verify soundness of one resolution step
  (`Complexitylib.SAT.Resolution`: `Clause.resolvent`, `Clause.resolvent_sound`).

### L6. Descriptive complexity

**Goal.** Develop the logic-vs-complexity correspondence (after Immerman and
Fagin): characterize complexity classes by the logics that define them, so that
lower bounds become expressibility questions. The `descriptive-complexity`
project was imported wholesale as `Complexitylib.DescriptiveComplexity`; this
track grows it toward the headline theorems.

**Foundations (imported, all 0 custom axioms).**

- [x] Vocabularies/signatures and finite structures over `Fin card`
  (`DescriptiveComplexity.Vocabulary`, `.Structure`: `Vocabulary`, `FinStruct`,
  built-in `≤`/successor/min/max, `DecFinStruct`).
- [x] Isomorphisms, embeddings, substructures; isomorphism is an equivalence and
  preserves cardinality (`.Isomorphism`: `Iso.refl`/`symm`/`trans`,
  `Iso.card_eq`, `Embedding`, `IsSubstructure`).
- [x] First-order syntax and semantics with de Bruijn environments; quantifier
  rank and formula size (`.FirstOrder.Syntax`, `.Semantics`, `.Env`).
- [x] Boolean queries and order-independence, closed under Boolean operations
  (`.Query`: `BooleanQuery`, `IsOrderIndependent`, complement/inter/union).
- [x] **FO sentences define order-independent queries** (Immerman Prop 1.16):
  `.FirstOrder.Isomorphism` `Sentence.orderIndependent`, via term/formula
  isomorphism-invariance (`Term.eval_iso`, `Formula.sat_iso`).
- [x] Worked examples: directed 3-cycles with an explicit isomorphism, a binary
  string with built-in order (`.Examples`).
- [x] First-order *definable* queries and the packaged crux
  (`.Definable`: `FODefinable`, `FODefinable.orderIndependent` — FO-definable ⟹
  order-independent — with Boolean closure `complement`/`inter`/`union`).

**Milestones (open).**

- [~] Second-order logic (`SO`, `∃SO`) syntax and semantics over finite
  structures, and its order-independence. *Decomposed:*
  - [x] `SOFormula` syntax: extend `Formula` with relation-variable application
    and second-order quantifiers (relation variables de Bruijn-indexed by a
    context of arities). (`SecondOrder/Syntax.lean`: `SOFormula`, `SOSentence`,
    the FO embedding `SOFormula.ofFormula`, and `SOFormula.size`.)
  - [x] SO semantics: satisfaction under a relation-variable assignment (in
    addition to the element `Env`). (`SecondOrder/Semantics.lean`: `REnv`/`rCons`/
    `emptyREnv`, `SOFormula.Sat`, `SOSentence.Models`, and the truth-preserving FO
    embedding `SOFormula.ofFormula_sat` / `SOSentence.models_ofFormula`.)
  - [x] SO isomorphism-invariance ⟹ SO-definable queries are order-independent
    (`SecondOrder/Isomorphism.lean`: `REnv.map`/`rCons_map`, `SOFormula.sat_iso`,
    `SOSentence.models_iso`, `SODefinable`, `SODefinable.orderIndependent`).
  - [x] Mark the `∃SO` fragment (second-order existentials only, over an FO
    matrix) — the exact fragment Fagin characterizes. (`SecondOrder/Syntax.lean`:
    `SOFormula.IsFOMatrix`, `IsExistSO`, and `ofFormula_isFOMatrix`/`_isExistSO`
    placing `FO ⊆ ∃SO`.)
- [~] Encode `FinStruct` as a bit-string language (ordered structures ↔ inputs)
  to connect `BooleanQuery` to the machine-model `Language`. *Decomposed:*
  - [x] Truth-table encoding of a single relation over `Fin card` tuples, with its
    length `card ^ arity` (`Encoding.lean`: `encodeRel`, `encodeRel_length`).
  - [x] Relational part of a structure's encoding (concatenate the truth tables)
    and its total length (`encodeRels`, `encodeRels_length`).
  - [~] Full encoding: prepend `card` (and any constants) and make it computable;
    a decode/encode round-trip on ordered structures. (`Encoding.lean`: computable
    tuple enumeration `allTuples` (length `card^k`, `mem_allTuples`), computable
    relation/structure encodings `encodeRelC`/`encodeRelsC`, and the full
    `encodeStruct` (unary `card` prefix + relations) with cardinality recovery
    `encodeStruct_card` are done; encoding the constants and a full structure
    round-trip remain.)
  - [x] The induced language `⟦Q⟧ : Language` of a query (`Language.lean`:
    `queryLanguage` — the encodings of `Q`-satisfying structures — and
    `mem_queryLanguage`). This is the bridge to the machine-model `Language`.
- [ ] **Fagin's theorem** `NP = ∃SO`: the descriptive-complexity headline —
  existential second-order logic captures `NP`. *Decomposed:*
  - [~] `∃SO ⊆ NP`: given an `∃SO` sentence, an NTM that guesses the witnessing
    relations and FO-model-checks the matrix in polynomial time. (The FO
    model-checking half is done: `ModelChecking.lean` `Formula.evalB` /
    `Sentence.evalB` are computable and proven correct (`evalB_eq_sat` /
    `evalB_eq_models`). The guess-the-relations NTM and its poly-time bound remain.)
  - [ ] `NP ⊆ ∃SO`: express "there is an accepting polynomial-time computation"
    as an `∃SO` sentence (guess the computation-tableau relation; FO-check the
    local transition constraints).
- [ ] `FO ⊆ AC⁰` (and the converse for a suitable uniform `AC⁰`), linking this
  track to the circuit tracks (M3/L4).
- [ ] Immerman–Vardi (`FO(LFP) = P` on ordered structures) after adding least
  fixed-point operators.

**Formalization hazards.** The structure↔bit-string encoding must fix an
ordering convention (Proviso 1.14) consistently; order-independence is what makes
a query "logical", so the encoding and the invariance results must be kept in
sync. Fagin's theorem's `∃SO ⊆ NP` direction needs a model-checking machine; the
converse needs to express an accepting computation as an `∃SO` formula.

### L7. Analysis of Boolean functions

**Goal.** Develop the Fourier analysis of Boolean functions (after Ryan O'Donnell)
as the analytic foundation for small-depth-circuit lower bounds (L4) and the
natural-proofs barrier (L3). The subtheory lives in `Complexitylib.BooleanAnalysis`
(`FourierExpansion` surface, `FourierExpansion.Defs`/`.Internal`), all 0 custom
axioms.

**Foundations (done).**

- [x] The ±1 cube `Cube n = Fin n → ZMod 2`, `BooleanFunction n = Cube n → ℝ` as a
  real inner-product space; the parity basis `χ S` and its orthonormality
  (`Defs`: `chi`, `parityFun`, `expect`, `inner`; `expect_parityFun`).
- [x] Fourier coefficients/weights, the expansion `f = ∑_S 𝓕(f,S)·χ_S`, Plancherel
  and Parseval, and mean/variance/convolution (`fourier_expansion`, `parseval`,
  `parseval_boolean`, `variance_boolean`, `fourierCoeff_convolution`).
- [x] Fourier linearity and the degree decomposition: `fourierCoeff_add`/`_smul`/
  `_sub`/`_neg`, `degreePart`, `norm_sq_degreePart`, spectral samples.
- [x] The BLR linearity test: `isLinear_iff_isMultiplicative`, `blrAcceptProb_eq`,
  `blr_soundness`, `local_correctability`.

**Chapter 2 — noise and average sensitivity (done).**

- [x] Noise stability/sensitivity and the bilinear form, with monotonicity and the
  Fourier-weight formula (`noiseStability`, `noiseStabilityBilin`,
  `noiseSensitivity`, `noiseStability_eq_sum_weight`, `noiseSensitivity_le_influence`).
- [x] The noise operator `T_ρ` with its Fourier formula `𝓕(T_ρ f, S) = ρ^|S|·𝓕(f,S)`,
  the endpoints `T_1 = id` and `T_0 f = 𝔼[f]·1`, and the (self-adjoint) operator forms
  `Stabᵨ[f] = ⟪f, T_ρ f⟫` and `Stabᵨ[f,g] = ⟪f, T_ρ g⟫` (`noiseOp`,
  `fourierCoeff_noiseOp`, `noiseOp_one`, `noiseOp_zero`, `noiseStability_eq_inner`,
  `noiseStabilityBilin_eq_inner`).
- [x] Total influence (= average sensitivity) and coordinate influence, with
  `totalInfluence_eq_sum_influence`, the Poincaré inequality
  `variance_le_totalInfluence`, and the parity checks
  `totalInfluence_parityFun`/`influence_parityFun`.
- [x] The discrete derivative `Dᵢ` and `Infᵢ[f] = ‖Dᵢ f‖²`
  (`derivative`, `fourierCoeff_derivative`, `influence_eq_norm_sq_derivative`).
- [x] The coordinate flip as a measure-preserving involution, the sensitivity
  operator `Lᵢ f = (f − f∘flipᵢ)/2` with `Infᵢ[f] = ‖Lᵢ f‖²`, and the probabilistic
  reading `Infᵢ[f] = Pr_x[f(x) ≠ f(x⊕eᵢ)]`, capped by `I[f] = 𝔼ₓ[#pivotal
  coordinates]` (`flipEquiv`, `expect_flipCoord`, `fourierCoeff_comp_flipCoord`,
  `sensitivityOp`, `fourierCoeff_sensitivityOp`,
  `influence_boolean_eq_expect_sensitive`, `totalInfluence_boolean_eq_expect_sensitive`).

**Milestones (open), roughly increasing in difficulty.**

- [~] The level-1 inequality and the FKN theorem (functions with almost all weight
  at level 1 are close to a dictator). *The elementary level-1 bounds are done:
  `𝓕(f,{i})² ≤ Infᵢ[f]`, `W¹[f] ≤ I[f]`, and the coordinate form
  `∑_i 𝓕(f,{i})² ≤ I[f]`, with the tight identity `∑_i 𝓕(f,{i})² = W¹[f]`
  (`fourierCoeff_singleton_sq_le_influence`,
  `fourierWeightAtDegree_one_le_totalInfluence`,
  `sum_fourierCoeff_singleton_sq_le_totalInfluence`,
  `sum_fourierCoeff_singleton_sq_eq_fourierWeightAtDegree_one`). The sharp
  `O(𝔼[f]²log(1/𝔼[f]))` level-1 inequality and FKN need hypercontractivity.*
- [ ] Monotone functions: `Infᵢ[f] = 𝓕(f,{i})` and the Margulis–Russo formula
  (needs a coordinate partial order on the cube in the ±1 convention).
- [~] Hypercontractivity (the `(2,4)`-norm bound) and its Fourier corollary — the
  gateway lemma for the remaining results. *The Bonami base case is done
  (`two_point_hypercontractive`: `𝔼[(T_{1/√3}(a+bx))⁴] ≤ (a²+b²)²` on one bit); the
  L^p-norm API and the coordinate-tensorization induction remain.*
- [ ] The KKL theorem (some coordinate has influence `Ω(log n / n)`).
- [ ] Friedgut's junta theorem (bounded total influence ⟹ close to a junta).
- [ ] The `AC⁰` Fourier concentration bound (Linial–Mansour–Nisan), linking this
  track to the switching-lemma work in L4.

**Formalization hazards.** The ±1 encoding flips the coordinate order (`χ(0)=+1`,
`χ(1)=−1`), so a monotonicity convention must be fixed explicitly. Hypercontractivity
is analytically heavy; prove the finite two-point inequality first and induct on
coordinates rather than importing continuous machinery. Influence has two distinct
operators — the spectral derivative `Dᵢ` (strips `i` from each frequency) and the
sensitivity operator `Lᵢ` (keeps frequencies containing `i`) — with the same squared
norm; keep them separate to avoid off-by-a-coordinate errors.

## Cross-cutting project ideas

These projects can proceed alongside the dependency-ordered tracks when they reuse
stable interfaces rather than introduce competing ones.

- **Concrete algorithms and languages:** regular languages, graph reachability,
  arithmetic languages, and bounded automata simulations provide excellent tests
  for class definitions and machine combinators.
- **Constructibility library:** close standard facts for polynomial, exponential,
  logarithmic, and composed time/space bounds.
- **Machine-model robustness:** multi-track tapes, RAM-like models, Boolean
  programs, and register machines should be related by explicit simulations rather
  than added as disconnected class definitions.
- **Communication complexity:** deterministic and randomized protocols, rectangle
  bounds, and discrepancy would support Karchmer--Wigderson and circuit lower
  bounds.
- **Cryptographic foundations:** ensembles, indistinguishability, one-way
  functions, hard-core predicates, PRGs, and PRFs can build on `Negligible` and the
  finite probability toolkit.
- **PCP and hardness of approximation:** this is a very long-term direction. Begin
  with constraint systems, gap-preserving reductions, and verifier randomness/query
  accounting; do not start from the PCP theorem statement.
- **Parameterized and fine-grained complexity:** reductions with explicit
  parameter maps and exact running times fit the library well once encoding costs
  are standardized.

## How to choose a contribution

1. Pick the earliest track containing the concept you need.
2. Check whether its prerequisites already have stable public definitions.
3. Prefer one unchecked “small entry task” or one milestone sub-lemma.
4. Write the intended public theorem statement before building proof internals.
5. Record the concrete resource bound, representation convention, and malformed
   input behavior in the module documentation.
6. Add the module to the appropriate import surface only when its API is ready.
7. Run `lake build --wfail` and the standalone single-tape validation target;
   require no errors or warnings.

For large theorem projects, a good first pull request contains definitions,
executable examples, and structural lemmas only. A second establishes the finite or
fixed-parameter theorem. The final pull request should lift that result to the
asymptotic complexity-class statement. This sequencing keeps ambitious work
reviewable and makes partial progress useful to the rest of the library.
