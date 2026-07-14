# N0 — Higher-level machine authoring

**Status:** external evaluation and the first cross-construction mechanics
audit are complete. Canonical NTM trace splitting/invariant rules and the
existing binary-loop space contract now remove duplicated proof plumbing;
stable phase-boundary routing is the next small contract candidate. Rose-tree
frontend/lowering is deferred and optional. No external dependency has been
adopted.

This note records the evaluation of CREI's experimental rose-tree machine
(RTM) as a possible source language for `Complexitylib` machines. The concrete
`Complexity.TM` remains the executable semantic target and the source of truth
for tape frames and complexity bounds.

## Evaluated upstream snapshot

The audit used CREI CSLib's `rtm` branch at commit
`834c364a8bf529b824a120c9d692173fb5354104` (2026-06-24). The relevant source
is under `Cslib/Computability/Machines/RTM/`.

The upstream design has several ideas worth preserving:

- `Data` is a single rose-tree representation with an encoded size equal to
  its balanced-parenthesis length.
- `Prog` gives a small functional syntax with variables, construction,
  elimination, equality, immediate application, and `while`.
- `PB` hides absolute de Bruijn-level bookkeeping behind a higher-order builder.
- `InPlace` identifies a first-order fragment in which closures are consumed
  immediately and cannot escape.
- the big-step semantics records functional results and abstract time/space
  costs, and the library already proves many functional builder laws.

These are strong source-language and proof-interface ideas. They are not yet a
verified lowering into this library's machine model.

## Adoption and prioritization decision

The first vertical slice did not add CSLib as a dependency. It used a small
local routine IR inspired by the builder and first-order-fragment ideas.

| Question | Finding | Consequence |
| --- | --- | --- |
| License | Both projects use Apache-2.0. | No licensing blocker. |
| Toolchain | The audited branch pins Lean 4.32.0-rc1 and a later Mathlib commit; this project pins Lean/Mathlib 4.30. | A dependency would force an unsupported version boundary. The core RTM sources happen to elaborate under 4.30 today, but that is not an upstream compatibility contract. |
| Build coverage | RTM is not imported by upstream `Cslib.lean` or `CslibTests.lean`. | The default upstream build and tests do not guard this branch's RTM stack. |
| Proof completeness | The builder, loop-resource, arithmetic, and TM-simulator files contain admitted declarations. | Importing the useful stack fails this project's `--wfail` and axiom policies. |
| Lowering direction | No `InPlace → TM` compiler or refinement theorem exists. The current simulator interprets a single-tape TM *in RTM*. | Direct reuse does not supply the compiler needed here. |
| Resource notion | RTM semantics records an abstract value cost; `TM.HoareSpace` bounds work heads and charged input-tail travel in every reachable configuration, while output safety is a separate transducer obligation. | A lowering must separately prove representation overhead and the concrete auxiliary-space and output-discipline contracts. |
| Tape interface | RTM values do not distinguish read-only input, named work tapes, or append-only output. | The middle layer needs explicit tape roles and preservation effects. |

The current priority is therefore the middle layer: proof-level contracts that
make named tape roles, preservation frames, output-accumulator endpoints, and
time bounds compose around concrete machine combinators while leaving other
resource dimensions explicit. The existing experimental `Routine` layer could
be expanded to consume that interface, or a rose-tree source language could sit
above it later. Building either syntax first would front-load compiler and
representation proofs before the shared composition boundary is stable.

Selective copying of the current `PB` stack is also premature: it would copy
unfinished proofs without addressing the missing concrete lowering. Revisit a
dependency or source port only after upstream exposes a warning-free public RTM
target and a compiler boundary compatible with our resource semantics.

## First local vertical slice

The implemented first slice deliberately targets the pain observed in the
binary input-length counter:

1. Define a tiny first-order `Experimental.Routine` syntax with atomic machine calls,
   sequential composition, and input-driven iteration.
2. Lower it definitionally through the existing `seqTM` and `forInputTM`
   combinators, so execution remains the ordinary concrete `TM` execution.
3. Add an indexed input-loop certificate carrying:
   - exact scanner, body, return, and terminal transitions;
   - a ghost iteration value and exact per-iteration time;
   - explicit scan/body/done configuration families;
   - all-reachable body-prefix and driver space bounds.
4. Express binary length as `forInput (call binarySuccTM)` and recover the
   existing exact endpoint, complete frame, time bound, logarithmic
   all-reachable space, and transducer results through the generic rule.

This is intentionally smaller than a direct compiler for `Prog`. It tests the
middle-layer contract first: whether higher-level control flow can remove run
stitching and prefix-space boilerplate without hiding the concrete resource
obligations.

### Baseline

Before extraction, `BinaryLength/Internal.lean` has 588 lines. Its machine
definition is already one combinator expression; most of the cost is proof
plumbing:

- exact scanner/body/return run stitching;
- classifying every reachable prefix into driver, body, or remaining-loop time;
- transporting a child space contract through a controller state;
- endpoint and frame packaging.

### Measured outcome

The explicitly experimental `Experimental.binaryLengthRoutine` expression now is
`forInput (call binarySuccTM)`, with definitional lowering to the concrete
machine. The generic certificate owns the exact loop induction and the
every-prefix driver/body/tail time split. The consumer supplies the successor
semantics, concrete configuration families, frame facts, and local space
inequality.

`BinaryLength/Internal.lean` decreased from 588 to 519 lines: 69 lines, or
about 12%, while preserving its public theorem statements and warning-free
build. Across Lean sources, however, this first slice is net +306 lines because
the generic certificate implementation and routine API are new. A second
consumer must amortize that shared cost. This is a useful first data point, not
yet a promotion result:

- the new generic layer has only one proven consumer;
- atomic calls still carry concrete `TM`s rather than typed named-tape effects;
- rose-tree representation and semantic refinement are not represented;
- fresh-start setup and final Hoare packaging remain partly bespoke.

The loop certificate itself still has only one loop consumer. It should not be
generalized further until another loop or serializer needs the same indexed
all-prefix argument.

## Second local benchmark: named-tape emitter effects

The next experiment packages the endpoint effect shared by short emitter
pipelines without changing their concrete machines. `TM.Experimental.EmitSpec`
names a fixed parked input, the work-tape family before and after a machine, the
output accumulator before and after it, and an upper time bound. Its sequencing
rule owns the real one-step `seqTM` phase boundary and the parked-tape seam.

Two existing Tseitin pipelines now use the contract:

- `emitClauseTM` keeps the input and work family fixed while evolving the
  output accumulator through four heterogeneous stages;
- `rollWideBuffersTM` changes the six-register work family through five
  heterogeneous stages while preserving the output accumulator.

Both concrete machine definitions and both theorem statements are unchanged.
Against the pre-experiment tree, the clause theorem decreased from 39 to 33
lines and the rotation theorem from 48 to 36 lines. `BufferSpecs.lean`
decreased from 584 to 567 lines including its new import. The shared contract
module is 86 lines, so this slice is still net +69 Lean lines. It demonstrates
local reuse and clearer phase composition, not global amortization or two
independent roadmap constructions.

The contract is intentionally narrower than a full effect system and is
indexed by concrete `TM`s, not by `Routine` syntax. This records the key result
of the benchmark: the present reduction comes from packaging endpoint/frame
facts, not from a higher-level authoring language. It also does not assert exact
running time, all-reachable space, append-only extension, or structural
transducer safety. Those properties must remain explicit until a future
contract carries and proves them. Before adding effects to the routine syntax
or generating controller phases, test this proof-level vocabulary in a separate
construction where it removes material plumbing.

## Cross-construction proof-mechanics audit

The dependency-ordered N0 audit compared four proof shapes rather than
starting from a proposed language:

- UTM straight-line composition (`PairSelf`, `ClockConstructible`, and
  `ClockedUtm`);
- fixed-schedule NTM repetition and rewind;
- the serialized circuit evaluator and Tseitin controller;
- the direct-unrolling binary serializer and its nested count-up loops.

The audit found two distinct kinds of repetition. Stable `seqTM` boundaries
repeatedly prove that input/work/output transition maps are identities before
transporting an endpoint predicate. The UTM `PairSelf` proof is the clearest
case: five ordinary stable seams are surrounded by one genuinely special
left-marker bounce that must remain explicit. This motivates one small
read-stable boundary-routing lemma as the next experiment, not a generated
controller language. A separate evaluator/Tseitin pattern existentially
packages bounded intermediate runs; a transparent bounded-reachability wrapper
may help there, but exact-cost theorems should continue to expose
`reachesIn` directly.

The first promoted result addresses finite NTM traces. The public
`NTM.trace_snoc` rule splits off the final choice with `Fin.last`/`castSucc`,
and `NTM.trace_invariant` owns all dependent prefix reindexing for an indexed
one-step invariant. The latter replaced parallel hand-written inductions in
the independent `GuessBounded`, `PairSplit`, and `PairBuild` subroutines plus
SAT verifier/counter preservation proofs. The former also simplified final-step
stitching in repetition and four SAT guess-and-verify phase exits.

The serializer audit found a different issue: the complete tableau loop had
locally reconstructed the already-public
`SpaceBoundByWidthAt.binaryFor_of_clamped_body` theorem. Reusing that contract
deleted two one-off wrappers and reduced `Tableau/Internal.lean` by 108 net
lines while preserving the same pointwise polynomial envelope and logarithmic
space theorem.

Before documentation, this audit's Lean diff adds 240 lines and deletes 305,
for a net reduction of 65 lines. More importantly, the
remaining bespoke obligations are now classified: special left-marker bounces,
branch meaning, underpowered child frames, and construction-specific arithmetic
stay visible. The audit rejects a combined mega-contract carrying soundness,
domains, emitted semantics, space, frames, and routing; it would obscure those
honest distinctions. `Routine`, evaluator-local `TapeAction`, and the
serializer-local effect/space pairing therefore remain experimental or local
until independent consumers justify promotion.

## Optional rose-tree revisit

The upstream-style `reverse (var 0)` program remains a useful frontend
benchmark, but it is not scheduled work. Revisit it only when:

1. named-tape/effect contracts have reduced plumbing in independent constructions;
2. a concrete roadmap construction needs recursive Data-valued syntax rather
   than ordinary concrete named-tape machines; and
3. a bounded slice can include executable lowering, semantic refinement,
   finite controller state, explicit time, all-reachable space, and complete
   tape frames.

Until those triggers fire, retain the RTM audit and its builder/first-order
ideas as design history rather than expanding the dependency or representation
surface. If revisited, `reverse (var 0)` remains preferable to a trivial
destructor because it exercises construction, elimination, and iteration.

## Evaluation gates

Do not move the proof-level endpoint contract into the stable API until it:

- removes material plumbing in a construction independent of the two Tseitin
  pipelines;
- states every carried endpoint and resource dimension precisely, without
  implying append-only output, exact runtime, space, or transducer safety;
- remains complementary to the uniform-list `bigSeqTM_hoareTime` rule rather
  than duplicating it;
- demonstrates enough reuse to justify its shared implementation cost; and
- preserves the existing warning, linter, and axiom gates.

Do not promote `Routine` or any future frontend to a general public authoring
language until it passes at least two independent constructions and these
additional compiler gates:

- executable definitional lowering to `TM`;
- semantic refinement stated independently of the compiler implementation;
- finite controller state with no admitted declarations;
- exact or explicit concrete time overhead;
- every-reachable-configuration space preservation;
- named-tape and append-only-output frame preservation;
- a measured reduction in consumer proof plumbing.
