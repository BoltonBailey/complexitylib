# N0 — Higher-level machine authoring

**Status:** active experiment. The first local routine/lowering slice is
implemented; rose-tree data lowering remains open. No external dependency has
been adopted.

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

## Adoption decision

Do not add CSLib as a dependency for the first vertical slice. Use a small local
routine IR inspired by its builder and first-order-fragment ideas.

| Question | Finding | Consequence |
| --- | --- | --- |
| License | Both projects use Apache-2.0. | No licensing blocker. |
| Toolchain | The audited branch pins Lean 4.32.0-rc1 and a later Mathlib commit; this project pins Lean/Mathlib 4.30. | A dependency would force an unsupported version boundary. The core RTM sources happen to elaborate under 4.30 today, but that is not an upstream compatibility contract. |
| Build coverage | RTM is not imported by upstream `Cslib.lean` or `CslibTests.lean`. | The default upstream build and tests do not guard this branch's RTM stack. |
| Proof completeness | The builder, loop-resource, arithmetic, and TM-simulator files contain admitted declarations. | Importing the useful stack fails this project's `--wfail` and axiom policies. |
| Lowering direction | No `InPlace → TM` compiler or refinement theorem exists. The current simulator interprets a single-tape TM *in RTM*. | Direct reuse does not supply the compiler needed here. |
| Resource notion | RTM semantics records an abstract value cost; `TM.HoareSpace` bounds work heads and charged input-tail travel in every reachable configuration, while output safety is a separate transducer obligation. | A lowering must separately prove representation overhead and the concrete auxiliary-space and output-discipline contracts. |
| Tape interface | RTM values do not distinguish read-only input, named work tapes, or append-only output. | The middle layer needs explicit tape roles and preservation effects. |

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

The certificate should next be tested on a second loop or serializer phase.
Only then should more of the repeated setup/packaging be moved into the shared
interface.

## RTM-shaped follow-up

The local control-flow slice is not enough to validate rose-tree data. The next
decisive benchmark is the upstream-style `reverse (var 0)` program:

1. define a well-scoped, Data-valued local `InPlace` core;
2. encode `Data` as balanced Boolean parentheses on named work tapes;
3. lower `empty`, `cons`, `elim`, immediate `let`, and `while` through the
   routine layer;
4. prove functional refinement for list reversal;
5. prove concrete time overhead, all-reachable auxiliary space, and complete
   input/work/output frames.

`tail (var 0)` is an acceptable representation warm-up, but it does not test
the loop compiler. Arithmetic `forLoop` and the universal simulator are not
first-slice candidates because their upstream resource proofs are unfinished.

## Evaluation gates

Do not promote the experimental layer to a general public authoring language
until it passes at least two independent constructions and all of these gates:

- executable definitional lowering to `TM`;
- semantic refinement stated independently of the compiler implementation;
- finite controller state with no admitted declarations;
- exact or explicit concrete time overhead;
- every-reachable-configuration space preservation;
- named-tape and append-only-output frame preservation;
- a measured reduction in consumer proof plumbing;
- no loss of the existing warning, linter, and axiom gates.

If the rose-tree slice does not meet these gates cleanly, retain only the local
routine/certificate layer and treat CSLib RTM as design inspiration rather than
an integration target.
