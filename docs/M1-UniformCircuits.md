# M1 — Uniform circuits and the machine bridge

Status: the nonuniform family foundation and a canonical serialized-circuit
evaluator are implemented. The evaluator Turing machine and both directions of
the uniform characterization remain open.

This note fixes the intended construction boundary for M1. The public family
API lives in `Complexitylib.Circuits.Family`; `SIZE` and `PPoly` live in
`Complexitylib.Classes.PPoly`. The encoding modules connect those mathematical
objects to a proof-free bit-string format suitable for Turing machines.

## Established conventions

- `BitString n` serializes in increasing index order via `List.ofFn`.
- A `CircuitFamily` stores one typed, single-output circuit for every positive
  input length and an explicit answer for the unique empty input.
- `CircuitFamily.size 0 = 0`; the empty-input bit is a finite exception.
- The library's circuit size includes internal and output gates but excludes
  primary input vertices.
- `PPoly` currently uses the fan-in-two AND/OR basis with free per-gate-input
  negation flags. Basis invariance is a later simulation theorem, not a
  definitional identification.
- Polynomial size means a pointwise bound by a polynomial over `ℕ`. The public
  API proves this equivalent to an eventual big-O power bound.

## Literature alignment and convention gaps

Arora and Barak define circuit families as one `n`-input, single-output DAG per
length and define `P/poly` by polynomial-size families. Their size convention
counts every vertex, including input vertices, and their base model has explicit
NOT gates. Complexitylib instead counts only internal and output gates and gives
each gate input a free negation flag. These conventions yield the same
polynomial-size class after additive/linear simulations, but they do not define
the same exact `SIZE(s)` class. Until those simulations are formalized, exact
size bounds and lower bounds must retain their stated basis and convention.
The model also requires a genuine counted AND/OR output gate, so even a
projection or negated projection has size one rather than zero. This is another
constant exact-size difference, not a `P/poly` difference.

Arora and Barak's main uniformity definition uses an implicitly
logspace-computable map from unary `1^n` to the description of `C_n`. As a first
variant, Complexitylib will use the common weaker notion usually called
P-uniformity: an explicit-output polynomial-time generator on `1^n`. This choice
still characterizes `P` for polynomial-size families, but it must not be
conflated with logspace or direct-connection uniformity for finer circuit
classes.

References:

- [Arora–Barak, Chapter 6](https://theory.cs.princeton.edu/complexity/book.pdf)
  for Boolean circuits, `SIZE`, `P/poly`, unary logspace uniformity, and advice.
- [UCSD CSE 200 Boolean-circuit notes](https://cseweb.ucsd.edu/classes/wi20/cse200-a/notes/6-boolean%20circuits.pdf)
  for the explicit-output P-uniform definition and its characterization of `P`.
- [Cornell CS 6810 circuit notes](https://www.cs.cornell.edu/courses/cs6810/2026sp/lec10.pdf)
  for the topological evaluation and bit-encoding viewpoint.

## Why the serialized evaluator is separate

`Circuit` is an excellent proof object: `Fin` indices and its `acyclic` field
make malformed wiring unrepresentable. It is not the right parser output or
runtime representation for a Turing machine. In particular,
`Circuit.wireValue` follows the DAG recursively and may evaluate a shared
predecessor more than once. A chain in which each gate reads its predecessor
twice already gives an exponential recursion tree.

The machine-facing evaluator must instead validate a topological gate list and
append each computed value to a memo table. Correctness should relate this
iterative semantics to `Circuit.eval`; no polynomial-time claim should be made
about the recursive definition itself.

The library already contains a useful internal semantic bridge. `GateSlot` and
`CircDesc` describe fixed-size fan-in-two circuits, `circuitToDesc` puts a typed
circuit's output gate last, and `circuit_eval_eq_evalD` proves semantic
preservation. These are proof intermediaries, not suitable on-tape syntax:
`CircDesc` contains `Fin` indices and fixed-size functions, and its evaluator
totalizes forward references to `false`. The new list format serializes the same
ordered gate data and its iterative evaluator is proved to agree with `evalD`
on validated topological descriptors. This reuses the established typed-circuit
bridge while keeping proof fields off the tape.

## Implemented proof-free format

Start with `Basis.andOr2`, whose gates have exactly two inputs. A raw gate has:

- an AND/OR operation bit;
- two negation bits; and
- two absolute natural-number wire references.

For input arity `N`, raw gate `i` is valid exactly when both references are less
than `N + i`. The final listed gate is the circuit output. A nonempty list is
therefore required at positive arity. Absolute references make the validator,
evaluator, and later generator substantially simpler than a dependent syntax.

The family-level format is tagged so length zero is total and unambiguous:

```text
encodeAt F 0       = [false, F.emptyOutput]
encodeAt F (n + 1) = true :: encodeCircuit (F.circuit (n + 1))
```

The evaluator requires the zero tag exactly when the supplied data input is
empty and the positive tag otherwise. Malformed tags, a zero tag with the wrong
payload length, and invalid circuit codes reject. `evalFamilyCode_encodeAt`
proves correctness at every fixed length, while
`evalFamilyCode_encodeAt_length` gives the list-native form
`evalFamilyCode (F.encodeAt input.length) input = some (F.evalList input)` for
machine-facing clients.

Positive circuit codes do not separately serialize their input arity;
`evalFamilyCode` parameterizes a decoded circuit by the supplied input's length.
Thus the tag distinguishes the empty case from positive arities, but it is not an
arity-mismatch certificate between two positive lengths. The canonical theorem
evaluates `encodeAt F input.length`, which is exactly the interface needed by a
uniform generator and evaluator. Any future API promising independent arity
mismatch detection must add an arity field to the format.

The implemented format uses terminated unary, `n ↦ 1^n 0`, for natural-number
fields. A gate is encoded as three fixed bits (operation and two negation flags)
followed by its two terminated-unary absolute references. A circuit begins with
its terminated-unary gate count and then contains exactly that many gates. The
count makes exact decoding reject trailing garbage without a separate end token.

Unary references make an `s`-gate circuit encoding polynomial in `N + s`; the
proved bound is
`1 + s * (2 * (N + s) + 6)`. Binary references can be added later if a tighter
encoding is useful. This deliberately gives a coarser bound than
`O(s log(N+s))` in the library's variables, or `O(S log S)` when `S` counts all
nodes and hence `S ≥ N`; no near-optimal encoding-length claim is intended.

Module layout:

```text
Complexitylib/Circuits/Encoding/Defs.lean
Complexitylib/Circuits/Encoding/Internal/Codec.lean
Complexitylib/Circuits/Encoding/Internal/Semantics.lean
Complexitylib/Circuits/Encoding/Internal.lean
Complexitylib/Circuits/Encoding.lean
Complexitylib/Circuits/Encoding/Family.lean
Complexitylib/Circuits/Encoding/Validation.lean
```

The definitions layer contains raw syntax, serialization, parsing,
well-formedness, and an array-backed iterative `eval?` that rejects malformed
references. The internal layer proves codec soundness, relates the executable
well-formedness checks to the propositions, and establishes typed-circuit
semantics. The surface module exposes stable theorem statements. Reuse
`Complexitylib.Circuits.Internal.CircDesc` and the focused
`Complexitylib.Circuits.Internal.CircuitToDesc` bridge behind the internal layer;
do not expose those proof-oriented descriptors as the public wire format.
`Validation.lean` stays outside the public import graph and supplies small
executable guards for round trips, truncation, trailing garbage, bad references, arity
checks, family tags, negated edges, and shared DAG nodes; the universal theorems
remain the correctness argument.

## Completed functional acceptance criterion

The first end-to-end result is semantic preservation for every typed fan-in-two
circuit:

```lean
theorem AONCircuitCode.evalCode_encodeCircuit
    {N G : ℕ} [NeZero N]
    (c : Circuit Basis.andOr2 N 1 G) (x : BitString N) :
    evalCode N (encodeCircuit c) x.toList = some ((c.eval x) 0)
```

The same milestone proves exact decoder soundness, success iff topological
well-formedness, and the concrete polynomial encoding-length bound. This pins
down gate order, output convention, malformed-input behavior, and the
`List Bool`/`BitString` bridge before any Turing-machine implementation depends
on them.

## Machine-evaluator milestone

The deterministic evaluator consumes the single input `pair code x`, using the
existing pairing codec and split machine. Its length is exactly
`2 * code.length + 2 + x.length`, so all time bounds should be stated in that
combined length. After splitting, the evaluator should stream the validated
code, keep `x ++ previously computed gate values` on a work tape, reject an
out-of-range reference, and append one result per gate. A coarse quadratic or
cubic bound is sufficient. Reuse the parsing, unary lookup, tape rewinding, and
sequential-composition patterns from the SAT verifier and machine-combinator
modules.

The machine theorem should state both functional correctness and an explicit
time bound. Only then define P-uniformity by requiring an `FP` generator to
produce `encodeAt F n` from unary `List.replicate n true`, including the tagged
empty-input answer at `n = 0`. Unary input is essential: polynomial time in a
binary encoding of `n` would impose a much stronger uniformity condition.

## Route to the characterization

1. On input `x`, run the unary family generator on `1^|x|`, pair its tagged code
   with `x`, and invoke the validated evaluator. This proves that a P-uniform
   polynomial-size family decides a language in `P`.
2. For the converse, totalize a time-bounded deterministic transition so halted
   configurations remain fixed.
3. Compile one transition layer to a raw ordered gate list.
4. Unroll the layer for the polynomial time bound and select the final output
   bit.
5. Prove semantic correctness and a concrete polynomial size bound.
6. Implement the circuit-list emitter as an `FP` machine, establishing
   P-uniformity rather than merely nonuniform existence.

Advice machines need not wait for the uniform emitter. Once validated evaluation
and the nonuniform unrolling/size theorem are available, prove the standard
advice equivalence with `PPoly` in parallel; this unblocks BPP-in-P/poly. The
harder `FP` emitter is needed for the full P-uniform characterization.
Direct-connection or DLOGTIME uniformity for `NC` and `AC` should remain a
separate later layer.
