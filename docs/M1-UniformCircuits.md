# M1 — Uniform circuits and the machine bridge

Status: the family foundation, proof-free codec, serialized-circuit evaluator
Turing machine, `UniformPPoly_subset_P`, and deterministic direct-unrolling
family are implemented. The remaining headline direction is
`P_subset_UniformPPoly`: its append-only direct-unrolling serializer must still
be proved to lie in `FL`. The canonical binary count-up loop supplies one reusable
serializer substrate, and its first consumer now emits a prepared binary value as
terminated-unary `NatCode` with restored scratch and frame. Fixed-polynomial binary
arithmetic, loading successive values, and the serializer itself remain open.
Experimental rose-tree lowering is deferred and is not on this dependency path.

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

Arora and Barak's main uniformity definition uses a logspace-computable map from
unary `1^n` to the description of `C_n`. Complexitylib follows that convention:
`CircuitFamily.Uniform F` requires the tagged code map on unary lengths to lie in
`FL`, and `UniformPPoly` uses that logspace-uniform family predicate. The weaker
explicit-output polynomial-time notion usually called P-uniformity may be added
separately, but it is not the definition used by the M1 headline. Direct-connection
or DLOGTIME uniformity for finer circuit classes also remains a separate layer.

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

## Completed machine-evaluator milestone

The deterministic evaluator consumes the single input `pair code x`, using the
existing pairing codec and split machine. Its length is exactly
`2 * code.length + 2 + x.length`, and the implemented end-to-end bound is stated
in that combined length. After total outer-pair validation and staging, the
three-work-tape controller streams the tagged code, memoizes input and gate
values, and rejects every malformed count, reference, tag, and trailing suffix.
`evalFamilyTM_hoareTime` proves agreement with `evalFamilyPair?` on every raw
input, `evalFamilyTM_decidesInTime` decides `circuitEvalLanguage`, and
`evalFamilyTime_bigO_quadratic` proves the complete budget is quadratic.

The family generator consumes unary `List.replicate n true`, including the
tagged empty-input answer at `n = 0`. Its required class is `FL`, not merely
`FP`. The proved containment `FL_subset_FP` lets the completed
`UniformPPoly_subset_P` direction run that generator in polynomial time before
invoking the evaluator. Unary input is essential: a binary encoding of `n` would
measure the generator against a much shorter input and impose a stronger
uniformity condition.

## Route to the characterization

1. **Complete:** on input `x`, compute `1^|x|`, run the `FL` family generator,
   pair its tagged code with `x`, and invoke the validated evaluator. Together
   with `FL_subset_FP`, this proves `UniformPPoly_subset_P`.
2. **Complete:** compile the totalized deterministic transition into raw ordered
   gate fragments and unroll it for the polynomial time horizon.
3. **Complete:** prove exact deterministic semantics and a concrete polynomial
   size bound. `TM.unrollingCircuitFamily` yields `P_subset_PPoly` nonuniformly.
4. **Complete:** define `TM.directUnrollingCircuitFamily` directly from the raw
   tableau gates and prove its tagged encoding is exactly
   `TM.directUnrollingCode`, avoiding typed prefix hardwiring in the generator.
5. **Open:** implement an append-only machine that emits
   `TM.directUnrollingCode` from unary `1^n`, prove that function lies in `FL`,
   and package `P_subset_UniformPPoly` and `UniformPPoly = P`.

The current binary count-up layer is a substrate for step 5, not its completion.
`CircuitCode.Machine.emitNatCodeTM` now demonstrates the intended serialization
boundary: given a distinct zero scratch counter and a preserved canonical binary
value, it appends exactly `NatCode.encode value`, restores the complete input/work
frame so the scratch can be reused, and never moves output left. Its explicit
time bound is `emitNatCodeTime value`; its all-prefix auxiliary-space budget is
`initialSpace + 2 * value.size + 5`, so the unary output length is not disguised
as work space. The caller must still load or change the preserved value between
emissions. Fixed-polynomial evaluation and remaining binary indexing arithmetic
are also needed before the raw-tableau serializer can be instantiated. This route
uses the concrete `TM` and its proof-level contracts directly; the deferred
rose-tree lowering is optional and not a prerequisite.

The advice equivalence no longer waits on this route:
`PAdvice_subset_PPoly`, `PPoly_subset_PAdvice`, and `PAdvice_eq_PPoly` are proved,
and `BPP_subset_PAdvice` follows through the completed `BPP_subset_PPoly` theorem.
Direct-connection or DLOGTIME uniformity for `NC` and `AC` remains a separate
later layer.
