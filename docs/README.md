# Complexitylib design notes

These documents explain the construction strategy behind several of the
library's largest verified machines. They complement the public theorem
statements; they are not the source of truth for current proof status.

| Document | Subject | Current status |
| --- | --- | --- |
| [N0 — Higher-level machine authoring](N0-MachineAuthoring.md) | CREI RTM evaluation, local routine lowering, and proof-engineering gates | RTM audit complete; TM-indexed endpoint/effect experiment active; rose-tree lowering deferred |
| [A3 — Guess-and-Verify NTM](A3-GuessVerifyNTM.md) | SAT witness generation, pairing, and verifier composition | SAT-specialized route implemented; generic construction remains open |
| [A4 — Single-Tape Simulation](A4-SingleTapeSimulation.md) | Quadratic multi-tape-to-single-tape simulation | Implemented and covered by executable regression guards |
| [A5 — Reduction Emitter](A5-ReductionEmitter.md) | Polynomial-time construction of Cook–Levin formulas | Implemented; SAT NP-completeness is proved |
| [Universal Turing Machine](UTM-design.md) | Description encoding, interpretation, fixed UTM, and clocking | Implemented through universal simulation and hierarchy support |
| [M1 — Uniform Circuits](M1-UniformCircuits.md) | Circuit serialization, validated evaluation, and the TM/circuit bridge | Evaluator TM, direct unrolling, and `UniformPPoly_subset_P` implemented; `FL` serializer for the reverse direction remains open |

For future work, see the repository-level [roadmap](../ROADMAP.md). When a
design plan is completed, preserve it if it still explains the construction,
but add a prominent status note and links to the final modules.
