# Contributing to Complexitylib

## Commit Format

Each commit message should follow this structure:

```
<type>(<scope>): <short summary>

<optional body>
```

### Types

- **feat**: A new definition, theorem, or structure
- **fix**: A bug fix or correction to an existing proof/definition
- **refactor**: Restructuring code without changing behavior (e.g. renaming, reorganizing modules)
- **style**: Formatting, whitespace, universe annotations, namespace organization
- **docs**: Documentation changes (README, comments, docstrings)
- **build**: Changes to lakefile.toml, lean-toolchain, CI configuration
- **chore**: Maintenance tasks (updating dependencies, cleaning up imports)

### Scope

The scope should identify the area of the library affected, typically a module path:

- `TuringMachine` — multi-tape Turing machine definitions
- `SAT` — verifier, tableau, and reduction developments
- `Circuits` — Boolean circuit definitions and lower bounds
- `Classes` — complexity classes and containments
- `Models` — the models aggregation layer
- `project` — project-level configuration

### Examples

```
feat(TuringMachine): add timed reachability endpoint lemma

Expose a reusable endpoint-uniqueness theorem for deterministic bounded runs
and replace private copies in the universal-machine proofs.
```

```
refactor(SAT): centralize initialized-tape helpers
```

```
build(project): bump Mathlib to v4.30.0
```

### Guidelines

- Keep the summary line under 72 characters.
- Use imperative mood ("add", "fix", "remove", not "added", "fixes", "removed").
- The body is optional but encouraged for non-trivial changes. Explain *why*, not *what*.
- Reference related issues or discussions if applicable.

## Code Style

- Follow Mathlib conventions for naming: `camelCase` for definitions, `PascalCase` for types and Prop-valued definitions.
- Use universe polymorphism where appropriate.
- Keep `open` declarations scoped to sections or namespaces rather than at module level.
- Use `variable` inside `section` blocks to organize implicit parameters.
- Avoid unused variable warnings — use `_` for genuinely unused binders.
- Prefer Mathlib's existing types and lemmas over custom ones.

## Building

```bash
lake build --wfail
lake build --wfail Complexitylib.Models.TuringMachine.SingleTape.Validation
lake build --wfail Complexitylib.Circuits.Encoding.Validation
```

Ensure all three commands build cleanly before submitting changes. The first
checks the complete library and treats warnings (including proof placeholders)
as failures. The latter two run executable `#guard` regression suites for the
single-tape simulator and encoded-circuit evaluator; both are intentionally
outside the public import graph.

## Choosing a Contribution

See [ROADMAP.md](ROADMAP.md) for dependency-ordered research programs and
smaller entry tasks. A contribution does not need to prove a headline theorem:
well-placed definitions, reusable finite-combinatorics lemmas, API cleanup,
executable examples, and documented intermediate results are all valuable when
they make a later milestone easier to state and prove.

Before starting a larger track, identify the public theorem statement, the
minimal prerequisite API, and a sequence of independently buildable,
`sorry`-free steps. Keep definitions and public statements auditable; isolate
long implementation proofs in `Internal` modules where appropriate.
