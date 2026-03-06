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

- `Possible` — the `Possible` typeclass and instances
- `TuringMachine` — multi-tape Turing machine definitions
- `Models` — the models aggregation layer
- `project` — project-level configuration

### Examples

```
feat(TuringMachine): add multi-tape monadic Turing machine

Define MultiTapeTM parameterized over a monad M with Possible typeclass,
along with step relation, reachability, and output predicates.
```

```
refactor(Possible): add universe polymorphism to Possible class
```

```
build(project): bump Mathlib to v4.28.0
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
lake build
```

Ensure the project builds cleanly with no warnings before submitting changes.
