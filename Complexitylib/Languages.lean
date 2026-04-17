import Complexitylib.Languages.Trivial
import Complexitylib.Languages.FirstCell
import Complexitylib.Languages.LengthParity
import Complexitylib.Languages.AnBn

/-!
# Concrete languages and their complexity — aggregation

Each file under `Complexitylib.Languages` defines a family of concrete
languages together with complexity-class memberships. They serve as
non-emptiness witnesses for the classes in `Complexitylib.Classes` and as
worked examples of building TMs from reusable building blocks.

## Submodules

- `Trivial`      — `∅` and `Set.univ`, decided in `O(1)` by `writeTM`.
- `FirstCell`    — languages determined by the first input bit:
                   `{[]}`, `firstBitOne`, `firstBitZero`, `nonempty`, and
                   their Boolean combinations.
- `LengthParity` — `evenLength`, `oddLength` — the first genuinely linear-time
                   examples, proved by induction on the input.
- `AnBn`         — `{0ⁿ 1ⁿ : n ≥ 0}` — the first non-regular example,
                   decided in linear time by a push-down TM that uses its
                   work tape as a unary counter.
-/
