import Complexitylib.Languages.Trivial
import Complexitylib.Languages.FirstCell
import Complexitylib.Languages.LengthParity
import Complexitylib.Languages.AnBn
import Complexitylib.Languages.ZeroPrefix
import Complexitylib.Languages.Balanced
import Complexitylib.Languages.AllSymbol
import Complexitylib.Languages.Contains
import Complexitylib.Languages.LengthDivBy
import Complexitylib.Languages.LastBit
import Complexitylib.Languages.Palindromes

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
- `ZeroPrefix`   — `{0ⁿ 1ᵐ : n ≥ m}` — an `AnBn` variant that accepts
                   strings with at least as many leading zeros as trailing
                   ones, decided by the same push-down construction.
- `Balanced`     — strings with equal numbers of `false`s and `true`s —
                   generalizes `anbn` to arbitrary interleavings, decided
                   in linear time by a push-down TM whose control state
                   records the sign of the count difference.
- `AllSymbol`    — `allZeros`, `allOnes` — strings consisting entirely of
                   a single bit, decided by the `scannerTM` combinator.
- `Contains`     — `containsZero`, `containsOne` — strings containing at
                   least one copy of a given bit, also decided via
                   `scannerTM`.
- `LengthDivBy`  — `lengthDivBy k` — strings whose length is divisible
                   by `k`, with `ZMod k` counter as the scan state.
- `LastBit`      — `lastBitOne`, `lastBitZero` — strings whose final bit
                   equals a target, with `Option Bool` scan state.
- `Palindromes`  — strings equal to their reverse, decided in linear time
                   by a 1-work-tape TM that copies the input then compares
                   forward against backward.
-/
