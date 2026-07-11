import Complexitylib.Models.TuringMachine
import Complexitylib.Asymptotics
import Mathlib.Data.Nat.Bits

namespace Complexity

/-!
# Time-constructible functions

A function `T : ℕ → ℕ` is **time-constructible** if `T(n) ≥ n` and the
mapping `x ↦ T(|x|)` can be computed by a deterministic TM in `O(T(n))`
time (AB Definition 1.12). The output is the binary encoding of `T(|x|)`
via `Nat.bits` (LSB-first).

Time-constructibility is the standard assumption on time bounds used in the
time hierarchy theorem and other separation results. Most "natural" time
bounds (polynomials with `T(n) ≥ n`, exponentials, `n log n`, etc.) are
time-constructible.

## Main definitions

- `TimeConstructible` — a function `T : ℕ → ℕ` is time-constructible

## Main results

- `TimeConstructible.linear_le` — `T(n) ≥ n`
- `TimeConstructible.pos` — `T(n) > 0` when `n > 0`
- `TimeConstructible.mono_id` — `id ≤ T` (pointwise)
- `TimeConstructible.computable` — extract the witnessing TM and time bound
-/

open Complexity

/-- A function `T : ℕ → ℕ` is **time-constructible** (AB Definition 1.12) if
    `T(n) ≥ n` for all `n`, and the mapping `x ↦ T(|x|)` (encoded in binary
    via `Nat.bits`) can be computed by a deterministic TM in `O(T(n))` time. -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.ComputesInTime (fun x => Nat.bits (T x.length)) f ∧ f =O T

namespace TimeConstructible

/-- A time-constructible function satisfies `n ≤ T(n)`. -/
theorem linear_le {T : ℕ → ℕ} (hT : TimeConstructible T) : ∀ n, n ≤ T n :=
  hT.1

/-- A time-constructible function is positive on positive inputs. -/
theorem pos {T : ℕ → ℕ} (hT : TimeConstructible T) {n : ℕ} (hn : 0 < n) :
    0 < T n :=
  Nat.lt_of_lt_of_le hn (hT.linear_le n)

/-- A time-constructible function dominates the identity pointwise. -/
theorem mono_id {T : ℕ → ℕ} (hT : TimeConstructible T) : ∀ n, id n ≤ T n :=
  hT.linear_le

/-- A time-constructible function is computable in `O(T)` time. -/
theorem computable {T : ℕ → ℕ} (hT : TimeConstructible T) :
    ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
      tm.ComputesInTime (fun x => Nat.bits (T x.length)) f ∧ f =O T :=
  hT.2

end TimeConstructible

end Complexity
