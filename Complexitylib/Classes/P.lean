import Complexitylib.Classes.P.Defs
import Complexitylib.Classes.P.Internal

/-!
# P — surface layer

This file aggregates the definitions and theorems for DTIME and P.

## Definitions (from `P/Defs.lean`)

- `DTIME` — deterministic time complexity class (AB Definition 1.6)
- `P` — polynomial time: `⋃ k, DTIME(n^k)`
- `FP` — functions computable in polynomial time

## Theorems (from `P/Internal.lean`)

- `DTIME_union` — DTIME is closed under union (AB Claim 1.5)
-/
