/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Incompressibility.Defs
public import Complexitylib.Metacomplexity.Kolmogorov.Incompressibility.Internal

/-!
# Finite incompressibility

At most `2^(k+1)-1` fixed-length strings can have deterministic
machine-relative time-bounded Kolmogorov complexity at most `k`. Consequently,
at least `2^n - (2^(k+1)-1)` of the `n`-bit strings exceed `k`, and one such
string exists whenever `k < n`.
-/


public section

namespace Complexity

namespace ShortProgram

/-- Packaging a bounded list as a short program and forgetting the certificate
recovers the original list. -/
@[simp] theorem toList_ofList (bound : ℕ) (program : List Bool)
    (hlength : program.length ≤ bound) :
    (ofList bound program hlength).toList = program :=
  toList_ofList_internal bound program hlength

/-- The variable-length contents uniquely determine a short program. -/
theorem toList_injective {bound : ℕ} :
    Function.Injective (toList : ShortProgram bound → List Bool) :=
  toList_injective_internal

/-- There are exactly `2^(k+1)-1` binary programs of length at most `k`. -/
theorem card (bound : ℕ) :
    Fintype.card (ShortProgram bound) = 2 ^ (bound + 1) - 1 :=
  card_internal bound

end ShortProgram

namespace TM

variable {tapes : ℕ}

/-- Membership in the compressible-string set is exactly the bounded
Kolmogorov-complexity inequality. -/
theorem mem_timeBoundedCompressibleStrings_iff (machine : TM tapes)
    (outputLength time bound : ℕ) (output : Fin outputLength → Bool) :
    output ∈ machine.timeBoundedCompressibleStrings outputLength time bound ↔
      machine.timeBoundedKolmogorovComplexity (List.ofFn output) time ≤
        (bound : WithTop ℕ) :=
  mem_timeBoundedCompressibleStrings_iff_internal
    machine outputLength time bound output

/-- Membership in the incompressible-string set is exactly strict complexity
above the bound. -/
theorem mem_timeBoundedIncompressibleStrings_iff (machine : TM tapes)
    (outputLength time bound : ℕ) (output : Fin outputLength → Bool) :
    output ∈ machine.timeBoundedIncompressibleStrings outputLength time bound ↔
      (bound : WithTop ℕ) <
        machine.timeBoundedKolmogorovComplexity (List.ofFn output) time :=
  mem_timeBoundedIncompressibleStrings_iff_internal
    machine outputLength time bound output

/-- No deterministic machine has more low-complexity outputs than short
programs. The bound is independent of the output length and clock. -/
theorem card_timeBoundedCompressibleStrings_le (machine : TM tapes)
    (outputLength time bound : ℕ) :
    (machine.timeBoundedCompressibleStrings outputLength time bound).card ≤
      2 ^ (bound + 1) - 1 :=
  card_timeBoundedCompressibleStrings_le_internal
    machine outputLength time bound

/-- Quantitative finite incompressibility: all but at most `2^(k+1)-1` of the
`n`-bit strings have time-bounded complexity greater than `k`. -/
theorem card_timeBoundedIncompressibleStrings_ge (machine : TM tapes)
    (outputLength time bound : ℕ) :
    2 ^ outputLength - (2 ^ (bound + 1) - 1) ≤
      (machine.timeBoundedIncompressibleStrings outputLength time bound).card :=
  card_timeBoundedIncompressibleStrings_ge_internal
    machine outputLength time bound

/-- Under the uniform distribution on `n`-bit strings, the probability of
time-`t` complexity at most `k` is at most `(2^(k+1)-1) / 2^n`. -/
theorem eventProb_timeBoundedCompressibleStrings_le (machine : TM tapes)
    (outputLength time bound : ℕ) :
    eventProb (machine.timeBoundedCompressibleStrings outputLength time bound) ≤
      ((2 ^ (bound + 1) - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength :=
  eventProb_timeBoundedCompressibleStrings_le_internal
    machine outputLength time bound

/-- Uniform fixed-length strings are quantitatively dense above every
time-bounded complexity threshold. -/
theorem eventProb_timeBoundedIncompressibleStrings_ge (machine : TM tapes)
    (outputLength time bound : ℕ) :
    1 - ((2 ^ (bound + 1) - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      eventProb
        (machine.timeBoundedIncompressibleStrings outputLength time bound) :=
  eventProb_timeBoundedIncompressibleStrings_ge_internal
    machine outputLength time bound

/-- For every clock and every `k < n`, some `n`-bit string has time-bounded
complexity strictly greater than `k`. -/
theorem exists_timeBoundedKolmogorovComplexity_gt
    (machine : TM tapes) (outputLength time bound : ℕ)
    (hbound : bound < outputLength) :
    ∃ output : Fin outputLength → Bool,
      (bound : WithTop ℕ) <
        machine.timeBoundedKolmogorovComplexity (List.ofFn output) time :=
  exists_timeBoundedKolmogorovComplexity_gt_internal
    machine outputLength time bound hbound

end TM

end Complexity
