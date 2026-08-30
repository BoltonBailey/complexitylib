/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Complexitylib.Metacomplexity.Kolmogorov.Oracle.Defs
public import Complexitylib.Encoding.BinaryNat
public import Complexitylib.Encoding.Pairing

/-!
# Random-access conditional Kolmogorov complexity -- definitions

This layer fixes an explicit convention for `C(x | y)`: an oracle machine gets
Boolean random access to the finite condition `y`. Queries are canonical pairs
of a one-bit tag and a minimal binary index. Tag `false` reads a data bit; tag
`true` asks whether the index is in bounds. The second query form makes the
condition length observable and prevents strings differing only by trailing
zeroes from defining the same oracle.

Every oracle lookup costs one `OracleTM` step. Constructing and positioning a
query on the query tape costs ordinary local steps.
-/


@[expose] public section

namespace Complexity

namespace RandomAccessCondition

/-- Canonical query for one condition bit. -/
def bitQuery (index : ℕ) : List Bool :=
  pair [false] (BinaryNatCode.encode index)

/-- Canonical query asking whether `index` is below the condition length. -/
def inBoundsQuery (index : ℕ) : List Bool :=
  pair [true] (BinaryNatCode.encode index)

/-- Faithful Boolean random-access oracle for one finite condition string.
Malformed query pairs, non-singleton tags, noncanonical indices, and
out-of-range bit queries all return `false`. -/
def oracle (condition : List Bool) : BooleanOracle :=
  fun query =>
    match unpair? query with
    | some ([tag], indexBits) =>
        match BinaryNatCode.decode? indexBits with
        | some index =>
            if tag then decide (index < condition.length)
            else (condition[index]?).getD false
        | none => false
    | _ => false

end RandomAccessCondition

namespace OracleTM

variable {n : ℕ}

/-- Plain machine-relative conditional complexity when the finite condition is
available through `RandomAccessCondition.oracle`. -/
noncomputable def randomAccessConditionalPlainKolmogorovComplexity
    (machine : OracleTM n) (output condition : List Bool) : WithTop ℕ :=
  machine.plainKolmogorovComplexity
    (RandomAccessCondition.oracle condition) output

/-- Whole-output time-bounded conditional complexity under the explicit
random-access condition convention. -/
noncomputable def randomAccessConditionalTimeBoundedKolmogorovComplexity
    (machine : OracleTM n) (output condition : List Bool)
    (time : ℕ) : WithTop ℕ :=
  machine.timeBoundedKolmogorovComplexity
    (RandomAccessCondition.oracle condition) output time

end OracleTM

end Complexity
