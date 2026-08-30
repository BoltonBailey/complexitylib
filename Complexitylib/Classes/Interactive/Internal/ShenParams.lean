/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenState
public import Complexitylib.Classes.Interactive.Internal.PrimeSearch

/-!
# The parameters of the concrete verifier

⚠️ Unreviewed by Bolton

From the input `x = ⌜(qs, φ)⌝` — a quantifier prefix and a CNF matrix — the verifier derives,
in polynomial time: the encoded schedule `codesE` and its length `nU`, the uniform degree bound
`DU = litCount φ + 2`, the size `NU = 6 n D + 1` from which the prime `p ∈ (N, 2N]` is found, the
modulus string `qStr` of width `w = N + 1`, the number of variables `mU`, and the initial point
and claim `pt0`, `cl0`. Every function comes with its value on a well-formed input.

## Main definitions

- `qsE`, `φE`, `codesE`, `nU`, `litU`, `DU`, `NU`, `qStr`, `mU`, `pt0`, `cl0`

## Main results

- the `*_eq` lemmas — values on `⌜(qs, φ)⌝`
- `qStr_spec` — the modulus is a prime in `(N, 2 N]`, below `2 ^ w`
- the `*_mem_FP` lemmas
-/

@[expose] public section

namespace Complexity

open Cobham OpChain Shen

/-- The input format: a prefix and a CNF matrix. -/
abbrev Instance := Prefix × List (List CLit)

/-! ## Reading the input -/

/-- The encoded prefix. -/
noncomputable def qsE (x : List Bool) : List Bool := fstEnc x
/-- The encoded matrix. -/
noncomputable def φE (x : List Bool) : List Bool := sndEnc x

theorem qsE_mem_FP : qsE ∈ FP := fstEnc_mem_FP (CobhamFP_subset_FP (Cobham.proj 0))
theorem φE_mem_FP : φE ∈ FP := sndEnc_mem_FP (CobhamFP_subset_FP (Cobham.proj 0))

theorem qsE_eq (I : Instance) :
    qsE (DataEncode.bitstringEncode I) = DataEncode.bitstringEncode I.1 := by
  rcases I with ⟨qs, φ⟩
  exact fstEnc_eq qs φ

theorem φE_eq (I : Instance) :
    φE (DataEncode.bitstringEncode I) = DataEncode.bitstringEncode I.2 := by
  rcases I with ⟨qs, φ⟩
  exact sndEnc_eq qs φ

/-- The encoded schedule. -/
noncomputable def codesE (x : List Bool) : List Bool := shenCodesEnc (qsE x)

theorem codesE_mem_FP : codesE ∈ FP := shenCodesEnc_mem_FP qsE_mem_FP

theorem codesE_eq (I : Instance) :
    codesE (DataEncode.bitstringEncode I) = DataEncode.bitstringEncode (shenCodes I.1 []) := by
  rw [codesE, qsE_eq, shenCodesEnc_eq]

/-- The number of rounds, in unary. -/
noncomputable def nU (x : List Bool) : List Bool := posCount (codesE x)

theorem nU_mem_FP : nU ∈ FP := posCount_mem_FP codesE_mem_FP

theorem nU_eq (I : Instance) :
    nU (DataEncode.bitstringEncode I) = List.replicate (shenChain I.1 []).length true := by
  rw [nU, codesE_eq, posCount_eq, shenCodes_length]

/-- The literal count of one clause, on `pair φE (unary i)`. -/
noncomputable def clauseLits (z : List Bool) : List Bool :=
  posCount (posAt (pairFst z) (pairSnd z).length)

theorem clauseLits_mem_FP : clauseLits ∈ FP :=
  posCount_mem_FP (posAt_mem_FP Cobham.sndBlock_mem_FP Cobham.fstBlock_mem_FP)

/-- The number of literals of the matrix, in unary. -/
noncomputable def litU (x : List Bool) : List Bool :=
  countOver clauseLits (pair (posCount (φE x)) (φE x))

theorem litU_mem_FP : litU ∈ FP := by
  unfold litU
  have h := mem_FP_comp (Cobham.pairFn_mem_FP (posCount_mem_FP φE_mem_FP) φE_mem_FP)
    (countOver_mem_FP clauseLits_mem_FP)
  simpa only [Function.comp_def] using h

theorem litU_length (I : Instance) :
    (litU (DataEncode.bitstringEncode I)).length = litCount I.2 := by
  rw [litU, φE_eq, posCount_eq, length_countOver, litCount]
  have : ∀ i ∈ Finset.range I.2.length,
      (clauseLits (pair (DataEncode.bitstringEncode I.2) (List.replicate i true))).length
        = (I.2[i]?.getD []).length := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [clauseLits, pairFst_pair, pairSnd_pair, List.length_replicate, posAt_eq_of_lt hi,
      posCount_eq, List.length_replicate, List.getElem?_eq_getElem hi]
    rfl
  rw [Finset.sum_congr rfl this]
  clear this
  induction I.2 with
  | nil => simp
  | cons c cs ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      rw [ih]
      ring

/-- The uniform degree bound `litCount + 2`, in unary. -/
noncomputable def DU (x : List Bool) : List Bool := litU x ++ [true, true]

theorem DU_mem_FP : DU ∈ FP := Cobham.appendFn_mem_FP litU_mem_FP (constFn_mem_FP _)

theorem DU_length (I : Instance) :
    (DU (DataEncode.bitstringEncode I)).length = litCount I.2 + 2 := by
  rw [DU, List.length_append, litU_length]
  rfl

/-- The degree-sum bound `6 n D + 1`, in unary. -/
noncomputable def NU (x : List Bool) : List Bool :=
  marks (mulLen (mulLen (List.replicate 6 true) (nU x)) (DU x)) ++ [true]

theorem NU_mem_FP : NU ∈ FP :=
  Cobham.appendFn_mem_FP
    (marks_mem_FP (mulLen_mem_FP (mulLen_mem_FP (constFn_mem_FP _) nU_mem_FP) DU_mem_FP))
    (constFn_mem_FP _)

theorem NU_length (I : Instance) :
    (NU (DataEncode.bitstringEncode I)).length
      = 6 * (shenChain I.1 []).length * (DU (DataEncode.bitstringEncode I)).length + 1 := by
  rw [NU, List.length_append, marks_eq, List.length_replicate, length_mulLen, length_mulLen, nU_eq,
    List.length_replicate, List.length_replicate]
  rfl

theorem NU_eq_replicate (x : List Bool) : NU x = List.replicate (NU x).length true := by
  rw [NU, marks_eq, List.length_append, List.length_replicate, List.replicate_add]
  rfl

/-- The modulus: the least prime above `N`, as an `N + 1`-bit string. -/
noncomputable def qStr (x : List Bool) : List Bool := primeBits (NU x)

theorem qStr_mem_FP : qStr ∈ FP := primeBitsFn_mem_FP NU_mem_FP

/-- **The modulus is a prime in `(N, 2 N]`**, below `2 ^ w` for `w = N + 1`. -/
theorem qStr_spec (I : Instance) :
    ∃ p : ℕ, p.Prime ∧ (NU (DataEncode.bitstringEncode I)).length < p ∧
      p ≤ 2 * (NU (DataEncode.bitstringEncode I)).length ∧
      p < 2 ^ ((NU (DataEncode.bitstringEncode I)).length + 1) ∧
      qStr (DataEncode.bitstringEncode I)
        = bitsOfLenLE ((NU (DataEncode.bitstringEncode I)).length + 1) p := by
  have hN : 0 < (NU (DataEncode.bitstringEncode I)).length := by rw [NU_length]; omega
  obtain ⟨p, hp, h1, h2, h3, h4⟩ := primeBits_eq (NU (DataEncode.bitstringEncode I)).length hN
  refine ⟨p, hp, h1, h2, h3, ?_⟩
  rw [qStr]
  conv_lhs => rw [NU_eq_replicate]
  exact h4

/-! ## The point and the claim -/

/-- The number of variables, in unary. -/
noncomputable def mU (x : List Bool) : List Bool := posCount (qsE x)

theorem mU_mem_FP : mU ∈ FP := posCount_mem_FP qsE_mem_FP

theorem mU_eq (I : Instance) :
    mU (DataEncode.bitstringEncode I) = List.replicate I.1.length true := by
  rw [mU, qsE_eq, posCount_eq]

/-- The initial point: every variable at `0`. -/
noncomputable def pt0 (x : List Bool) : List Bool := mulLen (mU x) (qStr x)

theorem pt0_mem_FP : pt0 ∈ FP := mulLen_mem_FP mU_mem_FP qStr_mem_FP

/-- The initial claim: `1`. -/
noncomputable def cl0 (x : List Bool) : List Bool := oneStr (qStr x)

theorem cl0_mem_FP : cl0 ∈ FP := oneStrFn_mem_FP qStr_mem_FP

/-- The all-zero point is the encoding of the zero assignment. -/
theorem pointStr_zero {p : ℕ} [NeZero p] (w m : ℕ) :
    pointStr w m (fun _ => (0 : ZMod p)) = List.replicate (m * w) false := by
  rw [pointStr]
  have : ((List.range m).map fun _ => encZMod w (0 : ZMod p))
      = (List.range m).map fun _ => List.replicate w false := by
    refine List.map_congr_left fun _ _ => ?_
    rw [encZMod, ZMod.val_zero, bitsOfLenLE_zero]
  rw [this, List.map_const', List.length_range]
  clear this
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm,
        List.replicate_add]

theorem pt0_eq (I : Instance) {p : ℕ} [NeZero p] {w : ℕ}
    (hq : qStr (DataEncode.bitstringEncode I) = bitsOfLenLE w p) :
    pt0 (DataEncode.bitstringEncode I) = pointStr w I.1.length (fun _ => (0 : ZMod p)) := by
  rw [pt0, mU_eq, hq, mulLen, List.length_replicate, bitsOfLenLE_length, pointStr_zero]

theorem cl0_eq (I : Instance) {p : ℕ} [NeZero p] {w : ℕ} (hp : p < 2 ^ w) (hp1 : 1 < p)
    (hq : qStr (DataEncode.bitstringEncode I) = bitsOfLenLE w p) :
    cl0 (DataEncode.bitstringEncode I) = encZMod w (1 : ZMod p) := by
  rw [cl0, hq, oneStr_encZMod w hp hp1]

/-! ## Composition lemmas and opacity -/

theorem qStr_comp {a : List Bool → List Bool} (ha : a ∈ FP) : (fun z => qStr (a z)) ∈ FP := by
  have h := mem_FP_comp ha qStr_mem_FP
  simpa only [Function.comp_def] using h

theorem codesE_comp {a : List Bool → List Bool} (ha : a ∈ FP) :
    (fun z => codesE (a z)) ∈ FP := by
  have h := mem_FP_comp ha codesE_mem_FP
  simpa only [Function.comp_def] using h

theorem pt0_comp {a : List Bool → List Bool} (ha : a ∈ FP) : (fun z => pt0 (a z)) ∈ FP := by
  have h := mem_FP_comp ha pt0_mem_FP
  simpa only [Function.comp_def] using h

theorem cl0_comp {a : List Bool → List Bool} (ha : a ∈ FP) : (fun z => cl0 (a z)) ∈ FP := by
  have h := mem_FP_comp ha cl0_mem_FP
  simpa only [Function.comp_def] using h

theorem DU_comp {a : List Bool → List Bool} (ha : a ∈ FP) : (fun z => DU (a z)) ∈ FP := by
  have h := mem_FP_comp ha DU_mem_FP
  simpa only [Function.comp_def] using h

theorem φE_comp {a : List Bool → List Bool} (ha : a ∈ FP) : (fun z => φE (a z)) ∈ FP := by
  have h := mem_FP_comp ha φE_mem_FP
  simpa only [Function.comp_def] using h

/- These functions unfold into scans containing a concrete `Polynomial.eval`; the unifier must
never be allowed to unfold them. Their behaviour is exposed only through the lemmas above. -/
attribute [irreducible] qsE φE codesE nU litU DU NU qStr mU pt0 cl0

end Complexity
