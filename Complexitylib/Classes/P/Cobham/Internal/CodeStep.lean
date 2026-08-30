/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.P.Cobham.Internal.PolyRuler

/-!
# What the encoded step does to a reachable configuration

⚠️ Unreviewed by Bolton

`Cobham.stepFn` tracks a machine's step only on configurations that respect the
encoding's window: every head inside it, every tape carrying its left-end
marker. This file collects those side conditions into `Complexity.CodeInv`,
shows that every configuration of a space-bounded machine's configuration graph
satisfies it, and reads off what `Complexity.nstepFn` computes there.

## Main definitions

- `Complexity.CodeInv` — the encoding's side conditions on a configuration

## Main results

- `Complexity.cfgCode_length` — a code is exactly `2(k+2)+1` blocks wide
-/

@[expose] public section

namespace Complexity

open Cobham

variable {k : ℕ}

/-! ## The width of a code -/

/-- The number of blocks in a code: one for the state and two per tape. -/
def codeBlocks (k : ℕ) : ℕ := 2 * (k + 2) + 1

private theorem length_flatten_const {α : Type} (bs : List (List α)) (w : ℕ)
    (h : ∀ b ∈ bs, b.length = w) : bs.flatten.length = bs.length * w := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      rw [List.flatten_cons, List.length_append, h b (List.mem_cons_self),
        ih (fun c hc => h c (List.mem_cons_of_mem _ hc)), List.length_cons, Nat.succ_mul]
      omega

/-- **A code is exactly `2(k+2)+1` blocks wide.** -/
@[simp] theorem cfgCode_length {Q : Type} [Fintype Q] [DecidableEq Q] (W : ℕ)
    (c : Cfg k Q) :
    (Cobham.cfgCode W c).length = codeBlocks k * (blockRuler W).length := by
  rw [Cobham.cfgCode, length_flatten_const _ _ (cfgBlocks_width W c), cfgBlocks_length, codeBlocks]

/-! ## The window conditions -/

/-- The side conditions under which the encoded step tracks the real one. -/
structure CodeInv {Q : Type} (W : ℕ) (c : Cfg k Q) : Prop where
  /-- Every tape carries its left-end marker. -/
  start : ∀ t ∈ cfgTapes c, t.StartInvariant
  /-- Every head is inside the encoded window. -/
  head : ∀ t ∈ cfgTapes c, t.head ≤ W

end Complexity
