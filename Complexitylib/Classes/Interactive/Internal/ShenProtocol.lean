/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Interactive.Internal.ShenRound

/-!
# Shen's protocol as a `Protocol`

⚠️ Unreviewed by Bolton

The concrete verifier packaged with its polynomial bounds: `Rp` rounds, `Wp` coins per round,
`Mp` on the message length. The message-length bound is discharged from the polynomial output
bounds of the parameter functions (`Cobham.output_length_poly_of_mem_FP`), so `exists_shenBounds`
produces a valid set of bounds for any choice of `Rp` and `Wp`.

## Main definitions

- `ShenBounds`, `shenProtocol`

## Main results

- `exists_shenBounds` — bounds exist
-/

@[expose] public section

namespace Complexity

/-- The polynomial bounds of the concrete protocol: rounds `Rp`, coins per round `Wp`, message
length `Mp`, with the message-length bound on the verifier's own messages. -/
structure ShenBounds where
  /-- Rounds. -/
  Rp : Polynomial ℕ
  /-- Coins per round. -/
  Wp : Polynomial ℕ
  /-- Message length. -/
  Mp : Polynomial ℕ
  /-- The verifier's messages respect the bound. -/
  hM : ∀ z, (shenVmsg Wp z).length ≤ Mp.eval (RepArgs.vx z).length

/-- **Shen's protocol**, as a `Protocol`. -/
noncomputable def shenProtocol (B : ShenBounds) : Protocol where
  rounds n := B.Rp.eval n
  coins n := (B.Rp * B.Wp).eval n
  msgLen n := B.Mp.eval n
  vmsg := shenVmsg B.Wp
  vmsg_mem := shenVmsg_mem_FP B.Wp
  vmsg_len := fun x r τ => by
    have := B.hM (protocolView x r τ)
    rwa [RepArgs.vx_view] at this
  verdict := shenVerdict
  verdict_mem := shenVerdict_mem_P

/-- **Message bounds exist**: the verifier's messages are polynomially bounded in the input. -/
theorem exists_shenBounds (Rp Wp : Polynomial ℕ) :
    ∃ B : ShenBounds, B.Rp = Rp ∧ B.Wp = Wp := by
  obtain ⟨Pc, hPc⟩ := Cobham.output_length_poly_of_mem_FP codesE_mem_FP
  obtain ⟨Pp, hPp⟩ := Cobham.output_length_poly_of_mem_FP pt0_mem_FP
  obtain ⟨Pq, hPq⟩ := Cobham.output_length_poly_of_mem_FP qStr_mem_FP
  obtain ⟨Pcl, hPcl⟩ := Cobham.output_length_poly_of_mem_FP cl0_mem_FP
  refine ⟨⟨Rp, Wp, 2 * Pc + 2 * Pp + Pq + Pcl + Polynomial.C 8, fun z => ?_⟩, rfl, rfl⟩
  have h := shenVmsg_length_le Wp z
  have h1 := hPc (RepArgs.vx z)
  have h2 := hPp (RepArgs.vx z)
  have h3 := hPq (RepArgs.vx z)
  have h4 := hPcl (RepArgs.vx z)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_C]
  omega

end Complexity
