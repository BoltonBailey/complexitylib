/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib.Models.RandomAccessMachine.Internal
import Complexitylib.Models.RandomAccessMachine.Soundness
import Complexitylib.Asymptotics

/-!
# Random access machines (surface)

This is the public entry point for the library's Random Access Machine (RAM)
model: a register machine with indirect addressing, executed under a
**logarithmic-cost** time measure and a matching space measure. The model,
its executable semantics, and both cost measures are defined in
`Complexitylib.Models.RandomAccessMachine.Defs`; the operational metatheory is
proved in `…/Internal`; the soundness of the cost convention is established in
`…/Soundness`.

## Main definitions

- `RAM.Instr`, `RAM.Program`, `RAM.Cfg`, `RAM.step`, `RAM.run` — the model
- `RAM.logTimeUpto`, `RAM.unitTimeUpto`, `RAM.spaceUpto` — the resource measures
- `RAM.Program.DecidesInTime`, `RAM.Program.DecidesInSpace` — deciding a language
- `RAM.DTIME`, `RAM.DSPACE` — the RAM time/space classes, over the same
  `Language = Set (List Bool)` interface as the Turing-machine classes `DTIME`,
  `DSPACE`, so the two families are directly comparable

## Main results

- `RAM.logGap_squaring` — the **soundness theorem**: the squaring program family
  has unit time `k + 1` but logarithmic time at least `2 ^ k`, so unit cost is
  super-polynomially stronger than logarithmic cost. This is the formal reason
  the library measures RAM time logarithmically and only then compares it to
  Turing time.
- `RAM.unitTimeUpto_le_logTimeUpto` — the step count is always at most the
  logarithmic time (every step costs `≥ 1`).
- `RAM.Program.DecidesInTime.mono` — deciding is monotone in the time bound.
- `RAM.run_initCfg_finiteSupport` — the register file keeps finite support
  along any run, so the space measure `RAM.Cfg.space` is a genuine finite sum.

## Relationship to the Turing-machine models

The RAM shares the library's `Language` interface, so `RAM.DTIME`/`RAM.DSPACE`
and the Turing-machine classes `DTIME`/`DSPACE` speak about the same objects.
The classical two-way simulation bounds that make the models polynomially
equivalent are (Cook–Reckhow, *Time bounded random access machines*, JCSS 7
(1973), 354–375; van Emde Boas, *Machine models and simulations*, Handbook of
Theoretical Computer Science A, 1990):

* **Turing machine → RAM.** A `T(n)`-time multi-tape Turing machine is
  simulated by a RAM in logarithmic time `O(T(n) · log T(n))`.
* **RAM → Turing machine.** A `T(n)`-time logarithmic-cost RAM is simulated by
  a multi-tape Turing machine in time `O(T(n)²)`.

Both overheads are polynomial, so `RAM.DTIME` and `DTIME` yield the *same*
polynomial-time class: `RAM-P = P`. Under the **unit-cost** measure the
RAM → TM direction fails — `RAM.logGap_squaring` exhibits a program whose
unit-time is linear but whose output already needs exponentially many Turing
steps to write — which is precisely why the model is defined with logarithmic
cost. These simulations are the next milestone for this model (see `ROADMAP.md`,
track *M6. Random access machines and machine-model robustness*); this module
fixes the definitions, resource conventions, and the soundness theorem they
build on, and does not assert the simulations as proved.
-/

namespace Complexity

namespace RAM

/-- `RAM.DTIME(T)` is the class of languages decided by a RAM in logarithmic
    time `O(T(n))`. Defined over the same `Language` interface as the
    Turing-machine class `DTIME(T)`, so the two are directly comparable; they
    coincide up to the polynomial simulation overhead documented above. -/
def DTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (P : Program) (f : ℕ → ℕ), P.DecidesInTime L f ∧ f =O T}

/-- `RAM.DSPACE(S)` is the class of languages decided by a RAM in logarithmic
    space `O(S(n))`, over the same `Language` interface as the Turing-machine
    class `DSPACE(S)`. -/
def DSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (P : Program) (f : ℕ → ℕ), P.DecidesInSpace L f ∧ f =O S}

/-- Deciding in logarithmic time is monotone in the time bound. Mirrors
    `TM.DecidesInTime.mono`. -/
theorem Program.DecidesInTime.mono {P : Program} {L : Language} {T T' : ℕ → ℕ}
    (hle : ∀ m, T m ≤ T' m) (h : P.DecidesInTime L T) : P.DecidesInTime L T' := by
  intro x
  obtain ⟨fuel, hhalt, hcost, hyes, hno⟩ := h x
  exact ⟨fuel, hhalt, hcost.trans (hle x.length), hyes, hno⟩

/-- Deciding in logarithmic space is monotone in the space bound. -/
theorem Program.DecidesInSpace.mono {P : Program} {L : Language} {S S' : ℕ → ℕ}
    (hle : ∀ m, S m ≤ S' m) (h : P.DecidesInSpace L S) : P.DecidesInSpace L S' := by
  intro x
  obtain ⟨fuel, hhalt, hspace, hyes, hno⟩ := h x
  exact ⟨fuel, hhalt, hspace.trans (hle x.length), hyes, hno⟩

/-! ### A worked decider

The two-instruction program `⟨imm 0 1⟩` overwrites the verdict register with `1`
and then halts (its program counter runs off the end). It decides the universal
language in constant logarithmic time, exercising the full `DecidesInTime` API
end to end. -/

/-- The always-accept program: set the verdict register to `1`. -/
def acceptProg : Program := [Instr.imm 0 1]

/-- On any input, `acceptProg` halts after one step with verdict `1`. -/
theorem acceptProg_run (x : List Bool) :
    (run acceptProg 1 (initCfg x)).verdict = 1 := by
  rfl

/-- `acceptProg` decides the universal language in constant logarithmic time. -/
theorem acceptProg_decides : acceptProg.DecidesInTime Set.univ (fun _ => 2) := by
  intro x
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro _; rfl
  · intro hx; exact absurd (Set.mem_univ x) hx

/-- The universal language is in `RAM.DTIME` at a constant bound: a witness that
    the RAM time classes are inhabited over the shared `Language` interface. -/
theorem univ_mem_DTIME : Set.univ ∈ DTIME (fun _ => 2) :=
  ⟨acceptProg, (fun _ => 2), acceptProg_decides, BigO.refl _⟩

end RAM

end Complexity
