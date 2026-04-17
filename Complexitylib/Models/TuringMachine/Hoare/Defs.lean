import Complexitylib.Models.TuringMachine

/-!
# Hoare-style specifications for Turing machines

This file defines Hoare triples for reasoning about TM behavior in terms of
tape preconditions and postconditions. This provides a compositional framework
for building and verifying complex machines from simpler components.

## Main definitions

- `TapePred` — a predicate on the tape configuration (input, work, output)
- `TM.HoareTime` — time-bounded Hoare triple: `{pre} tm {post} [≤ bound]`
- `TM.Hoare` — unbounded Hoare triple: `{pre} tm {post}`

## Design notes

Hoare triples abstract away the internal state `Q`, reasoning purely about
tape contents and head positions. This makes them ideal for compositional
reasoning: the pre/postconditions of composed machines can be stated without
reference to the internal state types of the components.

The precondition must imply that the starting configuration has the machine's
`qstart` state. The postcondition holds at halting.
-/

namespace TM

variable {n : ℕ}

/-- A predicate on the tape configuration: input tape, work tapes, output tape. -/
abbrev TapePred (n : ℕ) := Tape → (Fin n → Tape) → Tape → Prop

/-- **Time-bounded Hoare triple**: for any tapes satisfying `pre`, starting
    from `qstart`, the machine halts within `bound` steps with tapes satisfying
    `post`.

    This is the core specification type for compositional TM reasoning.
    Captures both correctness (pre/post) and efficiency (time bound). -/
def HoareTime (tm : TM n) (pre post : TapePred n) (bound : ℕ) : Prop :=
  ∀ inp work out, pre inp work out →
    ∃ c' t, t ≤ bound ∧
      tm.reachesIn t { state := tm.qstart, input := inp, work := work, output := out } c' ∧
      tm.halted c' ∧ post c'.input c'.work c'.output

/-- **Unbounded Hoare triple**: the machine halts with tapes satisfying `post`,
    without a time bound. Useful when only correctness matters. -/
def Hoare (tm : TM n) (pre post : TapePred n) : Prop :=
  ∀ inp work out, pre inp work out →
    ∃ c', tm.reaches { state := tm.qstart, input := inp, work := work, output := out } c' ∧
      tm.halted c' ∧ post c'.input c'.work c'.output

-- ════════════════════════════════════════════════════════════════════════
-- Helper: reachesIn implies reaches (re-export of TM.reaches_of_reachesIn)
-- ════════════════════════════════════════════════════════════════════════

@[inherit_doc TM.reaches_of_reachesIn]
private theorem reachesIn_toReaches {tm : TM n} {t : ℕ} {c c' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') : tm.reaches c c' :=
  TM.reaches_of_reachesIn h

-- ════════════════════════════════════════════════════════════════════════
-- Structural rules
-- ════════════════════════════════════════════════════════════════════════

/-- **Consequence rule**: weaken the precondition and strengthen the postcondition. -/
theorem HoareTime.consequence {tm : TM n}
    {pre pre' post post' : TapePred n} {b b' : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out)
    (hpost : ∀ inp work out, post inp work out → post' inp work out)
    (hbound : b ≤ b') :
    tm.HoareTime pre' post' b' := by
  intro inp work out hpre'
  obtain ⟨c', t, ht, hreach, hhalt, hpost_c⟩ := h inp work out (hpre _ _ _ hpre')
  exact ⟨c', t, le_trans ht hbound, hreach, hhalt, hpost _ _ _ hpost_c⟩

/-- **Precondition weakening**: if `pre'` implies `pre`, lift the Hoare triple. -/
theorem HoareTime.weaken_pre {tm : TM n}
    {pre pre' post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpre : ∀ inp work out, pre' inp work out → pre inp work out) :
    tm.HoareTime pre' post b :=
  h.consequence hpre (fun _ _ _ h => h) le_rfl

/-- **Postcondition strengthening**: if `post` implies `post'`, lift the triple. -/
theorem HoareTime.strengthen_post {tm : TM n}
    {pre post post' : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b)
    (hpost : ∀ inp work out, post inp work out → post' inp work out) :
    tm.HoareTime pre post' b :=
  h.consequence (fun _ _ _ h => h) hpost le_rfl

/-- **Time monotonicity**: increase the time bound. -/
theorem HoareTime.mono_bound {tm : TM n}
    {pre post : TapePred n} {b b' : ℕ}
    (h : tm.HoareTime pre post b) (hle : b ≤ b') :
    tm.HoareTime pre post b' :=
  h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) hle

/-- Bounded implies unbounded. -/
theorem HoareTime.toHoare {tm : TM n}
    {pre post : TapePred n} {b : ℕ}
    (h : tm.HoareTime pre post b) :
    tm.Hoare pre post := by
  intro inp work out hpre
  obtain ⟨c', t, _, hreach, hhalt, hpost⟩ := h inp work out hpre
  exact ⟨c', reachesIn_toReaches hreach, hhalt, hpost⟩

-- ════════════════════════════════════════════════════════════════════════
-- Connection to DecidesInTime
-- ════════════════════════════════════════════════════════════════════════

/-- `DecidesInTime` implies a family of Hoare triples, one per input. -/
theorem hoareTime_of_decidesInTime {tm : TM n} {L : Language} {T : ℕ → ℕ}
    (h : tm.DecidesInTime L T) (x : List Bool) :
    tm.HoareTime
      (fun inp work out => inp = initTape (x.map Γ.ofBool) ∧
                           (work = fun _ => initTape []) ∧
                           out = initTape [])
      (fun _ _ out => (x ∈ L → out.cells 1 = Γ.one) ∧
                      (x ∉ L → out.cells 1 = Γ.zero))
      (T x.length) := by
  intro inp work out ⟨hinp, hwork, hout⟩
  subst hinp; subst hout; subst hwork
  obtain ⟨c', t, ht, hreach, hhalt, hmem, hnmem⟩ := h x
  exact ⟨c', t, ht, hreach, hhalt, hmem, hnmem⟩

end TM
