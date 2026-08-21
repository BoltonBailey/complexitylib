/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.SavitchBits

/-!
# The abstract semantics of Savitch's stack machine

⚠️ Unreviewed by Bolton

`Complexitylib.Classes.Containments.Internal.SavitchStep` writes Savitch's
recursion as a polynomial-time function on a bitstring. This file gives the same
recursion on an ordinary inductive state — a `List` of frames rather than a
right-nested chain of pairs — where its correctness and its running time can be
proved by induction without any encoding in the way.

The machine is parametric in the two base tests it calls, `br` (is `v` within one
step of `u`) and `ba` (is `u` accepting, or within one step of accepting), and in
the all-zero code `z`, which is both the first midpoint every frame tries and the
width the enumeration wraps at.

## Main definitions

- `Complexity.Sav.Frm`, `Complexity.Sav.Sst` — a frame and the machine's state
- `Complexity.Sav.step` — one step of the recursion
- `Complexity.Sav.rchB`, `Complexity.Sav.accB` — what the recursion computes
- `Complexity.Sav.frameVal` — the value a frame is going to return
- `Complexity.Sav.runBound` — the number of steps a level costs

## Main results

- `Complexity.Sav.run_frame` — a frame pushed on the stack is popped again, with
  its value, within `runBound` steps, and the done flag stays down throughout
-/

@[expose] public section

namespace Complexity
namespace Sav

/-! ## The state -/

/-- A frame of Savitch's recursion: which subproblem it is working on (`kind`),
which half of the interval it is trying (`ph`), the level in unary (`lvl`), the
two endpoints (`u`, `v`) and the midpoint being tried (`m`). -/
structure Frm where
  /-- `true` for *is an accepting configuration reachable from `u`*, `false` for
  *is `v` reachable from `u`*. -/
  kind : Bool
  /-- `false` while the first half of the interval is being tried. -/
  ph : Bool
  /-- The level, in unary: `2 ^ lvl.length` steps are allowed. -/
  lvl : List Bool
  /-- The source endpoint. -/
  u : List Bool
  /-- The target endpoint; unused by an acceptance frame. -/
  v : List Bool
  /-- The midpoint being tried, which doubles as the enumeration's counter. -/
  m : List Bool

/-- The machine's state: the done flag, the answer, the value a finished subcall
is returning (`none` while descending), and the stack. -/
structure Sst where
  /-- The bit the space-bounded iteration watches. -/
  done : Bool
  /-- The answer, once it is known. -/
  ans : Bool
  /-- The value a finished subcall is returning. -/
  ret : Option Bool
  /-- The stack, top frame first. -/
  stk : List Frm

/-! ## One step -/

/-- The child a frame pushes: the first half of its interval while its phase is
zero, the second half afterwards. -/
def child (z : List Bool) (f : Frm) : Frm :=
  if f.ph then
    if f.kind then ⟨true, false, f.lvl.drop 1, f.m, z, z⟩
    else ⟨false, false, f.lvl.drop 1, f.m, f.v, z⟩
  else ⟨false, false, f.lvl.drop 1, f.u, f.m, z⟩

/-- The value a level-zero frame returns. -/
def baseVal (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (f : Frm) : Bool :=
  if f.kind then ba f.u else br f.u f.v

/-- **One step of Savitch's recursion**, on the abstract state. -/
def step (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (s : Sst) : Sst :=
  if s.done then ⟨s.ans, s.ans, s.ret, s.stk⟩
  else
    match s.stk, s.ret with
    | [], r => ⟨true, r.getD false, r, []⟩
    | f :: fs, none =>
        if f.lvl = [] then ⟨false, s.ans, some (baseVal br ba f), fs⟩
        else ⟨false, s.ans, none, child z f :: f :: fs⟩
    | f :: fs, some true =>
        if f.ph then ⟨false, s.ans, some true, fs⟩
        else ⟨false, s.ans, none, { f with ph := true } :: fs⟩
    | f :: fs, some false =>
        if bumpOver f.m then ⟨false, s.ans, some false, fs⟩
        else ⟨false, s.ans, none, { f with ph := false, m := bumpBits f.m } :: fs⟩

variable (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)

@[simp] theorem step_of_done (a : Bool) (r : Option Bool) (stk : List Frm) :
    step br ba z ⟨true, a, r, stk⟩ = ⟨a, a, r, stk⟩ := rfl

@[simp] theorem step_of_empty (a : Bool) (r : Option Bool) :
    step br ba z ⟨false, a, r, []⟩ = ⟨true, r.getD false, r, []⟩ := rfl

theorem step_base (a : Bool) (f : Frm) (fs : List Frm) (h : f.lvl = []) :
    step br ba z ⟨false, a, none, f :: fs⟩ = ⟨false, a, some (baseVal br ba f), fs⟩ := by
  simp [step, h]

theorem step_push (a : Bool) (f : Frm) (fs : List Frm) (h : f.lvl ≠ []) :
    step br ba z ⟨false, a, none, f :: fs⟩ = ⟨false, a, none, child z f :: f :: fs⟩ := by
  simp [step, h]

theorem step_ret_true_ph (a : Bool) (f : Frm) (fs : List Frm) (h : f.ph = true) :
    step br ba z ⟨false, a, some true, f :: fs⟩ = ⟨false, a, some true, fs⟩ := by
  simp [step, h]

theorem step_ret_true_of_ph_false (a : Bool) (f : Frm) (fs : List Frm) (h : f.ph = false) :
    step br ba z ⟨false, a, some true, f :: fs⟩
      = ⟨false, a, none, { f with ph := true } :: fs⟩ := by
  simp [step, h]

theorem step_ret_false_over (a : Bool) (f : Frm) (fs : List Frm) (h : bumpOver f.m = true) :
    step br ba z ⟨false, a, some false, f :: fs⟩ = ⟨false, a, some false, fs⟩ := by
  simp [step, h]

theorem step_ret_false_bump (a : Bool) (f : Frm) (fs : List Frm) (h : bumpOver f.m = false) :
    step br ba z ⟨false, a, some false, f :: fs⟩
      = ⟨false, a, none, { f with ph := false, m := bumpBits f.m } :: fs⟩ := by
  simp [step, h]

/-! ## What the recursion computes -/

/-- Try `j` successive midpoints, starting at `m`. -/
def anyMid (P : List Bool → Bool) : List Bool → ℕ → Bool
  | _, 0 => false
  | m, j + 1 => P m || anyMid P (bumpBits m) j

@[simp] theorem anyMid_zero (P : List Bool → Bool) (m : List Bool) : anyMid P m 0 = false := rfl

@[simp] theorem anyMid_succ (P : List Bool → Bool) (m : List Bool) (j : ℕ) :
    anyMid P m (j + 1) = (P m || anyMid P (bumpBits m) j) := rfl

/-- **Reachability within `2 ^ n` steps**, as the recursion computes it. -/
def rchB (br : List Bool → List Bool → Bool) (z : List Bool) :
    ℕ → List Bool → List Bool → Bool
  | 0, u, v => br u v
  | n + 1, u, v => anyMid (fun m => rchB br z n u m && rchB br z n m v) z (2 ^ z.length)

/-- **Acceptance within `2 ^ n` steps**, as the recursion computes it. -/
def accB (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool) :
    ℕ → List Bool → Bool
  | 0, u => ba u
  | n + 1, u => anyMid (fun m => rchB br z n u m && accB br ba z n m) z (2 ^ z.length)

/-- The number of midpoints a frame has still to try. -/
def midRem (m : List Bool) : ℕ := 2 ^ m.length - binValLE m

theorem midRem_pos (m : List Bool) : 0 < midRem m :=
  Nat.sub_pos_of_lt (binValLE_lt m)

theorem midRem_le (m : List Bool) : midRem m ≤ 2 ^ m.length := Nat.sub_le _ _

theorem midRem_of_over {m : List Bool} (h : bumpOver m = true) : midRem m = 1 := by
  have hv := (bumpOver_iff m).mp h
  have hp : 0 < 2 ^ m.length := Nat.two_pow_pos _
  rw [midRem, hv]
  omega

theorem midRem_bump {m : List Bool} (h : bumpOver m = false) :
    midRem (bumpBits m) + 1 = midRem m := by
  have hv := binValLE_bumpBits_of_not_over m h
  have hlen := bumpBits_length m
  have hlt := binValLE_lt (bumpBits m)
  rw [hlen] at hlt
  rw [midRem, midRem, hlen, hv]
  have hp : 0 < 2 ^ m.length := Nat.two_pow_pos _
  omega

theorem midRem_zero {m : List Bool} (h : binValLE m = 0) : midRem m = 2 ^ m.length := by
  rw [midRem, h, Nat.sub_zero]

/-- The value the frame `f` is going to return, given the state it is in. -/
def frameValAux (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (kind : Bool) (lvl u v m : List Bool) : Bool :=
  match lvl with
  | [] => if kind then ba u else br u v
  | _ :: t =>
      anyMid (fun w => rchB br z t.length u w &&
        (if kind then accB br ba z t.length w else rchB br z t.length w v)) m (midRem m)

/-- The value the frame `f` is going to return. -/
def frameVal (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (f : Frm) : Bool :=
  frameValAux br ba z f.kind f.lvl f.u f.v f.m

theorem frameVal_of_nil {f : Frm} (h : f.lvl = []) :
    frameVal br ba z f = baseVal br ba f := by
  rw [frameVal, baseVal, h]; rfl

theorem frameVal_of_cons {f : Frm} {b : Bool} {t : List Bool} (h : f.lvl = b :: t) :
    frameVal br ba z f
      = anyMid (fun w => rchB br z t.length f.u w &&
          (if f.kind then accB br ba z t.length w else rchB br z t.length w f.v))
        f.m (midRem f.m) := by
  rw [frameVal, h]; rfl

/-- A fresh frame — phase zero, midpoint at the bottom of the enumeration —
returns exactly the value its level asks for. -/
theorem frameVal_fresh {f : Frm} (hz : binValLE z = 0) (hm : f.m = z) :
    frameVal br ba z f
      = if f.kind then accB br ba z f.lvl.length f.u else rchB br z f.lvl.length f.u f.v := by
  rcases hl : f.lvl with _ | ⟨b, t⟩
  · rw [frameVal_of_nil br ba z hl, baseVal]
    cases f.kind <;> simp [accB, rchB]
  · rw [frameVal_of_cons br ba z hl, hm, midRem_zero hz, List.length_cons]
    cases f.kind <;> simp [accB, rchB]

/-! ## The invariant a frame carries -/

/-- A frame is well formed when its midpoint has the enumeration's width and,
once its phase has advanced, its first half really did succeed. -/
structure FrmOk (br : List Bool → List Bool → Bool) (z : List Bool) (f : Frm) : Prop where
  /-- The midpoint is a code. -/
  mlen : f.m.length = z.length
  /-- The first half succeeded before the phase advanced. -/
  phase : f.ph = true → rchB br z (f.lvl.length - 1) f.u f.m = true

/-! ## The number of steps -/

/-- The steps a frame at level `n` costs, over an enumeration of width `W`. -/
def runBound (W : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * 2 ^ W + 1) * (runBound W n + 2)

/-- How much work a frame has left, within its level. -/
def mu (f : Frm) : ℕ := 2 * midRem f.m + (if f.ph then 0 else 1)

theorem mu_of_ph_true {f : Frm} (h : f.ph = true) : mu f = 2 * midRem f.m := by
  rw [mu, h]; simp

theorem mu_of_ph_false {f : Frm} (h : f.ph = false) : mu f = 2 * midRem f.m + 1 := by
  rw [mu, h]; simp

theorem mu_pos (f : Frm) : 0 < mu f := by
  have := midRem_pos f.m
  rw [mu]
  split <;> omega

theorem mu_le {f : Frm} (h : f.m.length = z.length) : mu f ≤ 2 * 2 ^ z.length + 1 := by
  have := midRem_le f.m
  rw [h] at this
  rw [mu]
  split <;> omega

/-! ## The done flag stays down -/

/-- The done flag is down at every point of the first `T` steps from `s`. -/
def DoneDown (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (s : Sst) (T : ℕ) : Prop := ∀ j ≤ T, ((step br ba z)^[j] s).done = false

theorem doneDown_zero {s : Sst} (h : s.done = false) : DoneDown br ba z s 0 := by
  intro j hj
  have : j = 0 := Nat.le_zero.mp hj
  subst this
  simpa using h

theorem doneDown_add {s : Sst} {T₁ T₂ : ℕ} (h₁ : DoneDown br ba z s T₁)
    (h₂ : DoneDown br ba z ((step br ba z)^[T₁] s) T₂) : DoneDown br ba z s (T₁ + T₂) := by
  intro j hj
  by_cases hle : j ≤ T₁
  · exact h₁ j hle
  · have hj' : j = T₂ ⊓ (j - T₁) + T₁ := by omega
    have : j = (j - T₁) + T₁ := by omega
    rw [this, Function.iterate_add_apply]
    exact h₂ _ (by omega)

theorem doneDown_succ {s : Sst} {T : ℕ} (h : DoneDown br ba z s T)
    (h' : ((step br ba z)^[T + 1] s).done = false) : DoneDown br ba z s (T + 1) := by
  intro j hj
  rcases Nat.lt_or_ge j (T + 1) with hlt | hge
  · exact h j (by omega)
  · have : j = T + 1 := by omega
    subst this
    exact h'

/-! ## Unfolding a frame's value -/

@[simp] theorem child_lvl (f : Frm) : (child z f).lvl = f.lvl.drop 1 := by
  rw [child]; split_ifs <;> rfl

@[simp] theorem child_m (f : Frm) : (child z f).m = z := by
  rw [child]; split_ifs <;> rfl

@[simp] theorem child_ph (f : Frm) : (child z f).ph = false := by
  rw [child]; split_ifs <;> rfl

theorem frameVal_child_of_ph_false (hz : binValLE z = 0) {f : Frm} (h : f.ph = false) :
    frameVal br ba z (child z f) = rchB br z (f.lvl.length - 1) f.u f.m := by
  have hc : child z f = ⟨false, false, f.lvl.drop 1, f.u, f.m, z⟩ := by
    rw [child, h]; simp
  rw [frameVal_fresh br ba z hz (show (child z f).m = z by rw [hc]), hc]
  simp

theorem frameVal_child_of_ph_true (hz : binValLE z = 0) {f : Frm} (h : f.ph = true) :
    frameVal br ba z (child z f)
      = if f.kind then accB br ba z (f.lvl.length - 1) f.m
        else rchB br z (f.lvl.length - 1) f.m f.v := by
  have hc : child z f =
      if f.kind then ⟨true, false, f.lvl.drop 1, f.m, z, z⟩
      else ⟨false, false, f.lvl.drop 1, f.m, f.v, z⟩ := by
    rw [child, h]; simp
  rw [frameVal_fresh br ba z hz (show (child z f).m = z by rw [child_m]), hc]
  cases f.kind <;> simp

/-- The candidate a frame is currently testing. -/
def midVal (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (n : ℕ) (f : Frm) : Bool :=
  rchB br z n f.u f.m && (if f.kind then accB br ba z n f.m else rchB br z n f.m f.v)

theorem frameVal_of_last {f : Frm} {b : Bool} {t : List Bool} (hl : f.lvl = b :: t)
    (hov : bumpOver f.m = true) : frameVal br ba z f = midVal br ba z t.length f := by
  rw [frameVal_of_cons br ba z hl, midRem_of_over hov, anyMid_succ, anyMid_zero,
    Bool.or_false, midVal]

theorem frameVal_of_bump {f : Frm} {b : Bool} {t : List Bool} (hl : f.lvl = b :: t)
    (hov : bumpOver f.m = false) :
    frameVal br ba z f
      = (midVal br ba z t.length f ||
          frameVal br ba z { f with ph := false, m := bumpBits f.m }) := by
  have hr : midRem f.m = midRem (bumpBits f.m) + 1 := (midRem_bump hov).symm
  rw [frameVal_of_cons br ba z hl, hr, anyMid_succ,
    frameVal_of_cons br ba z (f := { f with ph := false, m := bumpBits f.m }) (by simpa using hl)]
  rfl

theorem frameVal_of_mid {f : Frm} {b : Bool} {t : List Bool} (hl : f.lvl = b :: t)
    (h : midVal br ba z t.length f = true) : frameVal br ba z f = true := by
  obtain ⟨r, hr⟩ : ∃ r, midRem f.m = r + 1 := ⟨midRem f.m - 1, by have := midRem_pos f.m; omega⟩
  rw [frameVal_of_cons br ba z hl, hr, anyMid_succ]
  rw [midVal] at h
  rw [h, Bool.true_or]

/-! ## Runs -/

/-- The frame `f`, pushed on top of `fs`, is popped again with its value after
exactly `T` steps, and the done flag stays down throughout. -/
def RunsTo (br : List Bool → List Bool → Bool) (ba : List Bool → Bool) (z : List Bool)
    (f : Frm) (fs : List Frm) (a : Bool) (T : ℕ) : Prop :=
  0 < T ∧ DoneDown br ba z ⟨false, a, none, f :: fs⟩ T ∧
    (step br ba z)^[T] ⟨false, a, none, f :: fs⟩ = ⟨false, a, some (frameVal br ba z f), fs⟩

/-- A run that begins by re-entering a frame of the same value. -/
theorem runsTo_prepend {f g : Frm} {fs : List Frm} {a : Bool} {T₀ T₁ : ℕ}
    (hd : DoneDown br ba z ⟨false, a, none, f :: fs⟩ T₀)
    (hs : (step br ba z)^[T₀] ⟨false, a, none, f :: fs⟩ = ⟨false, a, none, g :: fs⟩)
    (hr : RunsTo br ba z g fs a T₁)
    (hval : frameVal br ba z g = frameVal br ba z f) :
    RunsTo br ba z f fs a (T₁ + T₀) := by
  obtain ⟨hpos, hdd, hend⟩ := hr
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.add_comm]
    exact doneDown_add br ba z hd (by rw [hs]; exact hdd)
  · rw [Function.iterate_add_apply, hs, hend, hval]

/-- Pushing a frame's child, running it, and processing its return. -/
theorem child_phase {f : Frm} {fs : List Frm} {a : Bool} {Tc : ℕ} {s : Sst}
    (hne : f.lvl ≠ [])
    (hc : RunsTo br ba z (child z f) (f :: fs) a Tc)
    (hstep : step br ba z ⟨false, a, some (frameVal br ba z (child z f)), f :: fs⟩ = s)
    (hsdone : s.done = false) :
    DoneDown br ba z ⟨false, a, none, f :: fs⟩ (Tc + 1 + 1) ∧
      (step br ba z)^[Tc + 1 + 1] ⟨false, a, none, f :: fs⟩ = s := by
  obtain ⟨hpos, hdd, hend⟩ := hc
  have hpush : step br ba z ⟨false, a, none, f :: fs⟩
      = ⟨false, a, none, child z f :: f :: fs⟩ := step_push br ba z a f fs hne
  have h1 : (step br ba z)^[Tc + 1] ⟨false, a, none, f :: fs⟩
      = ⟨false, a, some (frameVal br ba z (child z f)), f :: fs⟩ := by
    rw [Function.iterate_succ_apply, hpush, hend]
  have h2 : (step br ba z)^[Tc + 1 + 1] ⟨false, a, none, f :: fs⟩ = s := by
    rw [Function.iterate_succ_apply', h1, hstep]
  refine ⟨?_, h2⟩
  have d1 : DoneDown br ba z ⟨false, a, none, f :: fs⟩ 1 := by
    refine doneDown_succ br ba z (doneDown_zero br ba z rfl) ?_
    rw [Function.iterate_one, hpush]
  have d2 : DoneDown br ba z ⟨false, a, none, f :: fs⟩ (Tc + 1) := by
    have := doneDown_add br ba z d1 (by rw [Function.iterate_one, hpush]; exact hdd)
    rwa [Nat.add_comm 1 Tc] at this
  exact doneDown_succ br ba z d2 (by rw [h2]; exact hsdone)

/-! ## Every pushed frame comes back -/

private theorem run_aux (hz : binValLE z = 0) (n : ℕ)
    (ih : ∀ g : Frm, g.lvl.length = n → FrmOk br z g → ∀ (gs : List Frm) (a : Bool),
      ∃ T ≤ runBound z.length n, RunsTo br ba z g gs a T) :
    ∀ (M : ℕ) (f : Frm), mu f ≤ M → f.lvl.length = n + 1 → FrmOk br z f →
      ∀ (fs : List Frm) (a : Bool),
        ∃ T ≤ mu f * (runBound z.length n + 2), RunsTo br ba z f fs a T := by
  intro M
  induction M with
  | zero =>
      intro f hmu _ _ _ _
      have := mu_pos f
      omega
  | succ M IH =>
    intro f hmu hlen hok fs a
    obtain ⟨b, t, hl⟩ : ∃ b t, f.lvl = b :: t := by
      cases hlv : f.lvl with
      | nil => rw [hlv] at hlen; simp at hlen
      | cons b t => exact ⟨b, t, rfl⟩
    have hne : f.lvl ≠ [] := by rw [hl]; simp
    have htn : t.length = n := by
      have := hlen
      rw [hl, List.length_cons] at this
      omega
    have hdrop : f.lvl.length - 1 = n := by omega
    set rb := runBound z.length n with hrb
    -- the child, and the fact that it is well formed
    have hgl : (child z f).lvl.length = n := by
      rw [child_lvl, List.length_drop, hlen]
      omega
    have hgok : FrmOk br z (child z f) :=
      ⟨by rw [child_m], by rw [child_ph]; simp⟩
    obtain ⟨Tc, hTc, hcr⟩ := ih (child z f) hgl hgok (f :: fs) a
    have hmid : ∀ g : Frm, g.kind = f.kind → g.u = f.u → g.v = f.v → g.m = f.m →
        midVal br ba z t.length g = midVal br ba z t.length f := by
      intro g h1 h2 h3 h4
      rw [midVal, midVal, h1, h2, h3, h4]
    cases hph : f.ph
    · -- descending into the first half
      have hb : frameVal br ba z (child z f) = rchB br z n f.u f.m := by
        rw [frameVal_child_of_ph_false br ba z hz hph, hdrop]
      cases hb1 : rchB br z n f.u f.m
      · -- the first half failed: try the next midpoint
        cases hov : bumpOver f.m
        · set f'' : Frm := { f with ph := false, m := bumpBits f.m } with hf''
          have hstep : step br ba z ⟨false, a, some (frameVal br ba z (child z f)), f :: fs⟩
              = ⟨false, a, none, f'' :: fs⟩ := by
            rw [hb, hb1]
            exact step_ret_false_bump br ba z a f fs hov
          obtain ⟨hd, hs⟩ := child_phase br ba z hne hcr hstep rfl
          have hokv : midVal br ba z t.length f = false := by
            rw [midVal, htn, hb1, Bool.false_and]
          have hval : frameVal br ba z f'' = frameVal br ba z f := by
            rw [frameVal_of_bump br ba z hl hov, hokv, Bool.false_or]
          have hmu'' : mu f = mu f'' + 2 := by
            have h1 : mu f'' = 2 * midRem (bumpBits f.m) + 1 := by rw [hf'', mu]; simp
            have h2 : mu f = 2 * midRem f.m + 1 := mu_of_ph_false hph
            have h3 := midRem_bump hov
            omega
          have hlen'' : f''.lvl.length = n + 1 := hlen
          have hok'' : FrmOk br z f'' :=
            ⟨by rw [hf'']; simpa using hok.mlen, by rw [hf'']; simp⟩
          obtain ⟨T', hT', hr'⟩ := IH f'' (by omega) hlen'' hok'' fs a
          refine ⟨T' + (Tc + 1 + 1), ?_, runsTo_prepend br ba z hd hs hr' hval⟩
          have hexp : mu f * (rb + 2) = mu f'' * (rb + 2) + 2 * (rb + 2) := by
            rw [hmu'']; ring
          omega
        · -- the enumeration has wrapped: the frame fails
          have hokv : midVal br ba z t.length f = false := by
            rw [midVal, htn, hb1, Bool.false_and]
          have hval : frameVal br ba z f = false := by
            rw [frameVal_of_last br ba z hl hov, hokv]
          have hstep : step br ba z ⟨false, a, some (frameVal br ba z (child z f)), f :: fs⟩
              = ⟨false, a, some (frameVal br ba z f), fs⟩ := by
            rw [hb, hb1, hval]
            exact step_ret_false_over br ba z a f fs hov
          obtain ⟨hd, hs⟩ := child_phase br ba z hne hcr hstep rfl
          refine ⟨Tc + 1 + 1, ?_, by omega, hd, hs⟩
          have hmuf : 3 ≤ mu f := by
            have h2 : mu f = 2 * midRem f.m + 1 := mu_of_ph_false hph
            rw [midRem_of_over hov] at h2
            omega
          calc Tc + 1 + 1 ≤ rb + 2 := by omega
            _ ≤ 3 * (rb + 2) := by omega
            _ ≤ mu f * (rb + 2) := Nat.mul_le_mul_right _ hmuf
      · -- the first half succeeded: advance the phase
        set f' : Frm := { f with ph := true } with hf'
        have hstep : step br ba z ⟨false, a, some (frameVal br ba z (child z f)), f :: fs⟩
            = ⟨false, a, none, f' :: fs⟩ := by
          rw [hb, hb1]
          exact step_ret_true_of_ph_false br ba z a f fs hph
        obtain ⟨hd, hs⟩ := child_phase br ba z hne hcr hstep rfl
        have hval : frameVal br ba z f' = frameVal br ba z f := rfl
        have hmu' : mu f = mu f' + 1 := by
          have h1 : mu f' = 2 * midRem f.m := by rw [hf', mu]; simp
          have h2 : mu f = 2 * midRem f.m + 1 := mu_of_ph_false hph
          omega
        have hok' : FrmOk br z f' :=
          ⟨hok.mlen, by intro _; rw [hf', hdrop]; exact hb1⟩
        obtain ⟨T', hT', hr'⟩ := IH f' (by omega) hlen hok' fs a
        refine ⟨T' + (Tc + 1 + 1), ?_, runsTo_prepend br ba z hd hs hr' hval⟩
        have hexp : mu f * (rb + 2) = mu f' * (rb + 2) + (rb + 2) := by
          rw [hmu']; ring
        omega
    · -- descending into the second half
      have hb : frameVal br ba z (child z f)
          = (if f.kind then accB br ba z n f.m else rchB br z n f.m f.v) := by
        rw [frameVal_child_of_ph_true br ba z hz hph, hdrop]
      have hfirst : rchB br z t.length f.u f.m = true := by
        have := hok.phase hph
        rwa [hdrop, ← htn] at this
      have hmv : midVal br ba z t.length f
          = (if f.kind then accB br ba z n f.m else rchB br z n f.m f.v) := by
        rw [midVal, hfirst, Bool.true_and, htn]
      cases hb2 : (if f.kind then accB br ba z n f.m else rchB br z n f.m f.v)
      · cases hov : bumpOver f.m
        · set f'' : Frm := { f with ph := false, m := bumpBits f.m } with hf''
          have hstep : step br ba z ⟨false, a, some (frameVal br ba z (child z f)), f :: fs⟩
              = ⟨false, a, none, f'' :: fs⟩ := by
            rw [hb, hb2]
            exact step_ret_false_bump br ba z a f fs hov
          obtain ⟨hd, hs⟩ := child_phase br ba z hne hcr hstep rfl
          have hokv : midVal br ba z t.length f = false := by rw [hmv, hb2]
          have hval : frameVal br ba z f'' = frameVal br ba z f := by
            rw [frameVal_of_bump br ba z hl hov, hokv, Bool.false_or]
          have hmu'' : mu f = mu f'' + 1 := by
            have h1 : mu f'' = 2 * midRem (bumpBits f.m) + 1 := by rw [hf'', mu]; simp
            have h2 : mu f = 2 * midRem f.m := mu_of_ph_true hph
            have h3 := midRem_bump hov
            omega
          have hok'' : FrmOk br z f'' :=
            ⟨by rw [hf'']; simpa using hok.mlen, by rw [hf'']; simp⟩
          obtain ⟨T', hT', hr'⟩ := IH f'' (by omega) hlen hok'' fs a
          refine ⟨T' + (Tc + 1 + 1), ?_, runsTo_prepend br ba z hd hs hr' hval⟩
          have hexp : mu f * (rb + 2) = mu f'' * (rb + 2) + (rb + 2) := by
            rw [hmu'']; ring
          omega
        · have hokv : midVal br ba z t.length f = false := by rw [hmv, hb2]
          have hval : frameVal br ba z f = false := by
            rw [frameVal_of_last br ba z hl hov, hokv]
          have hstep : step br ba z ⟨false, a, some (frameVal br ba z (child z f)), f :: fs⟩
              = ⟨false, a, some (frameVal br ba z f), fs⟩ := by
            rw [hb, hb2, hval]
            exact step_ret_false_over br ba z a f fs hov
          obtain ⟨hd, hs⟩ := child_phase br ba z hne hcr hstep rfl
          refine ⟨Tc + 1 + 1, ?_, by omega, hd, hs⟩
          have hmuf : 2 ≤ mu f := by
            have h2 : mu f = 2 * midRem f.m := mu_of_ph_true hph
            rw [midRem_of_over hov] at h2
            omega
          calc Tc + 1 + 1 ≤ rb + 2 := by omega
            _ ≤ 2 * (rb + 2) := by omega
            _ ≤ mu f * (rb + 2) := Nat.mul_le_mul_right _ hmuf
      · have hval : frameVal br ba z f = true :=
          frameVal_of_mid br ba z hl (by rw [hmv, hb2])
        have hstep : step br ba z ⟨false, a, some (frameVal br ba z (child z f)), f :: fs⟩
            = ⟨false, a, some (frameVal br ba z f), fs⟩ := by
          rw [hb, hb2, hval]
          exact step_ret_true_ph br ba z a f fs hph
        obtain ⟨hd, hs⟩ := child_phase br ba z hne hcr hstep rfl
        refine ⟨Tc + 1 + 1, ?_, by omega, hd, hs⟩
        have hmuf : 2 ≤ mu f := by
          have h2 : mu f = 2 * midRem f.m := mu_of_ph_true hph
          have := midRem_pos f.m
          omega
        calc Tc + 1 + 1 ≤ rb + 2 := by omega
          _ ≤ 2 * (rb + 2) := by omega
          _ ≤ mu f * (rb + 2) := Nat.mul_le_mul_right _ hmuf

/-- **Every pushed frame comes back.** A frame at level `n` is popped again,
carrying its value, within `runBound` steps, and the done flag stays down for
the whole of that run. -/
theorem run_frame (hz : binValLE z = 0) :
    ∀ (n : ℕ) (f : Frm), f.lvl.length = n → FrmOk br z f → ∀ (fs : List Frm) (a : Bool),
      ∃ T ≤ runBound z.length n, RunsTo br ba z f fs a T := by
  intro n
  induction n with
  | zero =>
      intro f hlen _ fs a
      have hl : f.lvl = [] := List.length_eq_zero_iff.mp hlen
      have hstep : step br ba z ⟨false, a, none, f :: fs⟩
          = ⟨false, a, some (frameVal br ba z f), fs⟩ := by
        rw [frameVal_of_nil br ba z hl]
        exact step_base br ba z a f fs hl
      refine ⟨1, by rw [runBound], Nat.one_pos, ?_, by rw [Function.iterate_one, hstep]⟩
      exact doneDown_succ br ba z (doneDown_zero br ba z rfl)
        (by rw [Function.iterate_one, hstep])
  | succ n IH =>
      intro f hlen hok fs a
      obtain ⟨T, hT, hr⟩ := run_aux br ba z hz n IH (mu f) f le_rfl hlen hok fs a
      refine ⟨T, ?_, hr⟩
      rw [runBound]
      exact le_trans hT (Nat.mul_le_mul_right _ (mu_le z hok.mlen))

/-! ## The enumeration covers every candidate -/

theorem anyMid_of_lt {P : List Bool → Bool} {m : List Bool} {i j : ℕ} (hij : i < j)
    (h : P (bumpBits^[i] m) = true) : anyMid P m j = true := by
  induction j generalizing m i with
  | zero => omega
  | succ j ih =>
      rw [anyMid_succ]
      cases i with
      | zero => rw [Function.iterate_zero_apply] at h; rw [h]; rfl
      | succ i =>
          rw [Function.iterate_succ_apply] at h
          rw [ih (by omega) h, Bool.or_true]

theorem exists_of_anyMid {P : List Bool → Bool} {m : List Bool} {j : ℕ}
    (h : anyMid P m j = true) : ∃ i < j, P (bumpBits^[i] m) = true := by
  induction j generalizing m with
  | zero => simp at h
  | succ j ih =>
      rw [anyMid_succ, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨0, by omega, by simpa using h⟩
      · obtain ⟨i, hi, hP⟩ := ih h
        exact ⟨i + 1, by omega, by rwa [Function.iterate_succ_apply]⟩

/-- **Every string of the enumeration's width is tried.** -/
theorem anyMid_of_length {P : List Bool → Bool} {z w : List Bool} (hz : binValLE z = 0)
    (hw : w.length = z.length) (h : P w = true) : anyMid P z (2 ^ z.length) = true := by
  have hzb : bitsOfLenLE z.length 0 = z := by
    have := bitsOfLenLE_binValLE z
    rwa [hz] at this
  have hv : binValLE w < 2 ^ z.length := by
    have := binValLE_lt w
    rwa [hw] at this
  have hstep : bumpBits^[binValLE w] z = w := by
    have := bumpBits_iterate z.length (binValLE w) hv
    rw [hzb] at this
    rw [this, ← hw, bitsOfLenLE_binValLE]
  exact anyMid_of_lt hv (by rw [hstep]; exact h)

/-! ## The stack invariant the encoding needs -/

/-- Nothing is returning only while the stack is nonempty. -/
def StkOk (s : Sst) : Prop := s.stk = [] → s.ret ≠ none

theorem step_stkOk {s : Sst} (h : StkOk s) : StkOk (step br ba z s) := by
  obtain ⟨d, a, r, stk⟩ := s
  cases d
  · cases stk with
    | nil =>
        obtain ⟨b, rfl⟩ : ∃ b, r = some b := by
          cases r with
          | none => exact absurd rfl (h rfl)
          | some b => exact ⟨b, rfl⟩
        rw [step_of_empty]
        intro _
        simp
    | cons f fs =>
      cases r with
      | none =>
          by_cases hl : f.lvl = []
          · rw [step_base _ _ _ a f fs hl]
            intro _
            simp
          · rw [step_push _ _ _ a f fs hl]
            intro hc
            simp at hc
      | some b =>
          cases b
          · cases hov : bumpOver f.m
            · rw [step_ret_false_bump _ _ _ a f fs hov]
              intro hc
              simp at hc
            · rw [step_ret_false_over _ _ _ a f fs hov]
              intro _
              simp
          · cases hp : f.ph
            · rw [step_ret_true_of_ph_false _ _ _ a f fs hp]
              intro hc
              simp at hc
            · rw [step_ret_true_ph _ _ _ a f fs hp]
              intro _
              simp
  · rw [step_of_done]
    exact h

/-! ## The number of steps is at most exponential in a polynomial -/

theorem runBound_pos (W : ℕ) : ∀ n, 0 < runBound W n := by
  intro n
  induction n with
  | zero => rw [runBound]; omega
  | succ n ih =>
      rw [runBound]
      have : 0 < 2 * 2 ^ W + 1 := by omega
      exact Nat.mul_pos this (by omega)

theorem runBound_le (W : ℕ) : ∀ n, runBound W n + 2 ≤ 2 ^ ((W + 3) * n + 2) := by
  intro n
  induction n with
  | zero => rw [runBound]; norm_num
  | succ n ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ W := Nat.one_le_two_pow
      have hA : 2 * 2 ^ W + 2 ≤ 2 ^ (W + 3) := by
        have h8 : 2 ^ (W + 3) = 8 * 2 ^ W := by rw [pow_add]; ring
        omega
      have hc : 2 ≤ runBound W n + 2 := by omega
      have hstep : runBound W (n + 1) + 2 ≤ (2 * 2 ^ W + 2) * (runBound W n + 2) := by
        rw [runBound]
        calc (2 * 2 ^ W + 1) * (runBound W n + 2) + 2
            ≤ (2 * 2 ^ W + 1) * (runBound W n + 2) + (runBound W n + 2) := by omega
          _ = (2 * 2 ^ W + 2) * (runBound W n + 2) := by ring
      calc runBound W (n + 1) + 2
          ≤ (2 * 2 ^ W + 2) * (runBound W n + 2) := hstep
        _ ≤ 2 ^ (W + 3) * 2 ^ ((W + 3) * n + 2) := Nat.mul_le_mul hA ih
        _ = 2 ^ ((W + 3) * (n + 1) + 2) := by rw [← pow_add]; ring_nf

/-! ## The whole run -/

/-- **The recursion terminates with its answer.** From the state carrying one
frame, the machine keeps its done flag down for `T` steps, raises it on the next
one, and one step later the flag *is* the answer. -/
theorem run_top (hz : binValLE z = 0) (root : Frm) (hok : FrmOk br z root) :
    ∃ T ≤ runBound z.length root.lvl.length,
      (∀ j ≤ T, ((step br ba z)^[j] ⟨false, false, none, [root]⟩).done = false) ∧
      (step br ba z)^[T + 1] ⟨false, false, none, [root]⟩
        = ⟨true, frameVal br ba z root, some (frameVal br ba z root), []⟩ ∧
      (step br ba z)^[T + 2] ⟨false, false, none, [root]⟩
        = ⟨frameVal br ba z root, frameVal br ba z root, some (frameVal br ba z root), []⟩ := by
  obtain ⟨T, hT, hpos, hdd, hend⟩ :=
    run_frame br ba z hz root.lvl.length root rfl hok [] false
  have h1 : (step br ba z)^[T + 1] ⟨false, false, none, [root]⟩
      = ⟨true, frameVal br ba z root, some (frameVal br ba z root), []⟩ := by
    rw [Function.iterate_succ_apply', hend, step_of_empty]
    rfl
  refine ⟨T, hT, hdd, h1, ?_⟩
  rw [show T + 2 = T + 1 + 1 from rfl, Function.iterate_succ_apply', h1, step_of_done]

/-! ## The size of the state -/

/-- The three codes a frame carries fit in `Wm` bits. -/
def FrmSize (Wm : ℕ) (f : Frm) : Prop :=
  f.u.length ≤ Wm ∧ f.v.length ≤ Wm ∧ f.m.length ≤ Wm

/-- The stack descends exactly one level per frame — which is what bounds its
depth — and every frame's codes fit. -/
def StkSize (Lmax Wm : ℕ) : List Frm → Prop
  | [] => True
  | f :: fs => fs.length + f.lvl.length = Lmax ∧ FrmSize Wm f ∧ StkSize Lmax Wm fs

theorem StkSize.length_le {Lmax Wm : ℕ} :
    ∀ {stk : List Frm}, StkSize Lmax Wm stk → stk.length ≤ Lmax + 1
  | [], _ => by simp
  | f :: fs, h => by
      rw [List.length_cons]
      have := h.1
      omega

theorem StkSize.mem_bound {Lmax Wm : ℕ} :
    ∀ {stk : List Frm}, StkSize Lmax Wm stk →
      ∀ f ∈ stk, f.lvl.length ≤ Lmax ∧ FrmSize Wm f
  | [], _ => by simp
  | g :: fs, h => by
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨by have := h.1; omega, h.2.1⟩
      · exact StkSize.mem_bound h.2.2 f hf

theorem step_stkSize {Lmax Wm : ℕ} {s : Sst} (hzw : z.length ≤ Wm)
    (h : StkSize Lmax Wm s.stk) : StkSize Lmax Wm (step br ba z s).stk := by
  obtain ⟨d, a, r, stk⟩ := s
  cases d
  · cases stk with
    | nil => cases r <;> simp [step, StkSize]
    | cons f fs =>
      obtain ⟨hd, hfs, hrest⟩ := h
      cases r with
      | none =>
          by_cases hl : f.lvl = []
          · rw [step_base _ _ _ a f fs hl]
            exact hrest
          · rw [step_push _ _ _ a f fs hl]
            have hpos : 1 ≤ f.lvl.length := by
              cases hlv : f.lvl with
              | nil => exact absurd hlv hl
              | cons _ t => simp
            refine ⟨?_, ?_, hd, hfs, hrest⟩
            · rw [child_lvl, List.length_drop, List.length_cons]
              omega
            · rw [FrmSize, child_m]
              refine ⟨?_, ?_, hzw⟩ <;> rw [child] <;> split_ifs <;>
                first
                  | exact hfs.1
                  | exact hfs.2.1
                  | exact hfs.2.2
                  | exact hzw
      | some b =>
          cases b
          · cases hov : bumpOver f.m
            · rw [step_ret_false_bump _ _ _ a f fs hov]
              exact ⟨hd, ⟨hfs.1, hfs.2.1, by rw [bumpBits_length]; exact hfs.2.2⟩, hrest⟩
            · rw [step_ret_false_over _ _ _ a f fs hov]
              exact hrest
          · cases hp : f.ph
            · rw [step_ret_true_of_ph_false _ _ _ a f fs hp]
              exact ⟨hd, hfs, hrest⟩
            · rw [step_ret_true_ph _ _ _ a f fs hp]
              exact hrest
  · rw [step_of_done]
    exact h

theorem iterate_stkSize {Lmax Wm : ℕ} (hzw : z.length ≤ Wm) :
    ∀ (j : ℕ) (s : Sst), StkSize Lmax Wm s.stk →
      StkSize Lmax Wm ((step br ba z)^[j] s).stk := by
  intro j
  induction j with
  | zero => intro s h; exact h
  | succ j ih =>
      intro s h
      rw [Function.iterate_succ_apply]
      exact ih _ (step_stkSize br ba z hzw h)

end Sav
end Complexity
