import Complexitylib.Circuits.Family.Defs
import Complexitylib.Asymptotics

namespace Complexity

/-!
# Boolean circuit families

This module provides the public API for circuit-family semantics, concrete
size/depth bounds, and the equivalence between pointwise polynomial bounds and
the power big-O convention used by complexity classes.
-/

namespace Circuit

variable {B : Basis} {N G : ℕ} [NeZero N]

theorem computes_congr (c : Circuit B N 1 G) {f g : BitString N → Bool}
    (h : f = g) : c.Computes f ↔ c.Computes g := by
  subst g
  rfl

theorem computesOnLength_congr (c : Circuit B N 1 G) {f g : BoolFunFamily}
    (h : f N = g N) : c.ComputesOnLength f ↔ c.ComputesOnLength g :=
  c.computes_congr h

theorem Computes.apply {c : Circuit B N 1 G} {f : BitString N → Bool}
    (h : c.Computes f) (x : BitString N) :
    (c.eval x) 0 = f x :=
  congrFun h x

theorem ComputesOnLength.apply {c : Circuit B N 1 G} {f : BoolFunFamily}
    (h : c.ComputesOnLength f) (x : BitString N) :
    (c.eval x) 0 = f N x :=
  Circuit.Computes.apply h x

theorem Computes.size_complexity_le {c : Circuit B N 1 G}
    {f : BitString N → Bool} (h : c.Computes f) :
    size_complexity B f ≤ c.size :=
  Circuit.size_complexity_le c f h

end Circuit

namespace CircuitFamily

variable {B : Basis}

@[simp] theorem function_zero (F : CircuitFamily B) (x : BitString 0) :
    F.function 0 x = F.emptyOutput := rfl

@[simp] theorem function_succ (F : CircuitFamily B) (n : ℕ)
    (x : BitString (n + 1)) :
    F.function (n + 1) x = (F.circuit (n + 1)).eval x 0 := rfl

@[simp] theorem size_zero (F : CircuitFamily B) : F.size 0 = 0 := rfl

@[simp] theorem size_succ (F : CircuitFamily B) (n : ℕ) :
    F.size (n + 1) = (F.circuit (n + 1)).size := rfl

@[simp] theorem depth_zero (F : CircuitFamily B) : F.depth 0 = 0 := rfl

@[simp] theorem depth_succ (F : CircuitFamily B) (n : ℕ) :
    F.depth (n + 1) = (F.circuit (n + 1)).depth := rfl

theorem sizeBoundedBy_mono (F : CircuitFamily B) {s t : ℕ → ℕ}
    (hF : F.SizeBoundedBy s) (hst : ∀ n, s n ≤ t n) :
    F.SizeBoundedBy t :=
  fun n => (hF n).trans (hst n)

theorem depthBoundedBy_mono (F : CircuitFamily B) {d e : ℕ → ℕ}
    (hF : F.DepthBoundedBy d) (hde : ∀ n, d n ≤ e n) :
    F.DepthBoundedBy e :=
  fun n => (hF n).trans (hde n)

section BigO

open Complexity

theorem SizeBoundedBy.bigO {F : CircuitFamily B} {s : ℕ → ℕ}
    (h : F.SizeBoundedBy s) : F.size =O s :=
  Complexity.BigO.of_le h

/-- Pointwise polynomial size is equivalent to a big-O power bound. -/
theorem polynomialSize_iff_bigO (F : CircuitFamily B) :
    F.PolynomialSize ↔ ∃ k, F.size =O ((· ^ k) : ℕ → ℕ) := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.natDegree, Complexity.BigO.of_polynomial_bound p hp⟩
  · rintro ⟨k, hk⟩
    obtain ⟨p, hp⟩ := Complexity.BigO.pow_polynomial_bound hk
    exact ⟨p, hp⟩

end BigO

theorem computes_congr (F : CircuitFamily B) {f g : BoolFunFamily}
    (h : f = g) : F.Computes f ↔ F.Computes g := by
  subst g
  rfl

theorem computes_unique (F : CircuitFamily B) {f g : BoolFunFamily}
    (hf : F.Computes f) (hg : F.Computes g) : f = g :=
  hf.symm.trans hg

/-- Evaluating the serialized fixed-length input agrees with family
    evaluation at that length. -/
@[simp] theorem evalList_ofFn (F : CircuitFamily B) {n : ℕ}
    (x : BitString n) :
    F.evalList (List.ofFn x) = F.function n x := by
  unfold evalList
  have h := List.equivSigmaTuple.apply_symm_apply
    (⟨n, x⟩ : Σ n, BitString n)
  exact congrArg (fun p : Σ n, BitString n => F.function p.1 p.2) h

@[simp] theorem evalList_toList (F : CircuitFamily B) {n : ℕ}
    (x : BitString n) : F.evalList x.toList = F.function n x :=
  F.evalList_ofFn x

@[simp] theorem evalList_nil (F : CircuitFamily B) :
    F.evalList [] = F.emptyOutput := rfl

theorem Computes.apply {F : CircuitFamily B} {f : BoolFunFamily}
    (h : F.Computes f) (n : ℕ) (x : BitString n) :
    F.function n x = f n x := by
  rw [h]

theorem Computes.evalList {F : CircuitFamily B} {f : BoolFunFamily}
    (h : F.Computes f) (x : List Bool) :
    F.evalList x = f x.length x.get :=
  h.apply x.length x.get

end CircuitFamily

end Complexity
