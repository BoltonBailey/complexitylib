/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.TQBFSavitch
public import Complexitylib.Classes.Interactive.Internal.ShenWF

/-!
# Savitch's recursion as a prenex CNF formula

⚠️ Unreviewed by Bolton

Over an abstract configuration space — blocks of `W` bits, a validity predicate, a one-step
relation with `Ws` bits of scratch, and an acceptance predicate, each given by a formula —
`savitchQBF` is the prenex formula `∃A ∃B ∃M_k ∀U_k ∀V_k … ∃M_1 ∀U_1 ∀V_1 ∃scratch ∃aux. CNF`
whose matrix is the Tseitin encoding of

`A = init ∧ valid B ∧ acc B ∧ valid M_k ∧ (cond_k → valid M_{k-1} ∧ (… → base U_1 V_1))`

with `cond_ℓ := (U_ℓ = A_ℓ ∧ V_ℓ = M_ℓ) ∨ (U_ℓ = M_ℓ ∧ V_ℓ = B_ℓ)`. It is true exactly when some
valid accepting block is reachable from `init` in `2 ^ k` steps through valid blocks
(`isTrue_savitchQBF_iff`).

## Main definitions

- `SavitchData` — the abstract configuration space and its formulas
- `SavitchData.ReachPow`, `SavitchData.matrixF`, `SavitchData.prefixF`, `SavitchData.savitchQBF`

## Main results

- `SavitchData.eval_level` — the recursion, level by level
- `SavitchData.isTrue_savitchQBF_iff`
-/

@[expose] public section

namespace Complexity

open QBF Shen

/-- An abstract configuration space with its formulas. -/
structure SavitchData (W Ws : ℕ) where
  /-- The valid blocks. -/
  Valid : (Fin W → Bool) → Prop
  /-- One step (or none), with scratch bits. -/
  Base : (Fin W → Bool) → (Fin W → Bool) → (Fin Ws → Bool) → Prop
  /-- The accepting blocks. -/
  Acc : (Fin W → Bool) → Prop
  /-- The validity formula of the block at an offset. -/
  validF : ℕ → QBF
  /-- The step formula of two blocks with scratch at a third offset. -/
  baseF : ℕ → ℕ → ℕ → QBF
  /-- The acceptance formula of a block. -/
  accF : ℕ → QBF
  validF_qf : ∀ off, QuantifierFree (validF off)
  validF_vars : ∀ off i, i ∈ freeVars (validF off) → off ≤ i ∧ i < off + W
  validF_eval : ∀ α off, eval α (validF off) = true ↔ Valid (blockOf W α off)
  baseF_qf : ∀ u v s, QuantifierFree (baseF u v s)
  baseF_vars : ∀ u v s i, i ∈ freeVars (baseF u v s) →
    (u ≤ i ∧ i < u + W) ∨ (v ≤ i ∧ i < v + W) ∨ (s ≤ i ∧ i < s + Ws)
  baseF_eval : ∀ α u v s, Valid (blockOf W α u) → Valid (blockOf W α v) →
    (eval α (baseF u v s) = true ↔ Base (blockOf W α u) (blockOf W α v) (blockOf Ws α s))
  accF_qf : ∀ off, QuantifierFree (accF off)
  accF_vars : ∀ off i, i ∈ freeVars (accF off) → off ≤ i ∧ i < off + W
  accF_eval : ∀ α off, eval α (accF off) = true ↔ Acc (blockOf W α off)

namespace SavitchData

variable {W Ws : ℕ} (D : SavitchData W Ws)

/-! ## Reachability in `2 ^ k` steps -/

/-- Reachability in exactly `2 ^ k` steps (a step may stay put), through valid blocks. -/
def ReachPow : ℕ → (Fin W → Bool) → (Fin W → Bool) → Prop
  | 0, u, v => D.Valid u ∧ D.Valid v ∧ ∃ σ, D.Base u v σ
  | k + 1, u, v => ∃ m, ReachPow k u m ∧ ReachPow k m v

theorem ReachPow.valid_left : ∀ (k : ℕ) {u v : Fin W → Bool}, D.ReachPow k u v → D.Valid u
  | 0, _, _, h => h.1
  | k + 1, _, _, ⟨_, h, _⟩ => ReachPow.valid_left k h

theorem ReachPow.valid_right : ∀ (k : ℕ) {u v : Fin W → Bool}, D.ReachPow k u v → D.Valid v
  | 0, _, _, h => h.2.1
  | k + 1, _, _, ⟨_, _, h⟩ => ReachPow.valid_right k h

/-! ## The formulas -/

/-- The condition of a level: the pair `(U, V)` is `(A, M)` or `(M, B)`. -/
def condF (W u v a m b : ℕ) : QBF :=
  disj (conj (eqF W u a) (eqF W v m)) (conj (eqF W u m) (eqF W v b))

theorem eval_condF_iff (α : ℕ → Bool) (u v a m b : ℕ) :
    eval α (condF W u v a m b) = true ↔
      (blockOf W α u = blockOf W α a ∧ blockOf W α v = blockOf W α m) ∨
        (blockOf W α u = blockOf W α m ∧ blockOf W α v = blockOf W α b) := by
  simp only [condF, eval_disj, eval_conj, Bool.or_eq_true, Bool.and_eq_true, eval_eqF_iff]

theorem quantifierFree_condF (u v a m b : ℕ) : QuantifierFree (condF W u v a m b) := by
  have h1 := quantifierFree_eqF W u a
  have h2 := quantifierFree_eqF W v m
  have h3 := quantifierFree_eqF W u m
  have h4 := quantifierFree_eqF W v b
  simp only [QuantifierFree, quantDepth, condF, Nat.max_eq_zero_iff] at *
  exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem mem_freeVars_condF (u v a m b i : ℕ) (hi : i ∈ freeVars (condF W u v a m b)) :
    (u ≤ i ∧ i < u + W) ∨ (v ≤ i ∧ i < v + W) ∨ (a ≤ i ∧ i < a + W) ∨
      (m ≤ i ∧ i < m + W) ∨ (b ≤ i ∧ i < b + W) := by
  simp only [condF, freeVars, Finset.mem_union] at hi
  rcases hi with (h | h) | (h | h) <;> rcases mem_freeVars_eqF _ _ _ _ h with h | h <;> tauto

/-- The matrix of `k` levels: blocks `a`, `b`, next free offset `nxt`, scratch at `s`. -/
def matrixF (s : ℕ) : ℕ → ℕ → ℕ → ℕ → QBF
  | 0, a, b, _ => D.baseF a b s
  | k + 1, a, b, nxt =>
      conj (D.validF nxt)
        (disj (neg (condF W (nxt + W) (nxt + 2 * W) a nxt b))
          (matrixF s k (nxt + W) (nxt + 2 * W) (nxt + 3 * W)))

/-- The prefix of `k` levels starting at `nxt`: `∃M ∀U ∀V` per level. -/
def prefixF (W : ℕ) : ℕ → ℕ → Prefix
  | 0, _ => []
  | k + 1, nxt =>
      blockQ false nxt W ++ blockQ true (nxt + W) W ++ blockQ true (nxt + 2 * W) W ++
        prefixF W k (nxt + 3 * W)

theorem mem_blockQ (q : Bool) (off n : ℕ) (p : Bool × ℕ) (hp : p ∈ blockQ q off n) :
    p.1 = q ∧ off ≤ p.2 ∧ p.2 < off + n := by
  rw [blockQ, List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  rw [List.mem_range] at hi
  exact ⟨rfl, by simp, by simp; omega⟩

theorem mem_prefixF (W : ℕ) : ∀ (k nxt : ℕ) (p : Bool × ℕ), p ∈ prefixF W k nxt →
    nxt ≤ p.2 ∧ p.2 < nxt + 3 * W * k
  | 0, _, _, hp => by simp [prefixF] at hp
  | k + 1, nxt, p, hp => by
      simp only [prefixF, List.mem_append] at hp
      rcases hp with ((hp | hp) | hp) | hp
      · have := mem_blockQ _ _ _ _ hp
        constructor <;> nlinarith [this.2.1, this.2.2]
      · have := mem_blockQ _ _ _ _ hp
        constructor <;> nlinarith [this.2.1, this.2.2]
      · have := mem_blockQ _ _ _ _ hp
        constructor <;> nlinarith [this.2.1, this.2.2]
      · have := mem_prefixF W k _ p hp
        constructor <;> nlinarith [this.1, this.2]

theorem quantifierFree_matrixF (s : ℕ) : ∀ (k a b nxt : ℕ),
    QuantifierFree (D.matrixF s k a b nxt)
  | 0, a, b, _ => D.baseF_qf a b s
  | k + 1, a, b, nxt => by
      have h1 := D.validF_qf nxt
      have h2 := quantifierFree_condF (W := W) (nxt + W) (nxt + 2 * W) a nxt b
      have h3 := quantifierFree_matrixF s k (nxt + W) (nxt + 2 * W) (nxt + 3 * W)
      simp only [QuantifierFree, quantDepth, matrixF, Nat.max_eq_zero_iff] at *
      exact ⟨h1, h2, h3⟩

/-- Every variable of the matrix is in the blocks `a`, `b`, the levels' blocks, or the scratch. -/
theorem mem_freeVars_matrixF (s : ℕ) : ∀ (k a b nxt i : ℕ), i ∈ freeVars (D.matrixF s k a b nxt) →
    (a ≤ i ∧ i < a + W) ∨ (b ≤ i ∧ i < b + W) ∨ (nxt ≤ i ∧ i < nxt + 3 * W * k) ∨
      (s ≤ i ∧ i < s + Ws)
  | 0, a, b, nxt, i, hi => by
      rcases D.baseF_vars a b s i hi with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  | k + 1, a, b, nxt, i, hi => by
      simp only [matrixF, freeVars, Finset.mem_union] at hi
      rcases hi with h | h | h
      · have := D.validF_vars nxt i h
        right; right; left
        constructor <;> nlinarith [this.1, this.2]
      · rcases mem_freeVars_condF _ _ _ _ _ _ h with h | h | h | h | h
        · right; right; left; constructor <;> nlinarith [h.1, h.2]
        · right; right; left; constructor <;> nlinarith [h.1, h.2]
        · exact Or.inl h
        · right; right; left; constructor <;> nlinarith [h.1, h.2]
        · exact Or.inr (Or.inl h)
      · rcases mem_freeVars_matrixF s k _ _ _ i h with h | h | h | h
        · right; right; left; constructor <;> nlinarith [h.1, h.2]
        · right; right; left; constructor <;> nlinarith [h.1, h.2]
        · right; right; left; constructor <;> nlinarith [h.1, h.2]
        · exact Or.inr (Or.inr (Or.inr h))

/-! ## Assignments with a block replaced -/

/-- `α` with the block at `off` set to `c`. -/
def setBlock (α : ℕ → Bool) (off : ℕ) (c : Fin W → Bool) : ℕ → Bool := fun i =>
  if h : off ≤ i ∧ i < off + W then c ⟨i - off, by omega⟩ else α i

theorem setBlock_agree (α : ℕ → Bool) (off : ℕ) (c : Fin W → Bool) :
    ∀ i, (i < off ∨ off + W ≤ i) → setBlock α off c i = α i := by
  intro i hi
  rw [setBlock, dif_neg (by omega)]

theorem blockOf_setBlock_self (α : ℕ → Bool) (off : ℕ) (c : Fin W → Bool) :
    blockOf W (setBlock α off c) off = c := by
  funext i
  rw [blockOf, setBlock, dif_pos (by omega)]
  congr 1
  ext
  simp

theorem blockOf_of_agree_below (α β : ℕ → Bool) (off n : ℕ) (hoff : off + W ≤ n)
    (h : ∀ i, i < n → β i = α i) : blockOf W β off = blockOf W α off :=
  blockOf_eq_of_agree W α β off fun i _ hi => h i (by omega)

/-! ## The level recursion -/

/-- `toQBF` respects pointwise equivalence of the matrix. -/
theorem eval_toQBF_congr : ∀ (qs : Prefix) (ψ₁ ψ₂ : QBF), (∀ α, eval α ψ₁ = eval α ψ₂) →
    ∀ α, eval α (toQBF qs ψ₁) = eval α (toQBF qs ψ₂)
  | [], _, _, h, α => h α
  | (b, i) :: qs, ψ₁, ψ₂, h, α => by
      cases b <;> simp only [toQBF, eval] <;>
        rw [eval_toQBF_congr qs ψ₁ ψ₂ h, eval_toQBF_congr qs ψ₁ ψ₂ h]

/-- **The recursion.** For valid blocks `A`, `B` below the level's offsets, and the scratch
beyond every level, the level formula says `B` is reached from `A` in `2 ^ k` steps. -/
theorem eval_level (s : ℕ) : ∀ (k a b nxt : ℕ) (α : ℕ → Bool),
    a + W ≤ nxt → b + W ≤ nxt → nxt + 3 * W * k ≤ s →
    D.Valid (blockOf W α a) → D.Valid (blockOf W α b) →
    (eval α (toQBF (prefixF W k nxt) (exs s Ws (D.matrixF s k a b nxt))) = true ↔
      D.ReachPow k (blockOf W α a) (blockOf W α b))
  | 0, a, b, nxt, α, ha, hb, hs, hva, hvb => by
      simp only [prefixF, toQBF, matrixF, ReachPow, eval_exs_iff]
      constructor
      · rintro ⟨β, hβ, h⟩
        have hA : blockOf W β a = blockOf W α a :=
          blockOf_eq_of_agree W α β a fun i _ hi => hβ i (by omega)
        have hB : blockOf W β b = blockOf W α b :=
          blockOf_eq_of_agree W α β b fun i _ hi => hβ i (by omega)
        rw [D.baseF_eval β a b s (by rw [hA]; exact hva) (by rw [hB]; exact hvb), hA, hB] at h
        exact ⟨hva, hvb, blockOf Ws β s, h⟩
      · rintro ⟨-, -, σ, h⟩
        refine ⟨setBlock (W := Ws) α s σ, setBlock_agree α s σ, ?_⟩
        have hA : blockOf W (setBlock (W := Ws) α s σ) a = blockOf W α a :=
          blockOf_eq_of_agree W α _ a fun i _ hi => setBlock_agree α s σ i (by omega)
        have hB : blockOf W (setBlock (W := Ws) α s σ) b = blockOf W α b :=
          blockOf_eq_of_agree W α _ b fun i _ hi => setBlock_agree α s σ i (by omega)
        rw [D.baseF_eval _ a b s (by rw [hA]; exact hva) (by rw [hB]; exact hvb), hA, hB,
          blockOf_setBlock_self]
        exact h
  | k + 1, a, b, nxt, α, ha, hb, hs, hva, hvb => by
      have hs' : nxt + 3 * W + 3 * W * k ≤ s := by nlinarith
      obtain ⟨BODY, hBODY⟩ : ∃ BODY, BODY = conj (D.validF nxt)
          (disj (neg (condF W (nxt + W) (nxt + 2 * W) a nxt b))
            (D.matrixF s k (nxt + W) (nxt + 2 * W) (nxt + 3 * W))) := ⟨_, rfl⟩
      have hfold : toQBF (prefixF W (k + 1) nxt) (exs s Ws (D.matrixF s (k + 1) a b nxt))
          = exs nxt W (toQBF (blockQ true (nxt + W) W)
              (toQBF (blockQ true (nxt + 2 * W) W)
                (toQBF (prefixF W k (nxt + 3 * W) ++ blockQ false s Ws) BODY))) := by
        rw [hBODY, prefixF, matrixF, toQBF_append, toQBF_append, toQBF_append, toQBF_append,
          toQBF_blockQ_false, toQBF_blockQ_false]
      have hinner : ∀ δ : ℕ → Bool,
          eval δ (toQBF (prefixF W k (nxt + 3 * W) ++ blockQ false s Ws) BODY) = true ↔
          (D.Valid (blockOf W δ nxt) ∧
            (((blockOf W δ (nxt + W) = blockOf W δ a ∧
                blockOf W δ (nxt + 2 * W) = blockOf W δ nxt) ∨
              (blockOf W δ (nxt + W) = blockOf W δ nxt ∧
                blockOf W δ (nxt + 2 * W) = blockOf W δ b)) →
              eval δ (toQBF (prefixF W k (nxt + 3 * W))
                (exs s Ws (D.matrixF s k (nxt + W) (nxt + 2 * W) (nxt + 3 * W)))) = true)) := by
        intro δ
        rw [← D.validF_eval, ← eval_condF_iff, hBODY, ← toQBF_blockQ_false, ← toQBF_append]
        refine eval_toQBF_conj_impl _ _ _ _ δ ?_ ?_
        · intro q hq hmem
          have hv := D.validF_vars nxt _ hmem
          rw [List.mem_append] at hq
          rcases hq with hq | hq
          · have := mem_prefixF W k _ q hq
            omega
          · have := mem_blockQ _ _ _ _ hq
            omega
        · intro q hq hmem
          rcases mem_freeVars_condF _ _ _ _ _ _ hmem with h | h | h | h | h <;>
            rw [List.mem_append] at hq <;> rcases hq with hq | hq <;>
            first
              | (have := mem_prefixF W k _ q hq; omega)
              | (have := mem_blockQ _ _ _ _ hq; omega)
      rw [hfold, eval_exs_iff]
      simp only [eval_toQBF_blockQ_true_iff, hinner]
      constructor
      · rintro ⟨β, hβ, h⟩
        have hM : D.Valid (blockOf W β nxt) := (h β (fun _ _ => rfl) β (fun _ _ => rfl)).1
        have hβa : blockOf W β a = blockOf W α a :=
          blockOf_of_agree_below α β a nxt ha fun i hi => hβ i (Or.inl hi)
        have hβb : blockOf W β b = blockOf W α b :=
          blockOf_of_agree_below α β b nxt hb fun i hi => hβ i (Or.inl hi)
        refine ⟨blockOf W β nxt, ?_, ?_⟩
        · obtain ⟨γ, hγ⟩ : ∃ γ, γ = setBlock (W := W) β (nxt + W) (blockOf W β a) := ⟨_, rfl⟩
          obtain ⟨δ, hδ⟩ : ∃ δ, δ = setBlock (W := W) γ (nxt + 2 * W) (blockOf W β nxt) :=
            ⟨_, rfl⟩
          have hγa : ∀ i, (i < nxt + W ∨ nxt + W + W ≤ i) → γ i = β i := by
            rw [hγ]; exact setBlock_agree _ _ _
          have hδa : ∀ i, (i < nxt + 2 * W ∨ nxt + 2 * W + W ≤ i) → δ i = γ i := by
            rw [hδ]; exact setBlock_agree _ _ _
          have hlow : ∀ i, i < nxt + W → δ i = β i := fun i hi => by
            rw [hδa i (by omega), hγa i (by omega)]
          have hu : blockOf W δ (nxt + W) = blockOf W β a := by
            rw [hδ, blockOf_eq_of_agree W γ _ (nxt + W) fun i _ hi =>
              setBlock_agree _ _ _ i (by omega), hγ, blockOf_setBlock_self]
          have hv : blockOf W δ (nxt + 2 * W) = blockOf W β nxt := by
            rw [hδ, blockOf_setBlock_self]
          have hδA : blockOf W δ a = blockOf W α a := by
            rw [blockOf_of_agree_below α δ a nxt ha fun i hi => by
              rw [hlow i (by omega), hβ i (Or.inl hi)]]
          have hδM : blockOf W δ nxt = blockOf W β nxt :=
            blockOf_of_agree_below β δ nxt (nxt + W) le_rfl hlow
          have hc := (h γ hγa δ hδa).2 (Or.inl ⟨by rw [hu, hδA, hβa], by rw [hv, hδM]⟩)
          rw [eval_level s k (nxt + W) (nxt + 2 * W) (nxt + 3 * W) δ (by omega) (by omega) hs'
            (by rw [hu, hβa]; exact hva) (by rw [hv]; exact hM), hu, hv, hβa] at hc
          exact hc
        · obtain ⟨γ, hγ⟩ : ∃ γ, γ = setBlock (W := W) β (nxt + W) (blockOf W β nxt) := ⟨_, rfl⟩
          obtain ⟨δ, hδ⟩ : ∃ δ, δ = setBlock (W := W) γ (nxt + 2 * W) (blockOf W β b) := ⟨_, rfl⟩
          have hγa : ∀ i, (i < nxt + W ∨ nxt + W + W ≤ i) → γ i = β i := by
            rw [hγ]; exact setBlock_agree _ _ _
          have hδa : ∀ i, (i < nxt + 2 * W ∨ nxt + 2 * W + W ≤ i) → δ i = γ i := by
            rw [hδ]; exact setBlock_agree _ _ _
          have hlow : ∀ i, i < nxt + W → δ i = β i := fun i hi => by
            rw [hδa i (by omega), hγa i (by omega)]
          have hu : blockOf W δ (nxt + W) = blockOf W β nxt := by
            rw [hδ, blockOf_eq_of_agree W γ _ (nxt + W) fun i _ hi =>
              setBlock_agree _ _ _ i (by omega), hγ, blockOf_setBlock_self]
          have hv : blockOf W δ (nxt + 2 * W) = blockOf W β b := by
            rw [hδ, blockOf_setBlock_self]
          have hδB : blockOf W δ b = blockOf W α b := by
            rw [blockOf_of_agree_below α δ b nxt hb fun i hi => by
              rw [hlow i (by omega), hβ i (Or.inl hi)]]
          have hδM : blockOf W δ nxt = blockOf W β nxt :=
            blockOf_of_agree_below β δ nxt (nxt + W) le_rfl hlow
          have hc := (h γ hγa δ hδa).2 (Or.inr ⟨by rw [hu, hδM], by rw [hv, hβb, hδB]⟩)
          rw [eval_level s k (nxt + W) (nxt + 2 * W) (nxt + 3 * W) δ (by omega) (by omega) hs'
            (by rw [hu]; exact hM) (by rw [hv, hβb]; exact hvb), hu, hv, hβb] at hc
          exact hc
      · rintro ⟨μ, h1, h2⟩
        have hμ : D.Valid μ := ReachPow.valid_right D k h1
        refine ⟨setBlock (W := W) α nxt μ, setBlock_agree _ _ _, fun γ hγ δ hδ => ?_⟩
        have hlowδ : ∀ i, i < nxt + W → δ i = setBlock (W := W) α nxt μ i := fun i hi => by
          rw [hδ i (by omega), hγ i (by omega)]
        have hδM : blockOf W δ nxt = μ := by
          rw [blockOf_of_agree_below _ δ nxt (nxt + W) le_rfl hlowδ, blockOf_setBlock_self]
        have hδA : blockOf W δ a = blockOf W α a := by
          rw [blockOf_of_agree_below _ δ a nxt ha fun i hi => by
            rw [hlowδ i (by omega), setBlock_agree _ _ _ i (by omega)]]
        have hδB : blockOf W δ b = blockOf W α b := by
          rw [blockOf_of_agree_below _ δ b nxt hb fun i hi => by
            rw [hlowδ i (by omega), setBlock_agree _ _ _ i (by omega)]]
        refine ⟨by rw [hδM]; exact hμ, fun hc => ?_⟩
        rcases hc with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · rw [eval_level s k (nxt + W) (nxt + 2 * W) (nxt + 3 * W) δ (by omega) (by omega) hs'
            (by rw [hu, hδA]; exact hva) (by rw [hv, hδM]; exact hμ), hu, hv, hδA, hδM]
          exact h1
        · rw [eval_level s k (nxt + W) (nxt + 2 * W) (nxt + 3 * W) δ (by omega) (by omega) hs'
            (by rw [hu, hδM]; exact hμ) (by rw [hv, hδB]; exact hvb), hu, hv, hδB, hδM]
          exact h2

/-! ## The whole formula -/

/-- The offset of the scratch block. -/
def scratchOff (W k : ℕ) : ℕ := 2 * W + 3 * W * k

/-- The number of variables before the Tseitin auxiliaries. -/
def preAux (W Ws k : ℕ) : ℕ := scratchOff W k + Ws

/-- The guards on the two outer blocks: `A` is the start, both are valid, `B` accepts. -/
def guardF (init : Fin W → Bool) : QBF :=
  andList [constF W 0 init, D.validF 0, D.validF W, D.accF W]

theorem eval_guardF_iff (init : Fin W → Bool) (α : ℕ → Bool) :
    eval α (D.guardF init) = true ↔
      blockOf W α 0 = init ∧ D.Valid (blockOf W α 0) ∧ D.Valid (blockOf W α W) ∧
        D.Acc (blockOf W α W) := by
  rw [guardF, eval_andList_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    eval_constF_iff, D.validF_eval, D.accF_eval]

theorem quantifierFree_guardF (init : Fin W → Bool) : QuantifierFree (D.guardF init) :=
  quantifierFree_andList _ fun φ hφ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl
    · exact quantifierFree_constF _ _ _
    · exact D.validF_qf _
    · exact D.validF_qf _
    · exact D.accF_qf _

theorem mem_freeVars_guardF (init : Fin W → Bool) (i : ℕ) (hi : i ∈ freeVars (D.guardF init)) :
    i < 2 * W := by
  obtain ⟨φ, hφ, hi⟩ := mem_freeVars_andList _ i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl | rfl
  · have := mem_freeVars_constF _ _ _ _ hi; omega
  · have := D.validF_vars 0 i hi; omega
  · have := D.validF_vars W i hi; omega
  · have := D.accF_vars W i hi; omega

/-- The quantifier-free matrix before Tseitin: the guards and the levels. -/
def topBody (init : Fin W → Bool) (k : ℕ) : QBF :=
  conj (D.guardF init) (disj (neg tru) (D.matrixF (scratchOff W k) k 0 W (2 * W)))

theorem quantifierFree_topBody (init : Fin W → Bool) (k : ℕ) :
    QuantifierFree (D.topBody init k) := by
  have h1 := D.quantifierFree_guardF init
  have h2 := D.quantifierFree_matrixF (scratchOff W k) k 0 W (2 * W)
  simp only [QuantifierFree, quantDepth, topBody, Nat.max_eq_zero_iff] at *
  exact ⟨h1, trivial, h2⟩

theorem mem_freeVars_topBody (init : Fin W → Bool) (k : ℕ) (i : ℕ)
    (hi : i ∈ freeVars (D.topBody init k)) : i < preAux W Ws k := by
  simp only [topBody, freeVars, Finset.mem_union] at hi
  have hk : 0 ≤ 3 * W * k := Nat.zero_le _
  rcases hi with h | h | h
  · have := D.mem_freeVars_guardF init i h
    simp only [preAux, scratchOff]
    omega
  · simp at h
  · rcases D.mem_freeVars_matrixF (scratchOff W k) k 0 W (2 * W) i h with h | h | h | h <;>
      simp only [preAux, scratchOff] at * <;> omega

/-- The quantifier prefix before the Tseitin auxiliaries: `∃A ∃B`, the levels, the scratch. -/
def basePrefix (W Ws k : ℕ) : Prefix :=
  blockQ false 0 W ++ blockQ false W W ++ prefixF W k (2 * W) ++
    blockQ false (scratchOff W k) Ws

/-- **The base formula.** -/
theorem eval_basePrefix (init : Fin W → Bool) (k : ℕ) (α : ℕ → Bool) :
    eval α (toQBF (basePrefix W Ws k) (D.topBody init k)) = true ↔
      D.Valid init ∧ ∃ B : Fin W → Bool, D.Valid B ∧ D.Acc B ∧ D.ReachPow k init B := by
  obtain ⟨P, hP⟩ : ∃ P, P = prefixF W k (2 * W) ++ blockQ false (scratchOff W k) Ws := ⟨_, rfl⟩
  have hsplit : toQBF (basePrefix W Ws k) (D.topBody init k)
      = toQBF (blockQ false 0 W) (toQBF (blockQ false W W) (toQBF P (D.topBody init k))) := by
    rw [hP, basePrefix, toQBF_append, toQBF_append, toQBF_append, toQBF_append]
  have hbody : ∀ δ : ℕ → Bool, eval δ (toQBF P (D.topBody init k)) = true ↔
      ((blockOf W δ 0 = init ∧ D.Valid (blockOf W δ 0) ∧ D.Valid (blockOf W δ W) ∧
          D.Acc (blockOf W δ W)) ∧
        eval δ (toQBF (prefixF W k (2 * W))
          (exs (scratchOff W k) Ws (D.matrixF (scratchOff W k) k 0 W (2 * W)))) = true) := by
    intro δ
    rw [← D.eval_guardF_iff, hP, topBody, ← toQBF_blockQ_false, ← toQBF_append]
    rw [eval_toQBF_conj_impl _ _ _ _ δ ?_ ?_]
    · simp
    · intro q hq hmem
      have hv := D.mem_freeVars_guardF init _ hmem
      rw [List.mem_append] at hq
      rcases hq with hq | hq
      · have := mem_prefixF W k _ q hq
        omega
      · have := mem_blockQ _ _ _ _ hq
        simp only [scratchOff] at this
        omega
    · intro q _ hmem
      simp [freeVars] at hmem
  have hlevel : ∀ δ : ℕ → Bool, D.Valid (blockOf W δ 0) → D.Valid (blockOf W δ W) →
      (eval δ (toQBF (prefixF W k (2 * W))
          (exs (scratchOff W k) Ws (D.matrixF (scratchOff W k) k 0 W (2 * W)))) = true ↔
        D.ReachPow k (blockOf W δ 0) (blockOf W δ W)) := by
    intro δ h0 hW
    exact D.eval_level (scratchOff W k) k 0 W (2 * W) δ (by omega) (by omega)
      (by simp only [scratchOff]; omega) h0 hW
  rw [hsplit, toQBF_blockQ_false, eval_exs_iff]
  simp only [toQBF_blockQ_false, eval_exs_iff, hbody]
  constructor
  · rintro ⟨β, -, γ, -, ⟨hinit, h0, hW, hacc⟩, hlev⟩
    rw [hlevel γ h0 hW, hinit] at hlev
    exact ⟨hinit ▸ h0, blockOf W γ W, hW, hacc, hlev⟩
  · rintro ⟨hvi, B, hvB, haB, hreach⟩
    obtain ⟨γ, hγ⟩ : ∃ γ, γ = setBlock (W := W) (setBlock (W := W) α 0 init) W B := ⟨_, rfl⟩
    have hγ0 : blockOf W γ 0 = init := by
      rw [hγ, blockOf_eq_of_agree W _ _ 0 fun i _ hi => setBlock_agree _ _ _ i (by omega),
        blockOf_setBlock_self]
    have hγW : blockOf W γ W = B := by rw [hγ, blockOf_setBlock_self]
    refine ⟨setBlock (W := W) α 0 init, setBlock_agree _ _ _, γ, ?_, ?_, ?_⟩
    · rw [hγ]; exact setBlock_agree _ _ _
    · exact ⟨hγ0, by rw [hγ0]; exact hvi, by rw [hγW]; exact hvB, by rw [hγW]; exact haB⟩
    · rw [hlevel γ (by rw [hγ0]; exact hvi) (by rw [hγW]; exact hvB), hγ0, hγW]
      exact hreach

/-! ## The prenex CNF instance -/

theorem eval_cnfQBF_snoc_lit (β : ℕ → Bool) (cs : List (List CLit)) (l : CLit) :
    eval β (cnfQBF (cs ++ [[l]])) = (eval β (cnfQBF cs) && eval β (litQBF l)) := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [Bool.and_eq_true]
  constructor
  · intro h
    rw [eval_cnfQBF_append] at h
    refine ⟨h.1, ?_⟩
    have := (eval_cnfQBF_iff β [[l]]).mp h.2 [l] (by simp)
    rw [eval_clauseQBF_iff] at this
    obtain ⟨l', hl', hv⟩ := this
    simp only [List.mem_singleton] at hl'
    exact hl' ▸ hv
  · rintro ⟨h1, h2⟩
    rw [eval_cnfQBF_append]
    refine ⟨h1, ?_⟩
    rw [eval_cnfQBF_iff]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    rw [eval_clauseQBF_iff]
    exact ⟨l, by simp, h2⟩

/-- The clauses of the whole instance: the Tseitin clauses and the output unit clause. -/
noncomputable def savitchCNF (init : Fin W → Bool) (k : ℕ) : List (List CLit) :=
  (tseitin (D.topBody init k) (preAux W Ws k)).1 ++
    [[(tseitin (D.topBody init k) (preAux W Ws k)).2.1]]

/-- The quantifier prefix of the whole instance: all variables, existential except the levels'
`U`/`V` blocks, in index order. -/
noncomputable def savitchPrefix (init : Fin W → Bool) (k : ℕ) : Prefix :=
  basePrefix W Ws k ++ blockQ false (preAux W Ws k)
    ((tseitin (D.topBody init k) (preAux W Ws k)).2.2 - preAux W Ws k)

/-- **The whole formula is Savitch's recursion.** -/
theorem eval_savitch (init : Fin W → Bool) (k : ℕ) (α : ℕ → Bool) :
    eval α (toQBF (D.savitchPrefix init k) (cnfQBF (D.savitchCNF init k))) = true ↔
      D.Valid init ∧ ∃ B : Fin W → Bool, D.Valid B ∧ D.Acc B ∧ D.ReachPow k init B := by
  obtain ⟨V, hV⟩ : ∃ V, V = preAux W Ws k := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = tseitin (D.topBody init k) V := ⟨_, rfl⟩
  have hqf := D.quantifierFree_topBody init k
  have hvars : ∀ i ∈ freeVars (D.topBody init k), i < V := fun i hi => by
    rw [hV]; exact D.mem_freeVars_topBody init k i hi
  have hcongr : ∀ β : ℕ → Bool,
      eval β (cnfQBF (D.savitchCNF init k)) = eval β (conj (cnfQBF R.1) (litQBF R.2.1)) := by
    intro β
    rw [savitchCNF, ← hV, ← hR, eval_cnfQBF_snoc_lit, eval_conj]
  have hstep : ∀ β : ℕ → Bool,
      eval β (toQBF (blockQ false V (R.2.2 - V)) (cnfQBF (D.savitchCNF init k)))
        = eval β (D.topBody init k) := by
    intro β
    rw [eval_toQBF_congr (blockQ false V (R.2.2 - V)) (cnfQBF (D.savitchCNF init k))
      (conj (cnfQBF R.1) (litQBF R.2.1)) hcongr β, toQBF_blockQ_false, hR]
    exact eval_exs_tseitin (D.topBody init k) V hqf hvars β
  rw [savitchPrefix, ← hV, ← hR, toQBF_append,
    eval_toQBF_congr (basePrefix W Ws k) _ (D.topBody init k) hstep]
  exact D.eval_basePrefix init k α

/-! ## Well-formedness -/

/-- A prefix listing consecutive variables from `off`. -/
def Ordered (off : ℕ) (qs : Prefix) : Prop :=
  ∀ (i : ℕ) (hi : i < qs.length), (qs[i]'hi).2 = off + i

theorem ordered_blockQ (q : Bool) (off n : ℕ) : Ordered off (blockQ q off n) := by
  intro i hi
  have h : (blockQ q off n)[i]'hi
      = ((List.range n).map fun j => (q, off + j))[i]'(by simpa [blockQ] using hi) := by
    congr 1
  rw [h, List.getElem_map, List.getElem_range]

theorem Ordered.append {off : ℕ} {qs₁ qs₂ : Prefix} (h₁ : Ordered off qs₁)
    (h₂ : Ordered (off + qs₁.length) qs₂) : Ordered off (qs₁ ++ qs₂) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases h : i < qs₁.length
  · rw [List.getElem_append_left h]
    exact h₁ i h
  · rw [List.getElem_append_right (by omega)]
    have := h₂ (i - qs₁.length) (by omega)
    rw [this]
    omega

theorem prefixF_length (W : ℕ) : ∀ (k nxt : ℕ), (prefixF W k nxt).length = 3 * W * k
  | 0, _ => by simp [prefixF]
  | k + 1, nxt => by
      rw [prefixF, List.length_append, List.length_append, List.length_append, blockQ_length,
        blockQ_length, blockQ_length, prefixF_length W k]
      ring

theorem ordered_prefixF (W : ℕ) : ∀ (k nxt : ℕ), Ordered nxt (prefixF W k nxt)
  | 0, _ => by intro i hi; simp [prefixF] at hi
  | k + 1, nxt => by
      rw [prefixF]
      refine Ordered.append (Ordered.append (Ordered.append (ordered_blockQ _ _ _) ?_) ?_) ?_
      · rw [blockQ_length]
        exact ordered_blockQ _ _ _
      · rw [List.length_append, blockQ_length, blockQ_length,
          show nxt + (W + W) = nxt + 2 * W by ring]
        exact ordered_blockQ _ _ _
      · rw [List.length_append, List.length_append, blockQ_length, blockQ_length, blockQ_length,
          show nxt + (W + W + W) = nxt + 3 * W by ring]
        exact ordered_prefixF W k (nxt + 3 * W)

theorem basePrefix_length (W Ws k : ℕ) : (basePrefix W Ws k).length = preAux W Ws k := by
  rw [basePrefix, List.length_append, List.length_append, List.length_append, blockQ_length,
    blockQ_length, blockQ_length, prefixF_length, preAux, scratchOff]
  ring

theorem ordered_basePrefix (W Ws k : ℕ) : Ordered 0 (basePrefix W Ws k) := by
  rw [basePrefix]
  refine Ordered.append (Ordered.append (Ordered.append (ordered_blockQ _ _ _) ?_) ?_) ?_
  · rw [blockQ_length, Nat.zero_add]
    exact ordered_blockQ _ _ _
  · rw [List.length_append, blockQ_length, blockQ_length,
      show 0 + (W + W) = 2 * W by ring]
    exact ordered_prefixF W k (2 * W)
  · rw [List.length_append, List.length_append, blockQ_length, blockQ_length, prefixF_length,
      show 0 + (W + W + 3 * W * k) = scratchOff W k by rw [scratchOff]; ring]
    exact ordered_blockQ _ _ _

theorem savitchPrefix_length (init : Fin W → Bool) (k : ℕ) :
    (D.savitchPrefix init k).length = (tseitin (D.topBody init k) (preAux W Ws k)).2.2 := by
  have hge := tseitin_next_ge (D.topBody init k) (preAux W Ws k)
  rw [savitchPrefix, List.length_append, basePrefix_length, blockQ_length]
  omega

theorem ordered_savitchPrefix (init : Fin W → Bool) (k : ℕ) :
    Ordered 0 (D.savitchPrefix init k) := by
  rw [savitchPrefix]
  refine Ordered.append (ordered_basePrefix W Ws k) ?_
  rw [basePrefix_length, Nat.zero_add]
  exact ordered_blockQ _ _ _

/-- **The instance is well formed** in the sense Shen's protocol needs: the prefix names the
variables `0, …, n - 1` in order, and every literal is one of them. -/
theorem wellFormed_savitch (init : Fin W → Bool) (k : ℕ) :
    WellFormed (D.savitchPrefix init k, D.savitchCNF init k) := by
  have hvars : ∀ i ∈ freeVars (D.topBody init k), i < preAux W Ws k := fun i hi =>
    D.mem_freeVars_topBody init k i hi
  refine ⟨fun i hi => ?_, fun c hc l hl => ?_⟩
  · have := D.ordered_savitchPrefix init k i hi
    simpa using this
  · rw [savitchPrefix_length]
    simp only [savitchCNF, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact tseitin_clause_vars_lt (D.topBody init k) _ hvars c hc l hl
    · simp only [List.mem_singleton] at hl
      subst hl
      exact tseitin_out_lt (D.topBody init k) _ hvars

/-- **The reduction, packaged**: the instance is well formed, and it is true exactly when some
valid accepting block is reachable from `init` in `2 ^ k` steps. -/
theorem savitch_spec (init : Fin W → Bool) (k : ℕ) :
    WellFormed (D.savitchPrefix init k, D.savitchCNF init k) ∧
      (QBF.eval (fun _ => false)
          (toQBF (D.savitchPrefix init k) (cnfQBF (D.savitchCNF init k))) = true ↔
        D.Valid init ∧ ∃ B : Fin W → Bool, D.Valid B ∧ D.Acc B ∧ D.ReachPow k init B) :=
  ⟨D.wellFormed_savitch init k, D.eval_savitch init k _⟩

end SavitchData

end Complexity
