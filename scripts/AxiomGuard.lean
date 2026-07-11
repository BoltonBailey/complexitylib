/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexitylib

/-!
# Axiom guard

Asserts that the library's headline theorems depend only on the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no custom
axioms. Run with:

```bash
lake env lean scripts/AxiomGuard.lean
```

CI runs this on every push. When a headline theorem is renamed, update
`headlineTheorems` in the same commit.
-/

open Lean

/-- The axioms a headline theorem is allowed to depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The library's headline theorems, fully qualified. -/
def headlineTheorems : List Name := [
  -- Cook–Levin / NP-completeness
  `Complexity.SAT.NPComplete_L_SAT,
  `Complexity.SAT.L_SAT_mem_NP,
  `Complexity.SAT.pairLang_R_SAT_mem_P,
  -- Universal machine
  `Complexity.TM.UTMBody.utmTM_universal,
  `Complexity.TM.UTMBody.utmTM_universal_padded,
  -- Time hierarchy
  `Complexity.time_hierarchy_weak,
  `Complexity.time_hierarchy_weak_ssubset,
  `Complexity.DTIME_pow_ssubset,
  -- Structural containments
  `Complexity.P_subset_NP,
  `Complexity.P_subset_PSPACE,
  `Complexity.RP_subset_NP,
  `Complexity.BPP_subset_PP
]

open Elab Command in
run_cmd do
  let env ← getEnv
  for thm in headlineTheorems do
    unless env.contains thm do
      throwError "axiom guard: unknown declaration `{thm}` — was it renamed?"
    let axs ← liftCoreM (collectAxioms thm)
    for ax in axs do
      unless allowedAxioms.contains ax do
        throwError "axiom guard: `{thm}` depends on disallowed axiom `{ax}`"
  logInfo s!"axiom guard: {headlineTheorems.length} headline theorems use only standard axioms"
