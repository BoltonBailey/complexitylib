import Complexitylib.SAT.VerifierTM
import Complexitylib.SAT.GuessVerify

namespace Complexity

/-!
# SAT ∈ NP — the headline theorem

This file ties together the two halves of the `SAT ∈ NP` proof:

* `SAT.TM.verifyPairTM_decidesInTime` (in `VerifierTM`) — the deterministic
  three-tape verifier decides `pairLang R_SAT` within the quadratic budget
  `verifyPairTMTime`, so `pairLang R_SAT ∈ P`.
* `SAT.L_SAT_in_NP_of_verifierP_direct` (in `GuessVerify`) — the SAT-specialized
  guess-and-verify NTM turns `pairLang R_SAT ∈ P` into `L_SAT ∈ NP`.

Combining them yields the unconditional theorem `SAT.L_SAT_mem_NP : L_SAT ∈ NP`.
-/

namespace SAT

/-- The paired SAT verifier language is decided in polynomial (in fact
quadratic) time by `verifyPairTM`, hence `pairLang R_SAT ∈ P`. -/
theorem pairLang_R_SAT_mem_P : pairLang R_SAT ∈ P :=
  Set.mem_iUnion.mpr
    ⟨2, 3, TM.verifyPairTM, TM.verifyPairTMTime,
      TM.verifyPairTM_decidesInTime, TM.verifyPairTMTime_bigO_quadratic⟩

/-- **SAT ∈ NP.** The Boolean satisfiability language is in `NP`, witnessed by
the SAT-specialized guess-and-verify NTM running over the polynomial-time
deterministic pair verifier. -/
theorem L_SAT_mem_NP : L_SAT ∈ NP :=
  L_SAT_in_NP_of_verifierP_direct pairLang_R_SAT_mem_P

end SAT

end Complexity
