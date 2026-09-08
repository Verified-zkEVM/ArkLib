/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Commitment
import ArkLib.ProofSystem.Binius.FRIBinius.Prelude

/-!
# The FRI-Binius ring-switch commitment relation

The abstract input relation is functional because the novel-basis code has unique
witnesses within strict half distance. Honest coverage uses its initial oracle family and first
oracle accessor. These properties supply the commitment-side premises of ring switching, separately
from the soundness of the later opening protocol.
-/

noncomputable section

namespace Binius.FRIBinius

open AdditiveNTT Module Sumcheck.Structured

variable (κ : ℕ)
variable (L : Type) [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K]
variable [Fact (Nat.Prime (ringChar K))] [Fact (Fintype.card K = 2)]
variable [Algebra K L] (β : Basis (Fin (2 ^ κ)) K L)
variable (ℓ' 𝓡 ϑ : ℕ) [NeZero ℓ'] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (h_ℓ_add_R_rate : ℓ' + 𝓡 < 2 ^ κ)

/-- The FRI-Binius oracle compatibility relation determines a unique packed polynomial. -/
theorem binaryBasefold_initialCompatibility_functional
    (oStmt : ∀ j, (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ
      h_ℓ_add_R_rate).OStmtIn j) (t u : MultilinearPoly L ℓ')
    (ht : (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).initialCompatibility
      (t, oStmt))
    (hu : (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).initialCompatibility
      (u, oStmt)) : t = u :=
  BinaryBasefold.firstOracleWitnessConsistencyProp_functional K β _ t u ht hu

/-- Honest packed-polynomial oracles from the Binary Basefold first-codeword family. -/
def honestPackedOracle (t : MultilinearPoly L ℓ') :
    ∀ j, (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).OStmtIn j :=
  BinaryBasefold.honestInitialOracleStatement K β ϑ (h_ℓ_add_R_rate := h_ℓ_add_R_rate) t

/-- Every packed polynomial has an oracle satisfying the FRI-Binius input relation. -/
theorem honestPackedOracle_compatible (t : MultilinearPoly L ℓ') :
    (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).initialCompatibility
      (t, honestPackedOracle κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate t) :=
  BinaryBasefold.honestInitialOracleStatement_consistent K β ϑ t

/-- The commitment relation is inhabited for each packed polynomial, independently of binding. -/
theorem binaryBasefold_initialCompatibility_coverage (t : MultilinearPoly L ℓ') :
    ∃ oStmt, (BinaryBasefoldAbstractOStmtIn κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate).initialCompatibility
      (t, oStmt) :=
  ⟨honestPackedOracle κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate t,
    honestPackedOracle_compatible κ L K β ℓ' 𝓡 ϑ h_ℓ_add_R_rate t⟩

end Binius.FRIBinius
