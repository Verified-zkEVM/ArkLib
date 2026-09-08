/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.FRIBinius.Commitment
import ArkLib.ProofSystem.RingSwitching.Packing.ExactCommitment

/-!
# The actual Binius commitment as a ring-switch commitment

The adapter preserves the production oracle types, query interfaces, strict-half-distance
compatibility relation and honest novel-basis codeword constructor. The proved unique-distance
binding supplies both the generic exact commitment seam and the legacy functionality premise.
No normalization of the first basis element is needed for either result. These are commitment
semantics; they do not assert security of the later interleaved FRI-Binius opening protocol.
-/

noncomputable section

namespace Binius.FRIBinius

open AdditiveNTT Module Sumcheck.Structured RingSwitching.Packing

variable (κ : ℕ)
variable (L : Type) [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K]
variable [Fact (Nat.Prime (ringChar K))] [Fact (Fintype.card K = 2)]
variable [Algebra K L] (β : Basis (Fin (2 ^ κ)) K L)
variable (m 𝓡 ϑ : ℕ) [NeZero m] [NeZero ϑ] [Fact (ϑ ∣ m)]
variable (hRate : m + 𝓡 < 2 ^ κ)

/-- The exact legacy functionality premise follows from production unique-distance binding. -/
theorem binaryBasefold_functional :
    (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).Functional :=
  binaryBasefold_initialCompatibility_functional κ L K β m 𝓡 ϑ hRate

/-- The real initial Binius oracle family, interpreted through its unchanged compatibility
relation. -/
def binaryBasefoldPackedCommitment : PackedCommitment L m where
  ιC := (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).ιₛᵢ
  OStmt := (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).OStmtIn
  Oᵢ := (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).Oₛᵢ
  commitsTo o p :=
    (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).initialCompatibility (p, o)
  commit := honestPackedOracle κ L K β m 𝓡 ϑ hRate
  commitsTo_commit := honestPackedOracle_compatible κ L K β m 𝓡 ϑ hRate

/-- The base adapter retains the actual initial compatibility relation on the same oracle. -/
theorem binaryBasefoldPackedCommitment_commitsTo
    (o : ∀ j, (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).OStmtIn j)
    (p : MultilinearPoly L m) :
    (binaryBasefoldPackedCommitment κ L K β m 𝓡 ϑ hRate).commitsTo o p ↔
      (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).initialCompatibility (p, o) := Iff.rfl

/-- The base adapter uses the actual honest novel-basis codeword oracle constructor. -/
theorem binaryBasefoldPackedCommitment_commit (p : MultilinearPoly L m) :
    (binaryBasefoldPackedCommitment κ L K β m 𝓡 ϑ hRate).commit p =
      honestPackedOracle κ L K β m 𝓡 ϑ hRate p := rfl

/-- The real relation is functional by the proved production unique-distance theorem. -/
theorem binaryBasefoldPackedCommitment_functional :
    (binaryBasefoldPackedCommitment κ L K β m 𝓡 ϑ hRate).Functional := by
  intro o p p'
  exact binaryBasefold_initialCompatibility_functional κ L K β m 𝓡 ϑ hRate o p p'

/-- The exact specialization adds the proved binding property to the same base commitment. -/
def binaryBasefoldExactCommitment : ExactPackedCommitment L m where
  toPackedCommitment := binaryBasefoldPackedCommitment κ L K β m 𝓡 ϑ hRate
  commitsTo_functional := binaryBasefoldPackedCommitment_functional κ L K β m 𝓡 ϑ hRate

/-- Forgetting exactness preserves the actual production commitment data definitionally. -/
theorem binaryBasefoldExactCommitment_toPackedCommitment :
    (binaryBasefoldExactCommitment κ L K β m 𝓡 ϑ hRate).toPackedCommitment =
      binaryBasefoldPackedCommitment κ L K β m 𝓡 ϑ hRate := rfl

/-- The adapter's relation is the actual initial compatibility relation, with the same oracle. -/
theorem binaryBasefoldExactCommitment_commitsTo
    (o : ∀ j, (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).OStmtIn j)
    (p : MultilinearPoly L m) :
    (binaryBasefoldExactCommitment κ L K β m 𝓡 ϑ hRate).commitsTo o p ↔
      (BinaryBasefoldAbstractOStmtIn κ L K β m 𝓡 ϑ hRate).initialCompatibility (p, o) := Iff.rfl

/-- Honest commitments use the production codeword oracle constructor. -/
theorem binaryBasefoldExactCommitment_commit (p : MultilinearPoly L m) :
    (binaryBasefoldExactCommitment κ L K β m 𝓡 ϑ hRate).commit p =
      honestPackedOracle κ L K β m 𝓡 ϑ hRate p := rfl

end Binius.FRIBinius

end
