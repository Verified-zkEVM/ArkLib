/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Algebra.Field.ZMod
import ArkLib.ProofSystem.Sumcheck.Interaction.Soundness
import ArkLibTest.ProofSystem.Sumcheck.Interaction.SingleRound

/-! # Adversarial closed-output regression tests

The false claim for `X` on `[0]` is supported by the cheating constant message `1`.
It passes the sum check, but produces a true closed output only at challenge `1`.
-/

namespace Sumcheck.Interaction.SingleRound.Test

open OracleComp Polynomial

noncomputable section

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A cheating message whose sum equals the false target. -/
def cheating : Message (ZMod 17) 1 :=
  ⟨1, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- The input behavior, rather than the sent message, decides the closed relation. -/
example : (committedRun (ZMod 17) 1 polynomial cheating [0] 1 0).closed.map
    (closedOutputRelation (ZMod 17) 1) ≠ some True := by
  rw [ne_eq, committedRun_true_iff]
  simp [polynomial, cheating]

/-- Collision at one challenge really does fool this round. -/
example : (committedRun (ZMod 17) 1 polynomial cheating [0] 1 1).closed.map
    (closedOutputRelation (ZMod 17) 1) = some True := by
  rw [committedRun_true_iff]
  simp [polynomial, cheating]

/-- The actual executor, with a false input claim, obeys the nonvacuous field bound. -/
example : Pr[fun run => run.closed.map (closedOutputRelation (ZMod 17) 1) = some True |
    executeCommitted (ZMod 17) 1 ($ᵗ (ZMod 17)) polynomial cheating [0] 1] ≤
      (1 : ENNReal) / 17 := by
  simpa using executeCommitted_soundness (ZMod 17) 1 polynomial cheating [0] 1
    (by simp [polynomial])

/-- A rejected message produces no output even at a collision challenge. -/
example : (committedRun (ZMod 17) 1 polynomial cheating [0] 2 1).closed = none := by
  apply committedRun_rejects
  simpa [cheating] using (show (1 : ZMod 17) ≠ 2 by decide)

#print axioms executeCommitted_eq
#print axioms executeCommitted_soundness
#print axioms executeRandomCommitment_soundness
#print axioms executeCommitted_measure_soundness
#print axioms executeRandomCommitment_measure_soundness

end
end Sumcheck.Interaction.SingleRound.Test
