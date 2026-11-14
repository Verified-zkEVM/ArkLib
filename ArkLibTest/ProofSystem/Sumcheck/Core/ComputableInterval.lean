/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.ComputableSoundness
import CompPoly.Multivariate.VarsDegrees

/-! # Runtime evidence for computed interval messages -/

namespace Sumcheck.Core.ComputableIntervalTest
open PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp

/-- The computed zero polynomial has degree zero in every coordinate. -/
theorem zero_degree (j : Fin 3) : (0 : CPoly.CMvPolynomial 3 ℕ).degreeOf j ≤ 0 := by
  simp

/-- Compute an honest message after a nonempty prefix, use challenge `3`, and retain data `29`. -/
def computedRun : Option (ℕ × ℕ × ℕ × ℕ) :=
  let st := intervalInitial 1 1 (by decide : 1 + 1 ≤ 3)
    (⟨0, ![7]⟩ : RoundStatement ℕ 3 1)
  (Interpreted.execute (pure 3 : Id ℕ) (intervalCheck (fun _ : Fin 2 => 0))
    IntervalClaim.finish 1 st 29
    (Computable.intervalHonestProver (fun _ : Fin 2 => 0) (0 : CPoly.CMvPolynomial 3 ℕ)
      zero_degree 1 st)).2.map fun t => (t.1.target, t.1.challenges 0, t.1.challenges 1, t.2)

/-- The actual computed-message executor accepts and preserves the earlier prefix and data. -/
example : computedRun = some (0, 7, 3, 29) := by
  dsimp only [computedRun]
  rw [Computable.execute_honest_eq_native]
  unfold Interpreted.execute intervalProver
  rw [run_foldRounds]
  have hid {α : Type} (x : α) : (pure x : Id α) = x := rfl
  have hbind {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
  have hmap {α β : Type} (f : α → β) (x : Id α) : (f <$> x) = f x := rfl
  have hmapM {α β : Type} (f : α → β) (xs : List α) :
      (xs.mapM (m := Id) f : List β) = xs.map f := List.idRun_mapM
  simp [hid, hbind, hmap, hmapM, simulateQ_list_mapM, drawChallenges, headNode,
    Interpreted.draw, foldTranscript,
    foldState, intervalNext,
    intervalMessage, Computable.toPolynomial, projectedRoundPolynomial,
    Interpreted.verdict, Interpreted.roundVerdict, Interpreted.message, Interpreted.challenge,
    consTranscript, MvPolynomial.evalExcept, intervalCheck, IntervalClaim.finish,
    IntervalClaim.next, IntervalClaim.index, intervalInitial]

#eval computedRun

end Sumcheck.Core.ComputableIntervalTest
