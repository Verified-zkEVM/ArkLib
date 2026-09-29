/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateRound
public import ArkLib.ProofSystem.Sumcheck.Interaction.Soundness

/-!
# Soundness of an actual multivariate Sumcheck round

The original multivariate polynomial has individual degree at most `deg` and realizes the retained
input behavior. An arbitrary univariate message of degree at most `deg` is selected before a fresh
uniform verifier challenge. The chance that
a false current claim produces an accepted true successor is at most `deg / |F|`. The proof
transports the existing univariate soundness theorem, including rejection, rather than repeating
the polynomial root argument. Both the original polynomial and the sent message use the global
degree cap; a smaller honest coordinate degree alone does not reduce the adversary's cap.
-/

@[expose] public section

namespace Sumcheck.Interaction.MultivariateRound

open OracleComp OracleSpec
open _root_.Interaction.Oracle
open SingleRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ)

/-- Closing the actual sampled executor preserves its input behavior in both branches. -/
theorem executeCore_sampled_closed_eq [DecidableEq R] {ι : Type} (ambient : OracleSpec ι)
    (i : Fin n) (stmt : Spec.StatementRound R n i.castSucc)
    (impl : (polynomialFamily R n deg).Behavior) (q : Message R deg)
    (domain : List R) (challenge : OracleComp ambient R) :
    CoreRun.closed <$> executeCore (sampledReduction R n deg ambient i domain challenge)
        impl stmt q =
      (fun r => if (domain.map (fun x => q.val.eval x)).sum = stmt.target then
        some (⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩, impl⟩ :
          ClosedClaim (Spec.StatementRound R n i.succ) (polynomialFamily R n deg))
        else none) <$> challenge := by
  rw [executeCore_sampled_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  congr 1
  funext r
  rw [executeCore_eq]
  split <;> rfl

/-- A true accepted successor is precisely a collision with the honest round projection. -/
theorem acceptedRun_closedRelation_iff {m : ℕ} (D : Fin m ↪ R) (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ())
    (q : Message R deg) (r : R) :
    closedRelation R n deg D i.succ
      ⟨⟨q.val.eval r, Fin.snoc stmt.challenges r⟩,
        (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩ ↔
      (Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval r =
        q.val.eval r :=
  relationRound_output_iff R n deg D i stmt p r (q.val.eval r)

/-- False current relation gives the exact false univariate projected input claim. -/
theorem projected_sum_iff_closedRelation {m : ℕ} (D : Fin m ↪ R) (i : Fin n)
    (stmt : Spec.StatementRound R n i.castSucc) (p : Spec.OracleStatement R n deg ()) :
    ((Finset.univ.map D).toList.map (fun x =>
      (Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval x)).sum =
        stmt.target ↔ closedRelation R n deg D i.castSucc
          ⟨stmt, (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p)⟩ :=
  projected_sum_iff_relationRound R n deg D i stmt p

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- One actual multivariate round is sound against every message fixed before its fresh challenge.
The realization equality ties the mathematical polynomial to the exact retained behavior. -/
theorem executeCore_sampled_soundness {m : ℕ} (D : Fin m ↪ F) (i : Fin n)
    (stmt : Spec.StatementRound F n i.castSucc) (p : Spec.OracleStatement F n deg ())
    (impl : (polynomialFamily F n deg).Behavior) (q : Message F deg)
    (himpl : impl = (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D i.castSucc ⟨stmt, impl⟩) :
    Pr{let result : Option (ClosedClaim (Spec.StatementRound F n i.succ)
        (polynomialFamily F n deg)) ← CoreRun.closed <$>
      executeCore (sampledReduction F n deg unifSpec i (Finset.univ.map D).toList ($ᵗ F))
        impl stmt q}[result.map (closedRelation F n deg D i.succ) = some True] ≤
      (deg : ENNReal) / Fintype.card F := by
  subst impl
  let projected := Spec.SingleRound.projectedRoundPolynomial F n deg D i stmt.challenges p
  have hsum : ((Finset.univ.map D).toList.map (fun x => projected.val.eval x)).sum ≠
      stmt.target := fun h => hfalse ((projected_sum_iff_closedRelation F n deg D i stmt p).mp h)
  have h := executeCommitted_soundness F deg projected q (Finset.univ.map D).toList
    stmt.target hsum
  rw [executeCommitted_eq, prEvent_map] at h
  rw [executeCore_sampled_closed_eq, prEvent_map]
  refine (prEvent_congr ($ᵗ F) _ _ ?_).trans_le h
  intro r
  rw [committedRun_true_iff]
  by_cases hcheck : ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = stmt.target
  · simp only [hcheck, ↓reduceIte, Option.map_some, Option.some.injEq]
    simpa only [eq_iff_iff, iff_true, true_and] using
      acceptedRun_closedRelation_iff F n deg D i stmt p q r
  · simp only [hcheck, ↓reduceIte, Option.map_none, reduceCtorEq, false_and]

private theorem prEvent_eq_evalDist_map_unifSpec {α : Type} (mx : OracleComp unifSpec α)
    (event : α → Prop) : Pr{let x ← mx}[event x] = 𝒟[event <$> mx] {True} :=
  prEvent_eq_evalDist_map mx event

/-- Native measure form of the same actual closed-output soundness event. -/
theorem executeCore_sampled_measureSoundness {m : ℕ} (D : Fin m ↪ F) (i : Fin n)
    (stmt : Spec.StatementRound F n i.castSucc) (p : Spec.OracleStatement F n deg ())
    (impl : (polynomialFamily F n deg).Behavior) (q : Message F deg)
    (himpl : impl = (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D i.castSucc ⟨stmt, impl⟩) :
    𝒟[(fun result : Option (ClosedClaim (Spec.StatementRound F n i.succ)
        (polynomialFamily F n deg)) => result.map (closedRelation F n deg D i.succ) = some True) <$>
      (CoreRun.closed <$>
        executeCore (sampledReduction F n deg unifSpec i (Finset.univ.map D).toList ($ᵗ F))
          impl stmt q)] {True} ≤ (deg : ENNReal) / Fintype.card F := by
  rw [← prEvent_eq_evalDist_map_unifSpec]
  exact executeCore_sampled_soundness n deg F D i stmt p impl q himpl hfalse

end
end Sumcheck.Interaction.MultivariateRound
