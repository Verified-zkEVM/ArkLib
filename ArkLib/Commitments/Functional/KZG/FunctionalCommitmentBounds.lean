/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.FunctionalCommitment
public import ArkLib.Commitments.Functional.KZG.Generic.Security

/-!
# KZG fixed-claim binding in group models

The bounds require that the pairing `e g₁ g₂` is nonzero. The KZG projection of the
functional commitment adversary must agree with the adversary induced by an algebraic or
generic group strategy.
-/

@[expose] public section

open OracleComp OracleSpec FunctionalCommitment GroupModel CompPoly
open scoped ENNReal

namespace KZG

variable {F G₁ G₂ Gₜ : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq G₂] [DecidableEq Gₜ]
  {n L : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (he : e g₁ g₂ ≠ 0)
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl emptySpec0 (StateT σ ProbComp))
  (chal : (functionalCommitment e g₁ g₂ n).ChallengeSampler)
  (A : (functionalCommitment e g₁ g₂ n).FixedClaimAdversary L)

include he in
/-- An algebraic adversary's fixed-claim binding advantage is at most the PairingDLog success
probability of `AGM.reduction` plus `1 / |F|`. The projection equation lets us apply
`AGM.functionBinding_le_pairingDLog` to the functional commitment game. -/
theorem fixedClaimBindingAdvantage_le_agm (M : AGM.Adversary F G₁ G₂ (List (F × F)))
    (h : toKZGAdversary A = AGM.toFunctionBindingAdversary M)
    (roots : CPolynomial F → List F)
    (complete : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p) :
    (functionalCommitment e g₁ g₂ n).fixedClaimBindingAdvantage init impl chal L A ≤
      Pr{let b ← PairingDLog.experiment g₁ g₂ (AGM.reduction (n := n) g₂ roots id M)}[b = true]
        + 1 / (Fintype.card F : ℝ≥0∞) := by
  rw [fixedClaimBindingAdvantage_eq, h]
  exact AGM.functionBinding_le_pairingDLog he roots complete M

include he in
/-- An algebraic adversary's fixed-claim binding advantage is at most the PairingDLog success
probability of the first-claim reduction `AGM.reductionFirst` plus `1 / |F|`. The projection
equation lets us apply `AGM.functionBinding_le_pairingDLog_first` to the functional commitment
game. -/
theorem fixedClaimBindingAdvantage_le_agmFirst (M : AGM.Adversary F G₁ G₂ (List (F × F)))
    (h : toKZGAdversary A = AGM.toFunctionBindingAdversary M)
    (roots : CPolynomial F → List F)
    (complete : ∀ p, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ roots p) :
    (functionalCommitment e g₁ g₂ n).fixedClaimBindingAdvantage init impl chal L A ≤
      Pr{let b ← PairingDLog.experiment g₁ g₂ (AGM.reductionFirst (n := n) g₂ roots id M)}[b = true]
        + 1 / (Fintype.card F : ℝ≥0∞) := by
  rw [fixedClaimBindingAdvantage_eq, h]
  exact AGM.functionBinding_le_pairingDLog_first he roots complete M

include he in
/-- A generic adversary with at most `q` group operations has fixed-claim binding advantage
at most `((n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2) / |F|`. The projection equation
lets us apply `Generic.functionBinding_le_generic` to the functional commitment game. -/
theorem fixedClaimBindingAdvantage_le_generic [DecidableEq G₁]
    (M : Generic.Adversary F (List (F × F)))
    (h : toKZGAdversary A = M.toFunctionBindingAdversary e)
    (q : ℕ) (hq : IsQueryBoundP (M (Generic.input n)) (fun i => isGroupOp i = true) q) :
    (functionalCommitment e g₁ g₂ n).fixedClaimBindingAdvantage init impl chal L A ≤
      (((n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  rw [fixedClaimBindingAdvantage_eq, h]
  exact Generic.functionBinding_le_generic n M e g₁ g₂ he q hq

end KZG
