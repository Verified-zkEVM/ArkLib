/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.AGM.FirstSecurity
public import ArkLib.Commitments.Functional.KZG.Generic.Equivalence
public import ArkLib.Commitments.Functional.KZG.Generic.Cost

/-!
# Unconditional KZG binding in Type 3 generic pairing groups

Both existing binding advantages are at most
`((n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2) / |F|`.
The bound is nontrivial when the field cardinality exceeds this numerator. It uses the FKL
translation, first-claim AGM recovery, and the generic `(n, 1)`-PairingDLog bound, with total
operation budget `Q = q + n + 1`. No source-generator surjectivity assumption is needed.

References: [KZG10TR]; Shoup, EUROCRYPT 1997; Maurer, IMA 2005;
Fuchsbauer–Kiltz–Loss, *The Algebraic Group Model and its Applications*, CRYPTO 2018.
-/

@[expose] public section

open CompPoly OracleComp OracleSpec GroupModel
open scoped ENNReal

namespace KZG.Generic

/-- A polynomial upper bound for the three collision terms and the two sampling terms. -/
theorem collision_numerator_le (n Q : ℕ) :
    (n + Q + 2).choose 2 * n + (Q + 3).choose 2 +
      (Q + 1).choose 2 * (n + 1) + 2 ≤ (n + 1) * (n + Q + 2) * (n + Q + 3) + 2 := by
  let C := (n + Q + 3).choose 2
  have h := Nat.add_one_mul_choose_eq (n + Q + 2) 1
  simp only [Nat.choose_one_right, Nat.reduceAdd] at h
  calc
    _ ≤ C * n + C + C * (n + 1) + 2 := by
      gcongr <;> apply Nat.choose_le_choose 2 <;> omega
    _ = (n + 1) * (C * 2) + 2 := by ring
    _ = _ := by dsimp [C]; rw [← h]; ring

variable {F G₁ G₂ Gₜ : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [DecidableEq G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq Gₜ]

/-- Generic recovery, including the KZG trapdoor-distribution penalty, has a closed polynomial
bound. The field size must exceed the numerator for this bound to be below one. -/
theorem recovery_le_generic {D : Type} (n : ℕ) (roots : CPolynomial F → List F)
    (claims : D → List (F × F)) (A : Adversary F D)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (he : e g₁ g₂ ≠ 0)
    (q : ℕ) (hq : IsQueryBoundP (A (input n)) (fun i => isGroupOp i = true) q) :
    Pr{let b ← (PairingDLog.experiment g₁ g₂
      (AGM.reductionFirst (n := n) g₂ roots claims (A.toAlgebraic e)))}[b = true] +
        1 / (Fintype.card F : ℝ≥0∞) ≤
      (((n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2 : ℕ) : ℝ≥0∞) /
        Fintype.card F := by
  rw [experiment_reductionFirst_toAlgebraic]
  have h := PairingDLog.experiment_ofGeneric_le_of_total e g₁ g₂ he n 1
    (program n roots claims A) (q + n + 1) (isQueryBoundP_program n roots claims A q hq)
  refine (add_le_add h le_rfl).trans ?_
  rw [← ENNReal.add_div]
  have hn := collision_numerator_le n (q + n + 1)
  have hn' : (n + (q + n + 1) + 2).choose 2 * n + (q + n + 1 + 3).choose 2 +
      (q + n + 1 + 1).choose 2 * (n + 1) + 2 ≤
      (n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2 := by
    convert hn using 1; ring
  apply ENNReal.div_le_div_right
  norm_cast
  simpa only [mul_one, show 1 + (q + (n + 3)) = q + (n + 4) by omega,
    Nat.add_assoc, Nat.reduceAdd] using hn'

/-- Root finding by enumerating the field. Root finding is scalar work and costs no group
operations, so the generic bounds below can use this finder without changing their budget. -/
noncomputable def enumRoots (p : CPolynomial F) : List F :=
  (Finset.univ.filter fun a => p.eval a = 0).toList

omit [SampleableType F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ] in
theorem enumRoots_complete :
    ∀ p : CPolynomial F, p ≠ 0 → ∀ a, p.eval a = 0 → a ∈ enumRoots p := by
  intro p _ a ha
  simp [enumRoots, ha]

/-- Unconditional evaluation binding for the existing KZG game against generic Type 3
adversaries. The operation budget includes additions, scalings, and pairings; equality queries
are free. This bound is nontrivial for
`Fintype.card F > (n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2`.
Neither translation nor AGM recovery requires a source generator to span its entire group. -/
theorem evalBinding_le_generic (n : ℕ)
    (A : Adversary F (F × F × F))
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (he : e g₁ g₂ ≠ 0)
    (q : ℕ) (hq : IsQueryBoundP (A (input n)) (fun i => isGroupOp i = true) q) :
    Pr{let b ← (evalBindingExperiment e g₁ g₂ (A.toEvalBindingAdversary (n := n) e))}[b = true] ≤
      (((n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2 : ℕ) : ℝ≥0∞) /
        Fintype.card F := by
  rw [← A.toAlgebraic_evalBinding e]
  exact (AGM.evalBinding_le_pairingDLog_first he enumRoots enumRoots_complete
    (A.toAlgebraic e)).trans (recovery_le_generic n enumRoots AGM.evalClaims A e g₁ g₂ he q hq)

/-- Unconditional function binding for the existing KZG game against generic Type 3
adversaries, with no bound on the number of claimed openings. This bound is nontrivial for
`Fintype.card F > (n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2`.
Only the first inconsistent claim is root-tested, so the reduction uses at most `q + n + 1`
group operations. No source-group surjectivity is assumed. -/
theorem functionBinding_le_generic (n : ℕ)
    (A : Adversary F (List (F × F)))
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (he : e g₁ g₂ ≠ 0)
    (q : ℕ) (hq : IsQueryBoundP (A (input n)) (fun i => isGroupOp i = true) q) :
    Pr{let b ← (functionBindingExperiment e g₁ g₂
      (A.toFunctionBindingAdversary (n := n) e))}[b = true] ≤
      (((n + 1) * (q + 2 * n + 3) * (q + 2 * n + 4) + 2 : ℕ) : ℝ≥0∞) /
        Fintype.card F := by
  rw [← A.toAlgebraic_functionBinding e]
  exact (AGM.functionBinding_le_pairingDLog_first he enumRoots enumRoots_complete
    (A.toAlgebraic e)).trans (recovery_le_generic n enumRoots id A e g₁ g₂ he q hq)

end KZG.Generic
