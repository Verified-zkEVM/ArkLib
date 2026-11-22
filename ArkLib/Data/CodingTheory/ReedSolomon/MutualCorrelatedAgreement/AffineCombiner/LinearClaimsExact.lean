/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Computable
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LinearClaims

/-!
# Exact evaluation of the linear-claim combiner error

`linearClaimMcaErrorRat` enumerates the received words, public weights, and initial claims.
For each such choice it enumerates all `q^q` message functions, where `q` is the field size.
`ofReal_linearClaimMcaErrorRat` identifies the result with the worst-case exceptional-event
probability `linearClaimMcaError`.

For each instance and challenge triple, the search tests up to `q^(d+1)` candidates against
`q^d` combinations `W = U + θ V` per candidate. The candidate `P` and `W` determine
`V = P - (α + β X) W` and `U = W - θ V`. The search skips the pair if `V` has degree at
least `d`. It uses executable finite enumerations and field operations.
-/

@[expose] public section

namespace ReedSolomon

open CompPoly Finset

variable {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]

namespace Computable

/-- Evaluate the weighted sum of the first `d + 1` coefficients of a computable polynomial. -/
def linearClaim {d : ℕ} (v : Fin (d + 1) → F) (P : CPolynomial F) : F :=
  ∑ j : Fin (d + 1), P.coeff j * v j

omit [DecidableEq F] in
/-- Coefficient conversion preserves a linear claim. -/
@[simp]
theorem linearClaim_eq_toPoly {d : ℕ} (v : Fin (d + 1) → F) (P : CPolynomial F) :
    linearClaim v P = ReedSolomon.linearClaim v P.toPoly := by
  classical
  simp [linearClaim, ReedSolomon.linearClaim, CPolynomial.coeff_toPoly]

/-- A bounded candidate is exceptional if it agrees, satisfies the combined claim, and every
bounded witness pair with correct claims loses more than `s` agreements. -/
def IsLinearClaimExceptional (domain : ι ↪ F) {d : ℕ} (w : LinearClaimInstance ι F d)
    (A s : ℕ) (θ α β : F) (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) : Prop :=
  let c := w.message θ
  A ≤ #{i | P.val.eval (domain i) = equalDegreeWord domain w.f w.g θ α β i} ∧
    linearClaim w.v P.val = w.γ₁ + α * (w.γ₀ + θ * w.γ₁) + β * c ∧
    ∀ U V : ↥(CPolynomial.degreeLT (R := F) d),
      P.val = equalDegreePolynomial θ α β U.val V.val →
      linearClaim w.v U.val = w.γ₀ → linearClaim w.v V.val = w.γ₁ →
      linearClaim w.v (CPolynomial.X * (U.val + CPolynomial.C θ * V.val)) = c →
      s < #(lostPositions domain w.f w.g (equalDegreeWord domain w.f w.g θ α β)
        P.val U.val V.val)

/-- The decision procedure searches the combinations `W = U + θ V ∈ degreeLT d`. Each
`W` determines the witnesses `V = P - (α + β X) W` and `U = W - θ V`. The search skips `W` if
`V` has degree at least `d`. The claim on `X (U + θ V)` is the claim on `X W`. -/
instance [Fintype F] (domain : ι ↪ F) {d : ℕ} (w : LinearClaimInstance ι F d) (A s : ℕ)
    (θ α β : F) (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    Decidable (IsLinearClaimExceptional domain w A s θ α β P) :=
  let c := w.message θ
  let word := equalDegreeWord domain w.f w.g θ α β
  decidable_of_iff
    (A ≤ #{i | P.val.eval (domain i) = word i} ∧
      linearClaim w.v P.val = w.γ₁ + α * (w.γ₀ + θ * w.γ₁) + β * c ∧
      ∀ W : ↥(CPolynomial.degreeLT (R := F) d),
        let V := P.val - affineMultiplier α β * W.val
        let U := W.val - CPolynomial.C θ * V
        V.degree < d → linearClaim w.v U = w.γ₀ → linearClaim w.v V = w.γ₁ →
          linearClaim w.v (CPolynomial.X * W.val) = c →
          s < #(lostPositions domain w.f w.g word P.val U V))
    (and_congr_right fun _ ↦ and_congr_right fun _ ↦ by
      rw [forall_eq_equalDegreePolynomial_iff P.val θ α β d fun U V ↦
        linearClaim w.v U = w.γ₀ → linearClaim w.v V = w.γ₁ →
          linearClaim w.v (CPolynomial.X * (U + CPolynomial.C θ * V)) = c →
          s < #(lostPositions domain w.f w.g word P.val U V)]
      simp only [sub_add_cancel])

/-- The executable predicate agrees with exceptionality of the converted candidate. -/
theorem isLinearClaimExceptional_iff (domain : ι ↪ F) {d : ℕ} (w : LinearClaimInstance ι F d)
    (A s : ℕ) (θ α β : F) (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    IsLinearClaimExceptional domain w A s θ α β P ↔
      ReedSolomon.IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁ (w.message θ)
        θ α β P.val.toPoly := by
  rw [IsLinearClaimExceptional, ReedSolomon.IsLinearClaimExceptional,
    card_eval_eq_card_polynomialAgreementSet]
  simp only [CPolynomial.degree_toPoly_le P, true_and, linearClaim_eq_toPoly]
  simp only [← CPolynomial.toPoly_inj (p := P.val), toPoly_equalDegreePolynomial,
    CPolynomial.toPoly_mul, CPolynomial.toPoly_add, CPolynomial.C_toPoly, CPolynomial.X_toPoly,
    lostPositions_eq_filter, HasCorrectLinearClaims, and_imp]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
    CPolynomial.forall₂_degreeLT_toPoly_iff d d fun U V ↦
      P.val.toPoly = V + ReedSolomon.affineMultiplier α β * (U + Polynomial.C θ * V) →
      ReedSolomon.linearClaim w.v U = w.γ₀ →
      ReedSolomon.linearClaim w.v V = w.γ₁ →
      ReedSolomon.linearClaim w.v (Polynomial.X * (U + Polynomial.C θ * V)) = w.message θ →
      s < #{i ∈ polynomialAgreementSet domain (equalDegreeWord domain w.f w.g θ α β)
          P.val.toPoly | U.eval (domain i) ≠ w.f i ∨ V.eval (domain i) ≠ w.g i}

end Computable

variable [Fintype F]

/-- Compute the worst-case linear-claim error by exhaustive finite counting. -/
def linearClaimMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) : ℚ≥0 :=
  letI : DecidableEq ι := domain.injective.decidableEq
  Probability.maxEventProbability fun (w : LinearClaimInstance ι F d) (c : F × F × F) ↦
    decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      Computable.IsLinearClaimExceptional domain w A s c.1 c.2.1 c.2.2 P)

/-- The exact rational evaluator computes the semantic linear-claim error. -/
theorem ofReal_linearClaimMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) :
    ENNReal.ofReal (linearClaimMcaErrorRat domain d A s : ℝ) =
      linearClaimMcaError domain d A s := by
  classical
  let : DecidableEq ι := domain.injective.decidableEq
  rw [linearClaimMcaErrorRat, Probability.ofReal_maxEventProbability_eq_iSup_of_iff _
    (fun w c ↦ ∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
      (w.message c.1) c.1 c.2.1 c.2.2 P) fun w c ↦ by
        rw [decide_eq_true_eq]
        simp_rw [Computable.isLinearClaimExceptional_iff]
        exact CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le d _ fun _ hP ↦ hP.1]
  simp only [linearClaimMcaError, Fintype.card_prod, Nat.cast_mul, pow_succ, pow_zero, one_mul,
    mul_assoc]

end ReedSolomon
