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

`linearClaimMcaErrorRat` enumerates received words, public weights, and initial claims. For each
first challenge `θ` and reply `c`, it counts exceptional pairs `(α, β)`. The event at `θ` reads
the message function only at `θ`. Maximizing the count over replies separately at each `θ` and
summing gives the maximum over message functions. This gives `q^4` challenge and reply cases per
fixed choice of words, weights, and initial claims, where `q` is the field size.

For each case, the evaluator tests up to `q^(d+1)` candidates. For each candidate it enumerates
up to `q^d` combinations `W = U + θ V`. The candidate and `W` determine `V` and `U`, and the
search skips the pair if `V` has degree at least `d`. The evaluator uses executable finite
enumerations and field operations.
`ofReal_linearClaimMcaErrorRat` identifies the result with the worst-case exceptional-event
probability `linearClaimMcaError`.
`Computable.hasLinearClaimExceptionalCandidate_eq_true_iff` connects the Boolean search
at a fixed challenge to the semantic exceptional-candidate event.
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

/-- Whether some candidate is exceptional for the given challenge triple. -/
def hasLinearClaimExceptionalCandidate [Fintype F] (domain : ι ↪ F) {d : ℕ}
    (w : LinearClaimInstance ι F d) (A s : ℕ) (θ α β : F) : Bool :=
  decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
    IsLinearClaimExceptional domain w A s θ α β P)

/-- The Boolean search succeeds exactly when a semantic candidate is exceptional for the
given challenge triple and the message at its first challenge. -/
theorem hasLinearClaimExceptionalCandidate_eq_true_iff [Fintype F] (domain : ι ↪ F) {d : ℕ}
    (w : LinearClaimInstance ι F d) (A s : ℕ) (θ α β : F) :
    hasLinearClaimExceptionalCandidate domain w A s θ α β = true ↔
      ∃ P, ReedSolomon.IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
        (w.message θ) θ α β P := by
  simp only [hasLinearClaimExceptionalCandidate, decide_eq_true_eq]
  simp_rw [isLinearClaimExceptional_iff]
  exact CPolynomial.exists_degreeLT_succ_toPoly_iff_of_degree_le d _ fun _ hP ↦ hP.1

end Computable

variable [Fintype F]

/-- The exact worst-case linear-claim error. The numerator sums the largest exceptional
counts over replies for each first challenge and then maximizes over the fixed data. The
denominator is the number of challenge triples. -/
def linearClaimMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) : ℚ≥0 :=
  letI : DecidableEq ι := domain.injective.decidableEq
  let count := Probability.maxEventCountWithReply
    (fun (w : (ι → F) × (ι → F) × (Fin (d + 1) → F) × F × F) (θ c : F) (ab : F × F) ↦
      let instanceData := (LinearClaimInstance.equivProd ι F d).symm (w, fun _ ↦ c)
      Computable.hasLinearClaimExceptionalCandidate domain instanceData A s θ ab.1 ab.2)
  (count : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ 3

/-- The exact rational evaluator computes the semantic linear-claim error. -/
theorem ofReal_linearClaimMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) :
    ENNReal.ofReal (linearClaimMcaErrorRat domain d A s : ℝ) =
      linearClaimMcaError domain d A s := by
  classical
  let : DecidableEq ι := domain.injective.decidableEq
  let e := (LinearClaimInstance.equivProd ι F d).symm
  let bad (w : LinearClaimInstance ι F d) (c : F × F × F) :=
    Computable.hasLinearClaimExceptionalCandidate domain w A s c.1 c.2.1 c.2.2
  have hcount :
      Probability.maxEventCount (fun w c ↦ bad (e w) c) = Probability.maxEventCount bad := by
    simp only [Probability.maxEventCount]
    rw [← map_univ_equiv e, sup_map]
    rfl
  have heval : linearClaimMcaErrorRat domain d A s = Probability.maxEventProbability bad := by
    rw [linearClaimMcaErrorRat, ← Probability.maxEventCount_eq_maxEventCountWithReply]
    have hmessage :
        (fun w (c : F × F × F) ↦
          Computable.hasLinearClaimExceptionalCandidate domain (e (w.1, fun _ ↦ w.2 c.1))
            A s c.1 c.2.1 c.2.2) = fun w c ↦ bad (e w) c := by
      funext w c
      apply Bool.eq_iff_iff.mpr
      exact (Computable.hasLinearClaimExceptionalCandidate_eq_true_iff domain
        (e (w.1, fun _ ↦ w.2 c.1)) A s c.1 c.2.1 c.2.2).trans
        (Computable.hasLinearClaimExceptionalCandidate_eq_true_iff domain (e w)
          A s c.1 c.2.1 c.2.2).symm
    rw [hmessage, hcount, Probability.maxEventProbability]
    simp only [Fintype.card_prod, Nat.cast_mul, pow_succ, pow_zero, one_mul, mul_assoc]
  rw [heval, Probability.ofReal_maxEventProbability_eq_iSup_of_iff _
    (fun w c ↦ ∃ P, IsLinearClaimExceptional domain w.f w.g d A s w.v w.γ₀ w.γ₁
      (w.message c.1) c.1 c.2.1 c.2.2 P) fun w c ↦
        Computable.hasLinearClaimExceptionalCandidate_eq_true_iff domain w A s c.1 c.2.1 c.2.2]
  simp only [linearClaimMcaError, Fintype.card_prod, Nat.cast_mul, pow_succ, pow_zero, one_mul,
    mul_assoc]

end ReedSolomon
