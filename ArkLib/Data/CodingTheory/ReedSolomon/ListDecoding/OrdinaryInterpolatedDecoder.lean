/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FieldTransport
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.OrdinaryInterpolation
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.OrdinaryQuotientDecoder

/-!
# Ordinary interpolation followed by quotient lifting

This module composes the verified Lee--O'Sullivan interpolation stage with ordinary quotient
lifting and shared agreement recovery. The program computes its interpolation polynomial and
removes its common Y-content. Callers supply the decoding parameters, a working-field embedding,
and a center.
The resulting coefficient lists are over the original message field, even when interpolation and
lifting use an auxiliary extension.

The exactness theorem keeps the remaining preprocessing obligations visible. Dimension slack
makes interpolation succeed. The returned polynomial must have a nonzero slice at the supplied
center, and every wanted message must be regular there. Selecting such a center (after the paper's
squarefree normalization over F(X)) is a separate producer step. The generic interpolation
backend and Newton quotient lift do not yet carry the paper's near-linear runtime proof.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.OrdinaryInterpolatedDecoder
open CompPoly CompPoly.GuruswamiSudan Polynomial FieldTransport
variable {F E : Type*} [Field F] [Field E] [Fintype E]
variable [BEq F] [LawfulBEq F] [DecidableEq F] [BEq E] [LawfulBEq E] [DecidableEq E]
variable (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar]

/-- Interpolate over E, lift at the supplied center, and recover coefficients back over F. -/
def run {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (params : GSInterpParams) (center : E) : List (List F) :=
  match OrdinaryInterpolation.runCMv
      (OrdinaryInterpolation.receivedPoints (liftedDomain base domain) (fun i => base (received i)))
      params with
  | none => []
  | some Q => OrdinaryQuotientDecoder.run pchar base domain received k A Q center

variable {pchar}
/-- Exactness of the composed executable path, including descent to the message field.
The two center premises refer to the polynomial actually returned by interpolation. They retain
the normalization/discriminant obligations required before a public near-linear decoder can use
this program unconditionally. -/
theorem run_exact_of_regular_center {n k A : ℕ} (base : F →+* E) (domain : Fin n ↪ F)
    (received : Fin n → F) (params : GSInterpParams) (center : E)
    -- Multiplicity forces Q(X,P(X))=0 once its weighted degree is below mA.
    (hAk : k ≤ A) (hdegreeParam : params.messageDegree = k)
    (hbound : params.weightedDegreeBound < params.multiplicity * A)
    -- More interpolation monomials than constraints guarantee a nonzero computed witness.
    (hslack : HasInterpolationDimensionSlack
      (OrdinaryInterpolation.receivedPoints (liftedDomain base domain)
        (fun i => base (received i))) params)
    -- The section must be nonzero, and wanted messages must lie on regular branches at center.
    (hsection : ∀ Q,
      OrdinaryInterpolation.runCMv
          (OrdinaryInterpolation.receivedPoints (liftedDomain base domain)
            (fun i => base (received i))) params = some Q →
        ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.sectionPolynomial Q center ≠ 0)
    (hregular : ∀ Q,
      OrdinaryInterpolation.runCMv
          (OrdinaryInterpolation.receivedPoints (liftedDomain base domain)
            (fun i => base (received i))) params = some Q →
        ∀ P : F[X], P.degree < k →
          A ≤ Code.agree (evalOnPoints domain P) received →
          MvPolynomial.eval₂ (RingHom.id E) ![center, (P.map base).eval center]
            (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) ≠ 0) :
    ExactOutput domain received k A (run pchar base domain received k A params center) := by
  have hexists := OrdinaryInterpolation.runCMv_exists_of_dimension_slack
    (OrdinaryInterpolation.receivedPoints_distinct (liftedDomain base domain)
      (fun i => base (received i))) hslack
  generalize hrun : OrdinaryInterpolation.runCMv
      (OrdinaryInterpolation.receivedPoints (liftedDomain base domain)
        (fun i => base (received i))) params = result at hexists ⊢
  cases result with
  | none => obtain ⟨Q, hfalse⟩ := hexists; contradiction
  | some Q =>
      rw [run, hrun]
      apply OrdinaryQuotientDecoder.run_exact_of_regular_cover
        (pchar := pchar) base domain received k A hAk Q center (hsection Q hrun)
      · intro P hdegree hagreement
        exact OrdinaryInterpolation.runCMv_solution_of_agreement
          (liftedDomain base domain) (fun i => base (received i)) params hdegreeParam hbound hrun
          (P.map base) (by simpa using hdegree) (by simpa [liftedAgreement] using hagreement)
      · exact hregular Q hrun
end ReedSolomon.ListDecoding.OrdinaryInterpolatedDecoder
