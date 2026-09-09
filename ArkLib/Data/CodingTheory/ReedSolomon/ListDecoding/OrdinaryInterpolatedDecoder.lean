/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.OrdinaryInterpolation
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.OrdinaryQuotientDecoder

/-!
# Ordinary interpolation followed by quotient lifting

This module composes the verified Lee--O'Sullivan interpolation stage with ordinary quotient
lifting and shared agreement recovery. The program computes its interpolation polynomial; callers
supply only the decoding parameters and a center.

The exactness theorem keeps the remaining preprocessing obligations visible. Dimension slack
makes interpolation succeed. The returned polynomial must have a nonzero slice at the supplied
center, and every wanted message must be regular there. Selecting such a center (after the paper's
primitive and squarefree normalization) is a separate producer step. The generic interpolation
backend and sequential quotient lift do not yet carry the paper's near-linear runtime proof.
-/

namespace ReedSolomon.ListDecoding.OrdinaryInterpolatedDecoder

open CompPoly CompPoly.GuruswamiSudan Polynomial

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F] [DecidableEq F]
variable (pchar : ℕ) [Fact pchar.Prime] [CharP F pchar]

/-- Compute an ordinary interpolant and, on success, recover its regular quotient branches. -/
def run {n : ℕ} (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ)
    (params : GSInterpParams) (center : F) : List (List F) :=
  match OrdinaryInterpolation.runCMv
      (OrdinaryInterpolation.receivedPoints domain received) params with
  | none => []
  | some Q =>
      OrdinaryQuotientDecoder.run pchar (RingHom.id F) domain received k A Q center

variable {pchar}

/-- Exactness of the composed executable path at a supplied regular center.

The two center premises are predicates of the polynomial actually returned by interpolation,
rather than externally supplied polynomial data. -/
theorem run_exact_of_regular_center {n k A : ℕ} (domain : Fin n ↪ F)
    (received : Fin n → F) (params : GSInterpParams) (center : F)
    (hAk : k ≤ A) (hdegreeParam : params.messageDegree = k)
    (hbound : params.weightedDegreeBound < params.multiplicity * A)
    (hslack : HasInterpolationDimensionSlack
      (OrdinaryInterpolation.receivedPoints domain received) params)
    (hsection : ∀ Q,
      OrdinaryInterpolation.runCMv
          (OrdinaryInterpolation.receivedPoints domain received) params = some Q →
        ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.sectionPolynomial Q center ≠ 0)
    (hregular : ∀ Q,
      OrdinaryInterpolation.runCMv
          (OrdinaryInterpolation.receivedPoints domain received) params = some Q →
        ∀ P : F[X], P.degree < k →
          A ≤ Code.agree (evalOnPoints domain P) received →
          MvPolynomial.eval₂ (RingHom.id F) ![center, P.eval center]
            (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) ≠ 0) :
    ExactOutput domain received k A
      (run pchar domain received k A params center) := by
  have hexists : ∃ Q,
      OrdinaryInterpolation.runCMv
          (OrdinaryInterpolation.receivedPoints domain received) params = some Q :=
    OrdinaryInterpolation.runCMv_exists_of_dimension_slack
      (OrdinaryInterpolation.receivedPoints_distinct domain received) hslack
  generalize hrun : OrdinaryInterpolation.runCMv
      (OrdinaryInterpolation.receivedPoints domain received) params = result at hexists ⊢
  cases result with
  | none =>
      obtain ⟨Q, hfalse⟩ := hexists
      contradiction
  | some Q =>
      rw [run, hrun]
      apply OrdinaryQuotientDecoder.run_exact_of_regular_cover
        (pchar := pchar) (RingHom.id F) domain received k A hAk Q center
        (hsection Q hrun)
      · intro P hdegree hagreement
        simpa only [Polynomial.map_id] using
          OrdinaryInterpolation.runCMv_solution_of_agreement domain received params
            hdegreeParam hbound hrun P hdegree hagreement
      · intro P hdegree hagreement
        simpa only [Polynomial.map_id] using
          hregular Q hrun P hdegree hagreement

end ReedSolomon.ListDecoding.OrdinaryInterpolatedDecoder
