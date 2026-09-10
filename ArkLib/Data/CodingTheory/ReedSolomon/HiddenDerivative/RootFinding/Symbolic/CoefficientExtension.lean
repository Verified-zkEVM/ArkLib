/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorHeight
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.SeparantChain


/-!
# Extending symbolic differential coefficients

Extending the ground field keeps the challenge symbolic. Subsequent challenge evaluation
agrees with direct evaluation through the field embedding, with no height or jet-degree loss.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace ReedSolomon.HiddenDerivative

open Polynomial MvPolynomial

variable {F E : Type*} [Field F] [Field E] {d : ℕ}

/-- Extend the ground field without evaluating the polynomial challenge parameter. -/
def extendSymbolicCoefficients (iota : F →+* E) (Q : DifferentialPolynomial F[X] d) :
    DifferentialPolynomial E[X] d := MvPolynomial.map (Polynomial.mapRingHom iota) Q

/-- Ground-field extension followed by challenge evaluation equals direct specialization. -/
theorem specialize_extendSymbolicCoefficients (iota : F →+* E)
    (Q : DifferentialPolynomial F[X] d) (z : E) :
    MvPolynomial.map (Polynomial.evalRingHom z) (extendSymbolicCoefficients iota Q) =
      MvPolynomial.map (Polynomial.eval₂RingHom iota z) Q := by
  rw [extendSymbolicCoefficients, MvPolynomial.map_map]
  have he : (Polynomial.evalRingHom z).comp (Polynomial.mapRingHom iota) =
      Polynomial.eval₂RingHom iota z := by
    apply Polynomial.ringHom_ext
    · intro a; simp
    · simp
  rw [he]

/-- Challenge-height upper bounds survive field extension. -/
theorem challengeHeightLE_extendSymbolicCoefficients (iota : F →+* E)
    (Q : DifferentialPolynomial F[X] d) {h : ℕ} (hQ : ChallengeHeightLE Q h) :
    ChallengeHeightLE (extendSymbolicCoefficients iota Q) h := by
  intro u
  rw [extendSymbolicCoefficients, MvPolynomial.coeff_map]
  exact Polynomial.natDegree_map_le.trans (hQ u)

/-- The symbolic jet-weight bound survives field extension. -/
theorem jetWeight_extendSymbolicCoefficients_le (iota : F →+* E)
    (Q : DifferentialPolynomial F[X] d) :
    SymbolicSeparantChain.jetWeight (extendSymbolicCoefficients iota Q) ≤
      SymbolicSeparantChain.jetWeight Q := by
  apply Finset.sup_le_iff.mpr
  intro u hu
  exact le_weightedTotalDegree _
    (support_map_subset (Polynomial.mapRingHom iota) Q hu)

/-- The literal selected separant commutes with ground-field extension. -/
theorem separant_extendSymbolicCoefficients (iota : F →+* E)
    (Q : DifferentialPolynomial F[X] d) (j : Fin (d + 1)) :
    separant (extendSymbolicCoefficients iota Q) j =
      extendSymbolicCoefficients iota (separant Q j) := by
  exact pderiv_map

end ReedSolomon.HiddenDerivative
