/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Support
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Identity


/-!
# Evaluating universal Taylor residuals

Specializing universal coefficient variables to the Taylor coefficients of an actual
polynomial recovers the canonical shifted differential residual. This connects the
universal support bounds to the existing differential-equation semantics.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open scoped BigOperators

variable {F : Type*} [CommRing F]

/-- Specialize coefficient variables while retaining the Taylor variable. -/
def specializeTaylorCoefficients {K : ℕ} (c : Fin K → F) :
    MvPolynomial (Option (Fin K)) F →ₐ[F] Polynomial F :=
  (Polynomial.mapAlgHom (MvPolynomial.aeval c)).comp
    (MvPolynomial.optionEquivLeft F (Fin K)).toAlgHom

/-- The specialized universal jet is the Hasse derivative of the coefficient polynomial. -/
theorem specializeTaylorCoefficients_universalTaylorJet {K : ℕ} (c : Fin K → F) (j : ℕ) :
    specializeTaylorCoefficients c (universalTaylorJet K j) =
      Polynomial.hasseDeriv j (∑ l : Fin K, Polynomial.monomial l.val (c l)) := by
  rw [specializeTaylorCoefficients, AlgHom.comp_apply]
  change ((MvPolynomial.optionEquivLeft F (Fin K)) (universalTaylorJet K j)).map
    (MvPolynomial.aeval c).toRingHom = _
  rw [optionEquivLeft_universalTaylorJet]
  rw [Polynomial.map_hasseDeriv]
  congr 1
  simp [universalTaylorPolynomial, Polynomial.map_sum, Polynomial.map_monomial]

/-- The universal residual evaluated at a polynomial's actual Taylor coefficients is
its canonical shifted differential substitution. -/
theorem specializeTaylorCoefficients_universalTaylorResidual
    {r K : ℕ} (center : F) (P : Polynomial F) (hP : P.degree < K)
    (Q : DifferentialPolynomial F r) :
    specializeTaylorCoefficients (fun l : Fin K ↦ (Polynomial.taylor center P).coeff l.val)
      (universalTaylorResidual K center Q) = shiftedJetSubstitution center P Q := by
  have hsum : (∑ l : Fin K, Polynomial.monomial l.val
      ((Polynomial.taylor center P).coeff l.val)) = Polynomial.taylor center P := by
    rw [Polynomial.sum_fin (fun i c ↦ Polynomial.monomial i c) (by simp)
      (by simpa [Polynomial.degree_taylor] using hP), Polynomial.sum_monomial_eq]
  have heq :
      (specializeTaylorCoefficients
        (fun l : Fin K ↦ (Polynomial.taylor center P).coeff l.val)).comp
        (MvPolynomial.aeval (fun i : Option (Fin (r + 1)) ↦
          i.elim (MvPolynomial.C center + MvPolynomial.X none)
            (fun j ↦ universalTaylorJet K j.val))) = shiftedJetSubstitution center P := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | none => simp [specializeTaylorCoefficients, shiftedJetSubstitution]
    | some j =>
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Option.elim_some,
        specializeTaylorCoefficients_universalTaylorJet, hsum]
      rw [Polynomial.hasseDeriv_taylor]
      simp [shiftedJetSubstitution]
  exact DFunLike.congr_fun heq Q

end

end ReedSolomon.HiddenDerivative
