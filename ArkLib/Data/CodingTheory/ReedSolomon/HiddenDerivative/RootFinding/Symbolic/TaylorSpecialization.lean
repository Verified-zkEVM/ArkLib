/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorNumerator
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Taylor.Chart


/-!
# Specialization of symbolic Taylor numerators

Evaluating a retained polynomial parameter gives exactly the existing field-valued numerator.
The identities hold at singular separants and zero binomial pivots as well. Regularity and
invertible pivots enter only when the resulting rational chart is compared with a solution.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial

variable {F A E : Type*} [Field F] [CommRing A] [Algebra F A]
  [Field E] [Algebra F E] {r : ℕ}

/-- Any specialization to a field recovers the original literal Taylor numerator. -/
theorem map_rationalTaylorNumeratorOver_eq (φ : A →ₐ[F] E)
    (center : A) (Q : DifferentialPolynomial A r) (l : ℕ) :
    MvPolynomial.map φ.toRingHom (rationalTaylorNumeratorOver (F := F) center Q l) =
      rationalTaylorNumerator (φ center) (MvPolynomial.map φ.toRingHom Q) l := by
  rw [map_rationalTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]

/-- Any specialization to a field recovers the original common numerator. -/
theorem map_commonTaylorNumeratorOver_eq (φ : A →ₐ[F] E)
    (center : A) (Q : DifferentialPolynomial A r) (K : ℕ) (l : Fin K)
    (τ : ℕ := 2 * K) :
    MvPolynomial.map φ.toRingHom
        (commonTaylorNumeratorOver (F := F) center Q K l (τ := τ)) =
      commonTaylorNumerator (φ center) (MvPolynomial.map φ.toRingHom Q) K l (τ := τ) := by
  rw [map_commonTaylorNumeratorOver (τ := τ)]
  simp only [commonTaylorNumeratorOver, commonTaylorNumerator,
    rationalTaylorNumeratorOver_eq]
  rfl

/-- Evaluating the challenge specializes the numerator at every scalar challenge. -/
theorem eval₂AlgHom_rationalTaylorNumeratorOver (f : A →ₐ[F] E) (center : A) (z : E)
    (Q : DifferentialPolynomial (Polynomial A) r) (l : ℕ) :
    let φ := Polynomial.eval₂AlgHom f z (fun a ↦ Commute.all (f a) z)
    MvPolynomial.map φ.toRingHom
        (rationalTaylorNumeratorOver (F := F) (Polynomial.C center) Q l) =
      rationalTaylorNumerator (f center) (MvPolynomial.map φ.toRingHom Q) l := by
  dsimp only
  simpa using map_rationalTaylorNumeratorOver_eq
    (Polynomial.eval₂AlgHom f z (fun a ↦ Commute.all (f a) z)) (Polynomial.C center) Q l

/-- Evaluating the challenge specializes the numerator at every base-field challenge. -/
theorem eval_rationalTaylorNumeratorOver (center z : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (l : ℕ) :
    MvPolynomial.map (Polynomial.evalRingHom z)
        (rationalTaylorNumeratorOver (F := F) (Polynomial.C center) Q l) =
      rationalTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) l := by
  simpa using map_rationalTaylorNumeratorOver_eq (Polynomial.aeval z)
    (Polynomial.C center) Q l

/-- Evaluating the challenge specializes the common numerator at every scalar challenge. -/
theorem eval_commonTaylorNumeratorOver (center z : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (K : ℕ) (l : Fin K)
    (τ : ℕ := 2 * K) :
    MvPolynomial.map (Polynomial.evalRingHom z)
        (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Q K l (τ := τ)) =
      commonTaylorNumerator center
        (MvPolynomial.map (Polynomial.evalRingHom z) Q) K l (τ := τ) := by
  simpa using map_commonTaylorNumeratorOver_eq (Polynomial.aeval z)
    (Polynomial.C center) Q K l (τ := τ)

end

end ReedSolomon.HiddenDerivative
