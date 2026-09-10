/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorCuts

/-!
# Sparse reconstruction from symbolic Taylor cuts

Vanishing common numerators outside multiples of `s` forces the corresponding Taylor
coefficients to vanish on the regular chart. The finite prefix supplies all remaining zeros.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

open Polynomial PolynomialDifferential MvPolynomial

variable {F E A : Type*} [Field F] [Field E] [CommRing A]
  [Algebra F E] [Algebra F A] {r : ℕ}

/-- Sparse symbolic cuts imply sparse Taylor coefficients of the actual reconstructed
polynomial, including every coefficient beyond the finite prefix. -/
theorem sparse_rationalTaylorPolynomial_of_symbolic_cuts
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K s τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (MvPolynomial.map φ.toRingHom (initialJetSeparantOver center Q)) ≠ 0)
    (hcuts : ∀ l : Fin K, ¬s ∣ l.val →
      aeval jet (MvPolynomial.map φ.toRingHom
        (commonTaylorNumeratorOver (F := F) center Q K l (τ := τ))) = 0) :
    ∀ i : ℕ, ¬s ∣ i →
      (Polynomial.taylor (φ center)
        (rationalTaylorPolynomial (φ center)
          (MvPolynomial.map φ.toRingHom Q) K jet)).coeff i = 0 := by
  intro i hi
  by_cases hiK : i < K
  · have hnum := hcuts ⟨i, hiK⟩ hi
    rw [aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent
      φ center Q K τ hτ jet hS ⟨i, hiK⟩] at hnum
    exact (mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hS)
  · simp only [rationalTaylorPolynomial, coeff_taylor_centeredCoefficientPrefix,
      if_neg hiK]

end ReedSolomon.HiddenDerivative
