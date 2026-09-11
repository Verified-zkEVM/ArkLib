/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Admissible
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.OneJetGraphCounting
/-!
# Counting retained Frobenius power tuples

Sparse reconstruction injects admissible original-degree tuples into polynomial graphs on the
source equation.  Their number is therefore bounded by the separable root degree, independently
of both the Frobenius exponent and the power-curve degree.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

/-- The separable root degree bounds every finite family of admissible power tuples. -/
theorem admissibleFrobeniusPowerTuples_card_le_degreeOf [Infinite E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleFrobeniusPowerTuple
        domain values ι roots center Q K k τ (p ^ e) P) :
    tuples.card ≤ (symbolicSourceInitialEquation center Q).degreeOf (some 0) := by
  classical
  let graph : (Fin (ℓ + 1) → F[X]) → E[X] := fun P ↦
    frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι) 0
  have hinj : Set.InjOn graph (tuples : Set (Fin (ℓ + 1) → F[X])) := by
    intro P hP R hR heq
    have hgraphs :
        frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι) =
          frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (R t).map ι) := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact heq
    exact (htuples P hP).eq_of_initialGraph_eq (htuples R hR)
      hroots hK hKk hτ hgraphs
  have hcount := polynomialGraphs_card_le_degreeOf
    (symbolicSourceInitialEquation center Q) hinit (tuples.image graph) (by
      intro q hq
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
      exact (htuples P hP).initial)
  rwa [Finset.card_image_of_injOn hinj] at hcount

end ReedSolomon
