/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.GraphAdmissibility
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.OneJetGraphCounting
/-!
# Counting retained Frobenius pairs

Reconstruction injects admissible base-field pairs into polynomial graphs on the actual
source equation. The number of pairs is bounded by its root degree without an inseparability
factor.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

/-- The separable root degree bounds every finite family of actual admissible pairs.
No degree of the retained challenge map appears in this count. -/
theorem admissibleFrobeniusPairs_card_le_degreeOf [Infinite E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (pairs : Finset (F[X] × F[X]))
    (hpairs : ∀ P ∈ pairs,
      IsAdmissibleFrobeniusPair domain f g ι roots center Q K k τ (p ^ e) P.1 P.2) :
    pairs.card ≤ (symbolicSourceInitialEquation center Q).degreeOf (some 0) := by
  classical
  let graph : F[X] × F[X] → E[X] := fun P ↦
    frobeniusInitialGraph center (p ^ e) (P.1.map ι) (P.2.map ι) 0
  have hinj : Set.InjOn graph (pairs : Set (F[X] × F[X])) := by
    intro P hP R hR heq
    have hgraphs : frobeniusInitialGraph center (p ^ e) (P.1.map ι) (P.2.map ι) =
        frobeniusInitialGraph center (p ^ e) (R.1.map ι) (R.2.map ι) := by
      funext j
      exact heq
    obtain ⟨hleft, hright⟩ := (hpairs P hP).eq_of_initialGraph_eq (hpairs R hR)
      hroots hK hKk hτ hgraphs
    exact Prod.ext hleft hright
  have hcount := polynomialGraphs_card_le_degreeOf
    (symbolicSourceInitialEquation center Q) hinit (pairs.image graph) (by
      intro q hq
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
      exact (hpairs P hP).initial)
  rwa [Finset.card_image_of_injOn hinj] at hcount

end ReedSolomon
