/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ComponentDimension

open Polynomial PolynomialDifferential ReedSolomon

namespace ReedSolomon.MutualCorrelatedAgreementTest

/-- The empty list of cuts leaves the full two-coordinate source affine space. -/
example :
    (MvPolynomial.affineHilbertPolynomial
      (⊥ : Ideal (SourceRing 0 ℚ))).natDegree ≤ 2 := by
  let Q : DifferentialPolynomial ℚ[X] 0 :=
    MvPolynomial.X (some (0 : Fin 1))
  have hτ : TaylorExponentSufficient 0 1 0 := by
    intro l
    fin_cases l
    decide
  have hhigh (l : Fin 1) (hl : 1 ≤ l.val) :
      symbolicSourceNumerator 0 Q 1 l (τ := 0) ∈ (⊥ : Ideal (SourceRing 0 ℚ)) := by
    fin_cases l
    omega
  have hsep : symbolicSourceSeparant 0 Q ∉ (⊥ : Ideal (SourceRing 0 ℚ)) := by
    simp [symbolicSourceSeparant, initialJetSeparant, separant, Q]
  let α : Fin 0 ↪ ℚ := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  let f : Fin 0 → ℚ := Fin.elim0
  let g : Fin 0 → ℚ := Fin.elim0
  have h := symbolicSource_prime_affineHilbertPolynomial_natDegree_le_of_agreements_of_exponent
    (center := (0 : ℚ)) (Q := Q) (K := 1) (k := 1) (c := 0) (τ := 0)
    hτ (by omega) (by omega) (by omega) (⊥ : Ideal (SourceRing 0 ℚ)) inferInstance
    hsep hhigh α f g (by intro i; exact Fin.elim0 i)
  exact h

end ReedSolomon.MutualCorrelatedAgreementTest
