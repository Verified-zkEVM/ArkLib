/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.Interpolant
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ColumnHeight

/-!
# First-order certificate data and support assembly

This module defines the specialization-sound certificate returned by finite first-order
interpolation. Its support consists of the monomials

```text
X^x Y₀^a Y₁^b,  b ≤ M,  a + b ≤ μ,
                    x + D a + (D - 1) b < m A.
```

The structure records primitivity, coefficient height, support, local constraints, and uniform
specialization soundness. `coeff_interpolant_natDegree_le` and
`interpolant_mem_firstOrderSpace` are the support-independent assembly lemmas used by the shifted
finite constructor.

## Main statements

* `FirstOrderSymbolicCertificate`: a primitive first-order interpolant with uniform
  specialization soundness.
* `coeff_interpolant_natDegree_le`: distinct source columns preserve the coefficient height of
  the coefficient vector.
* `interpolant_mem_firstOrderSpace`: assembling eligible source columns preserves the finite
  first-order support.

## References

* [DKT26], Section 6.1.3, Proposition 6.3.
-/

@[expose] public section

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} [Field F]

/-- A primitive first-order symbolic interpolant and its uniform soundness property.

`primitiveCoefficients` records primitivity of the finite coefficient vector used to assemble
`Q`. When `columns` is injective, this gives nonvanishing after every extension-field challenge
specialization. `specialization_sound` records nonvanishing and vanishing after specialization to
any polynomial within the stated degree and agreement bounds. -/
structure FirstOrderSymbolicCertificate {n N : ℕ} (D A m M μ k h : ℕ)
    (centers : Fin n ↪ F) (f g : Fin n → F) (columns : Fin N → SourceColumn 1) where
  coefficients : Fin N → F[X]
  Q : DifferentialPolynomial F[X] 1
  eq_interpolant : Q = SourceColumn.interpolant columns coefficients
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  challengeDegree_le : ∀ u, (Q.coeff u).natDegree ≤ h
  support : Q ∈ firstOrderSpace F[X] D A m M μ
  firstJetDegree_le : ∀ u ∈ Q.support, firstJetExponent u ≤ M
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ μ
  localConstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
    (receivedLine (f i) (g i)) Q
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Distinct source columns preserve the coefficient height of the coefficient vector. -/
theorem coeff_interpolant_natDegree_le {N h : ℕ}
    (columns : Fin N → SourceColumn 1) (hcolumns : Function.Injective columns)
    (v : Fin N → F[X]) (hv : ∀ j, (v j).natDegree ≤ h) :
    ∀ u, ((SourceColumn.interpolant columns v).coeff u).natDegree ≤ h := by
  classical
  intro u
  by_cases hu : u ∈ Set.range (fun j ↦ (columns j).exponent)
  · obtain ⟨j, rfl⟩ := hu
    rw [SourceColumn.coeff_interpolant hcolumns v j]
    exact hv j
  · have hcoeff : (SourceColumn.interpolant columns v).coeff u = 0 := by
      rw [SourceColumn.interpolant, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [MvPolynomial.coeff_monomial]
      split
      · rename_i heq
        exact (hu ⟨j, heq⟩).elim
      · rfl
    simp [hcoeff]

/-- Assembling eligible source columns preserves the finite first-order support. -/
theorem interpolant_mem_firstOrderSpace {D A m M μ N : ℕ}
    (columns : Fin N → SourceColumn 1)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ)
    (v : Fin N → F[X]) :
    SourceColumn.interpolant columns v ∈ firstOrderSpace F[X] D A m M μ := by
  rw [SourceColumn.interpolant]
  apply Submodule.sum_mem
  intro j _
  rw [mem_firstOrderSpace_iff]
  intro u hu
  have hueq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hu
  simpa [hueq] using mem_firstOrderExponents.mp (heligible j)

end

end ReedSolomon.HiddenDerivative
