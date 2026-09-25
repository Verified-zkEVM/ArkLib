/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.TailBound

/-!
# First-order squarefree list bounds from symbolic certificates

This module specializes a finite first-order symbolic certificate at a fixed received word and
applies the squarefree agreement bound to its nonzero equation. The certificate's first-derivative
cap controls the positive-characteristic condition independently of its total jet cap.

## Main statements

* `firstOrder_finite_agreement_solutions_card_le_squarefree`: a certificate bounds the size of
  every finite family of degree-bounded polynomials with sufficiently many agreements.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative

noncomputable section

universe u

open Classical in
/-- A finite certificate bounds every finite family of sufficiently agreeing polynomials of
bounded degree. -/
theorem firstOrder_finite_agreement_solutions_card_le_squarefree
    {F : Type u} [Field F] {D A m M μ k h n N : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F) D A m M μ k h domain received
      (fun _ ↦ 0) columns)
    (hk : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n) (hMμ : M ≤ μ)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < k ∧
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne k μ M (regularTaylorExponent (k - 1)) : ℝ) *
          ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) +
        ordinaryDegreeEnvelope μ M := by
  let φ := Polynomial.eval₂RingHom (RingHom.id F) 0
  let Q : DifferentialPolynomial F 1 := MvPolynomial.map φ cert.Q
  obtain ⟨hQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
  have hdegreeQ : jetTotalDegree Q ≤ μ := by
    rw [jetTotalDegree_le_iff]
    intro u hu
    have huQ : u ∈ cert.Q.support := MvPolynomial.support_map_subset φ cert.Q hu
    simpa [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.some_apply] using
      cert.totalJetDegree_le u huQ
  have hfirstQ : jetDegree Q (1 : Fin 2) ≤ M := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro exponent hexponent
    have hsource : exponent ∈ cert.Q.support :=
      MvPolynomial.support_map_subset φ cert.Q hexponent
    have hcap := cert.firstJetDegree_le exponent hsource
    have hfirst : exponent (some (⟨1, by omega⟩ : Fin 2)) ≤ M := by
      simpa only [firstJetExponent_eq_coordinates Nat.one_pos,
        jetExponentCoordinatesEquiv_apply] using hcap
    have hcoord : (⟨1, by omega⟩ : Fin 2) = 1 := Fin.ext rfl
    simpa only [hcoord] using hfirst
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    apply hsound indices P (hS P hP).1 (hS P hP).2
    intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  have hsquarefree := finite_squarefree_agreement_solutions_card_le
    domain received Q hQ (D := k - 1) (A := A) (B := μ) (M := M)
      (by omega) (by omega) hAn hMμ hdegreeQ hfirstQ hchar S hsol
      (fun P hP ↦ by
        have hkdegree : (↑(k - 1) : WithBot ℕ) + 1 = k := by
          exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ k by omega))
        simpa only [hkdegree] using hS P hP)
  simpa only [show k - 1 + 1 = k by omega,
    show n - (k - 1) = n - k + 1 by omega, show A - (k - 1) = A - k + 1 by omega]
    using hsquarefree

end

end ReedSolomon.FirstOrder.Squarefree
