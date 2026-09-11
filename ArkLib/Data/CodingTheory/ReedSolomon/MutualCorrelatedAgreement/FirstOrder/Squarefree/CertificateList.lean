/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.TailBound

/-!
# Squarefree list bounds from finite first-order certificates

This module specializes a finite symbolic line certificate at a fixed received word and feeds
the resulting nonzero equation to the squarefree product/resultant count.  Reconstruction uses
the actual message degree `D = k - 1`; the interpolation weight may be larger.  Consequently the
positive-characteristic guard depends on the first-derivative cap, not the total jet cap.
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial Polynomial PolynomialDifferential
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
open ReedSolomon.HiddenDerivative.SymbolicWeightedSupportInterpolation

noncomputable section

universe u

open Classical in
/-- A positive-first-derivative finite certificate gives the squarefree fixed-word list bound.
The underlying semantic theorem retains the actual degrees of the reduced positive product;
this certificate-facing statement exposes the convenient source-cap envelope. -/
theorem firstOrder_finite_agreement_solutions_card_le_squarefree
    {F : Type u} [Field F] {D A m M μ k h n N : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F) D A m M μ k h domain received
      (fun _ ↦ 0) columns)
    (hk : 2 ≤ k) (hkn : k ≤ n) (hkA : k ≤ A) (hAn : A ≤ n)
    (hM : 0 < M) (hMμ : M ≤ μ)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℝ) ≤
      (firstOrderCurveFiberStageOne k μ M (2 * k - 3) : ℝ) *
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
    simpa [firstJetExponent, Finsupp.weight_apply, Finsupp.sum_fintype] using hcap
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    apply hsound indices P (hS P hP).1 (hS P hP).2
    intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  have hsquarefree := finite_squarefree_agreement_solutions_card_le
    domain received Q hQ (D := k - 1) (A := A) (B := μ) (M := M)
      (by omega) (by omega) hAn (by omega) hM hMμ hdegreeQ hfirstQ hchar S hsol
      (fun P hP ↦ by simpa only [show k - 1 + 1 = k by omega] using hS P hP)
  simpa only [show k - 1 + 1 = k by omega, show 2 * (k - 1) - 1 = 2 * k - 3 by omega,
    show n - (k - 1) = n - k + 1 by omega, show A - (k - 1) = A - k + 1 by omega]
    using hsquarefree

end

end ReedSolomon.FirstOrder.Squarefree
