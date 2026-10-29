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
  obtain ⟨Q, hQ, hdegreeQ, hfirstQ, hsound⟩ :=
    firstOrderSymbolicCertificate_specialization_at_zero domain received columns cert
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    have hagreementCount :
        A ≤ ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)).ncard := by
      let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
      have hagreement :
          ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)) =
            (indices : Set (Fin n)) := by
        ext i
        simp [indices]
      rw [hagreement, Set.ncard_coe_finset]
      exact (hS P hP).2
    exact hsound P (hS P hP).1 hagreementCount
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
