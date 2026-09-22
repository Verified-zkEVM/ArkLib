/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SolutionEmbedding
import ArkLibTest.Data.CodingTheory.HiddenDerivative.Interpolation.Certificates

/-!
# Acceptance cases for the solution embedding

* `mem_agreeingPolynomials_iff` on a concrete constant: `r` agrees with the constant word `r`
  everywhere.
* With the certificate `Y₀ - r` on the points `0, 1` of `ℤ` (from the certificates test), the
  embedding shows that the agreement list with threshold `2` is exactly `{r}`, so its extended
  cardinality is `1`; `encard_agreeingPolynomials_le` then says `BoundedSolution` is nonempty.
* On the prime-field certificate over `ZMod 5`, `solutionEmbedding` and `exists_solution` are
  reached by dot notation through the parent structure.
* `exists_solution` and `solutionEmbedding` for a general prime-field certificate over `ZMod q`.
-/

open Polynomial PolynomialDifferential ReedSolomon ReedSolomon.HiddenDerivative ListDecoding
  CertificatesTest

/-- The constant `r` as a message polynomial of degree below `2`. -/
noncomputable def constantMessage (r : ℤ) : MessagePolynomial ℤ 2 :=
  ⟨C r, mem_degreeLT.2 ((degree_C_le).trans_lt (by decide))⟩

/-- The constant `r` agrees with the constant word `r` at both points. -/
theorem constantMessage_mem (r : ℤ) :
    constantMessage r ∈ agreeingPolynomials intDomain 2 2 (fun _ ↦ r) := by
  rw [mem_agreeingPolynomials_iff]
  have : polynomialAgreementSet intDomain (fun _ ↦ r) (constantMessage r : ℤ[X]) =
      Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro i
    simp [polynomialAgreementSet, constantMessage]
  simp [this]

/-- The agreement list with threshold `2` for the constant word `r` on `{0, 1} ⊆ ℤ` is `{r}`:
the embedding sends each member `P` to a solution of `Y₀ - r`, so `P = r`. -/
example (r : ℤ) : agreeingPolynomials intDomain 2 2 (fun _ ↦ r) = {constantMessage r} := by
  ext P
  refine ⟨fun hP ↦ ?_, fun hP ↦ hP ▸ constantMessage_mem r⟩
  have h := ((constantCertificate intDomain r).solutionEmbedding ⟨P, hP⟩).equation
  rw [InterpolationCertificate.solutionEmbedding_polynomial] at h
  have hP' : (P : ℤ[X]) - C r = 0 := by
    simpa [constantCertificate, differentialSpecialization, differentialSpecializationHom] using h
  exact Subtype.ext (sub_eq_zero.mp hP')

/-- `encard_agreeingPolynomials_le` on the concrete certificate: a list member gives a bounded
solution. -/
example (r : ℤ) :
    1 ≤ ENat.card (BoundedSolution (constantCertificate intDomain r).interpolant 1) := by
  have h := (constantCertificate intDomain r).encard_agreeingPolynomials_le
  refine le_trans ?_ h
  rw [Set.one_le_encard_iff_nonempty]
  exact ⟨_, constantMessage_mem r⟩

/-- The embedding on the prime-field certificate, reached through the parent structure, keeps the
polynomial. -/
example (r : ZMod 5) (p : agreeingPolynomials zmodDomain 2 2 (fun _ ↦ r)) :
    ((zmodCertificate r).solutionEmbedding p).polynomial = (p.1 : (ZMod 5)[X]) := by
  simp

/-- `exists_solution` for a prime-field certificate over `ZMod q`. -/
example {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction :
      HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received)
    (p : agreeingPolynomials domain k A received) :
    ∃ solution : BoundedSolution construction.interpolant (construction.ambientDim - 1),
      solution.polynomial = (p.1 : (ZMod q)[X]) :=
  construction.exists_solution p

/-- `solutionEmbedding` for a prime-field certificate over `ZMod q`. -/
noncomputable example {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction :
      HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received) :
    agreeingPolynomials domain k A received ↪
      BoundedSolution construction.interpolant (construction.ambientDim - 1) :=
  construction.solutionEmbedding
