/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Certificates
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList

/-!
# Embedding agreeing polynomials into bounded differential solutions

An interpolation certificate makes every message polynomial with enough agreements a root of its
differential interpolant `Q` (`InterpolationCertificate.specializes_to_zero`). Since message
polynomials have degree at most the ambient degree `D = ambientDim - 1`, each one is, unchanged, a
bounded solution of `Q` of degree at most `D`. This gives an injection from the agreement list into
`BoundedSolution Q D`, so every bound on the number of bounded solutions bounds the list. The
construction does not depend on how the interpolant was found.

## Main definitions

* `HiddenDerivative.InterpolationCertificate.toBoundedSolution`: an agreeing polynomial as a
  bounded solution.
* `HiddenDerivative.InterpolationCertificate.solutionEmbedding`: the injection
  `agreeingPolynomials domain k A received ↪ BoundedSolution Q (ambientDim - 1)`.

## Main statements

* `HiddenDerivative.InterpolationCertificate.solutionEmbedding_polynomial`: the embedding keeps
  the polynomial.
* `HiddenDerivative.InterpolationCertificate.exists_solution`: the source-shaped existence form.
* `HiddenDerivative.InterpolationCertificate.encard_agreeingPolynomials_le`: the list is no larger
  than the set of bounded solutions.

## References

Ports `Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/SolutionEmbedding.lean` at
ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d.

* `HiddenDerivativeInterpolationCertificate.exists_solution` and
  `HiddenDerivativeInterpolationCertificate.solutionEmbedding` are stated for
  `InterpolationCertificate` over any domain, which a prime-field certificate extends; dot notation
  on a prime-field certificate finds them through the parent structure. The source defined the
  embedding by choice from `exists_solution`; here it is defined directly through
  `toBoundedSolution`, so `solutionEmbedding_polynomial` is a definitional fact.
* The private source lemma `exists_boundedSolution_of_polynomial` is inlined: a bounded solution
  is a subtype of `Polynomial.degreeLT`.
* `encard_agreeingPolynomials_le` is new; it is the cardinality step of the source's
  `ListDecodability/Capacity/CertificateRootBound.lean`.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.HiddenDerivative.InterpolationCertificate

open ListDecoding

variable {ι R : Type*} [Fintype ι] [CommRing R] {k A d m : ℕ} {domain : ι ↪ R}
  {received : ι → R}

/-- A message polynomial of degree below `k` lies in `degreeLT R (ambientDim - 1 + 1)`. -/
theorem mem_degreeLT (c : InterpolationCertificate k A d m domain received)
    (P : MessagePolynomial R k) : (P : R[X]) ∈ degreeLT R (c.ambientDim - 1 + 1) :=
  degreeLT_mono (by have := c.messageDim_le; have := c.one_le_ambientDim; omega) P.property

variable [IsDomain R] [DecidableEq R]

/-- An agreeing message polynomial, unchanged, as a bounded solution of the interpolant of degree
at most `ambientDim - 1`. -/
def toBoundedSolution (c : InterpolationCertificate k A d m domain received)
    (p : agreeingPolynomials domain k A received) :
    BoundedSolution c.interpolant (c.ambientDim - 1) :=
  ⟨⟨p.1, c.mem_degreeLT p.1⟩, c.specializes_to_zero p.1 p.2⟩

/-- `toBoundedSolution` keeps the polynomial. -/
@[simp]
theorem toBoundedSolution_polynomial (c : InterpolationCertificate k A d m domain received)
    (p : agreeingPolynomials domain k A received) :
    (c.toBoundedSolution p).polynomial = (p.1 : R[X]) := by
  unfold toBoundedSolution BoundedSolution.polynomial
  rfl

/-- The embedding of the agreement list into the bounded solutions of the interpolant. A message
polynomial with at least `A` agreements is sent to itself, viewed as a solution of degree at most
`ambientDim - 1`. It is injective because it keeps the polynomial. -/
def solutionEmbedding (c : InterpolationCertificate k A d m domain received) :
    agreeingPolynomials domain k A received ↪ BoundedSolution c.interpolant (c.ambientDim - 1) where
  toFun := c.toBoundedSolution
  inj' p p' h := by
    have h' := congrArg BoundedSolution.polynomial h
    rw [toBoundedSolution_polynomial, toBoundedSolution_polynomial] at h'
    exact Subtype.ext (Subtype.ext h')

/-- The embedding keeps the polynomial. -/
@[simp]
theorem solutionEmbedding_polynomial (c : InterpolationCertificate k A d m domain received)
    (p : agreeingPolynomials domain k A received) :
    (c.solutionEmbedding p).polynomial = (p.1 : R[X]) :=
  c.toBoundedSolution_polynomial p

/-- Every agreeing message polynomial has a bounded-solution representative with the same
polynomial. -/
theorem exists_solution (c : InterpolationCertificate k A d m domain received)
    (p : agreeingPolynomials domain k A received) :
    ∃ solution : BoundedSolution c.interpolant (c.ambientDim - 1),
      solution.polynomial = (p.1 : R[X]) :=
  ⟨c.solutionEmbedding p, c.solutionEmbedding_polynomial p⟩

/-- The agreement list has at most as many elements as the bounded solutions of the interpolant.
Both sides are extended cardinalities, so the statement holds whether or not either side is
finite. -/
theorem encard_agreeingPolynomials_le (c : InterpolationCertificate k A d m domain received) :
    (agreeingPolynomials domain k A received).encard ≤
      ENat.card (BoundedSolution c.interpolant (c.ambientDim - 1)) :=
  ENat.card_le_card_of_injective c.solutionEmbedding.injective

end ReedSolomon.HiddenDerivative.InterpolationCertificate
