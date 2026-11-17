/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger, Alexander Hicks
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Computable
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.EqualDegree

/-!
# Exact computable errors for equal-degree combiners

Finite coefficient vectors enumerate the candidate and both witnesses.
The exhaustive challenge count computes the error as a nonnegative rational.
The equality theorem identifies that value with the semantic equal-degree error.
The output has degree at most `d`, and both witnesses have degree below `d`.
The computation requires executable field operations, equality decisions, and finite enumerations.
It uses no sampler.
Its exhaustive search can be expensive for large fields or degree bounds.

## Main definitions

* `ReedSolomon.Computable.IsEqualDegreeExceptional`: a predicate with finite witness searches.
* `ReedSolomon.equalDegreeMcaErrorRat`: the exact rational equal-degree error.

## Main statements

* `ReedSolomon.Computable.exists_isEqualDegreeExceptional_iff`: agreement of the exceptional events.
* `ReedSolomon.ofReal_equalDegreeMcaErrorRat`: equality with the semantic `ENNReal` error.

The semantic equal-degree error is defined in Section 5 of [CWYZ26].

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon.Computable

open CompPoly Finset

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

/-- A candidate has degree at most `d`.
It agrees with `g + (α + βX)(f + θg)` on at least `A` domain points.
Every decomposition `P = G₀ + (α + βX) (F₀ + θ G₀)` with both witness degrees below `d`
loses more than `s` agreements. -/
def IsEqualDegreeExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) : Prop :=
  A ≤ #{i : ι | P.val.eval (domain i) = equalDegreeWord domain f g θ α β i} ∧
    ∀ F₀ G₀ : ↥(CPolynomial.degreeLT (R := F) d),
      P.val = G₀.val + affineMultiplier α β * (F₀.val + CPolynomial.C θ * G₀.val) →
        s < (lostPositions domain f g (equalDegreeWord domain f g θ α β)
          P.val F₀.val G₀.val).card

instance [Fintype F] (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    Decidable (IsEqualDegreeExceptional domain f g d A s θ α β P) := by
  unfold IsEqualDegreeExceptional
  infer_instance

/-- Bounded equal-degree exceptionality is equivalent to the mathematical predicate. -/
theorem isEqualDegreeExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (θ α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    IsEqualDegreeExceptional domain f g d A s θ α β P ↔
      ReedSolomon.IsEqualDegreeExceptional domain f g d A s θ α β P.val.toPoly := by
  have hdeg := CPolynomial.degreeLT_toPoly.mp P.property
  rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE] at hdeg
  unfold IsEqualDegreeExceptional ReedSolomon.IsEqualDegreeExceptional
  simp only [hdeg, true_and]
  have hcard : #{i : ι | P.val.eval (domain i) = equalDegreeWord domain f g θ α β i} =
      (polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P.val.toPoly).card := by
    congr 1
    ext i
    simp [polynomialAgreementSet, CPolynomial.eval_toPoly]
  rw [hcard]
  have heq (F₀ G₀ : CPolynomial F) :
      (P.val = G₀ + affineMultiplier α β * (F₀ + CPolynomial.C θ * G₀)) ↔
      P.val.toPoly = G₀.toPoly + ReedSolomon.affineMultiplier α β *
        (F₀.toPoly + Polynomial.C θ * G₀.toPoly) := by
    simpa only [CPolynomial.toPoly_add, CPolynomial.toPoly_mul, toPoly_affineMultiplier,
      CPolynomial.C_toPoly] using
        (CPolynomial.toPoly_inj (p := P.val)
          (q := G₀ + affineMultiplier α β * (F₀ + CPolynomial.C θ * G₀))).symm
  simp_rw [heq, lostPositions_eq_filter]
  refine and_congr_right fun _ ↦ ?_
  exact CPolynomial.forall_pair_degreeLT_toPoly_iff d d
    (fun F₀ G₀ ↦ P.val.toPoly = G₀ + ReedSolomon.affineMultiplier α β *
      (F₀ + Polynomial.C θ * G₀) →
        s < #{i ∈ polynomialAgreementSet domain (equalDegreeWord domain f g θ α β) P.val.toPoly |
          F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i})

/-- The bounded candidate search detects every equal-degree exceptional challenge. -/
theorem exists_isEqualDegreeExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ)
    (θ α β : F) :
    (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      IsEqualDegreeExceptional domain f g d A s θ α β P) ↔
      ∃ P, ReedSolomon.IsEqualDegreeExceptional domain f g d A s θ α β P := by
  simp_rw [isEqualDegreeExceptional_iff]
  apply CPolynomial.exists_degreeLT_toPoly_iff_of_degree_lt (d + 1) _
  intro P hP
  rw [← Polynomial.mem_degreeLT, Polynomial.degreeLT_succ_eq_degreeLE,
    Polynomial.mem_degreeLE]
  exact hP.1

end ReedSolomon.Computable

namespace ReedSolomon

open CompPoly Finset

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype ι]

/-- The exact worst-case equal-degree combiner error, computed as a nonnegative rational.

The output degree bound is `d`, both witness degrees are below `d`, the agreement threshold
is `A`, and the allowed loss is `s`.
The computation exhausts received word pairs, challenge triples, candidates, and witnesses. -/
def equalDegreeMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) : ℚ≥0 :=
  letI : DecidableEq ι := domain.injective.decidableEq
  Probability.maxEventProbability fun (w : (ι → F) × (ι → F)) (c : F × F × F) ↦
    decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      Computable.IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P)

/-- The computed rational equal-degree error equals the semantic error after real embedding. -/
theorem ofReal_equalDegreeMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) :
    ENNReal.ofReal (equalDegreeMcaErrorRat domain d A s : ℝ) =
      equalDegreeMcaError domain d A s := by
  classical
  let : DecidableEq ι := domain.injective.decidableEq
  unfold equalDegreeMcaErrorRat
  rw [Probability.ofReal_maxEventProbability_eq_iSup]
  have hcount (w : (ι → F) × (ι → F)) :
      #{c : F × F × F | decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
        Computable.IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P) = true} =
      #{c : F × F × F | ∃ P, IsEqualDegreeExceptional domain w.1 w.2 d A s c.1 c.2.1 c.2.2 P} := by
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact Computable.exists_isEqualDegreeExceptional_iff domain w.1 w.2 d A s c.1 c.2.1 c.2.2
  simp_rw [hcount]
  simp only [equalDegreeMcaError, Fintype.card_prod, Nat.cast_mul, pow_succ, pow_zero,
    one_mul, mul_assoc]

end ReedSolomon
