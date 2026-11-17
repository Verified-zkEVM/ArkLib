/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger, Alexander Hicks
-/
module

public import ArkLib.Data.Probability.FiniteError
public import ArkLib.ToCompPoly.Univariate.Finite
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Basic

/-!
# Computable affine-combiner errors

Finite coefficient vectors enumerate all candidates and witnesses within their degree bounds.
CompPoly supplies executable polynomial arithmetic and evaluation for this search.
The maximum exceptional-challenge count over received word pairs gives an exact rational error.
The equality theorems identify these values with the semantic `ENNReal` errors.
The computations require executable field operations, equality decisions, and finite enumerations.
They use no sampler.
The search is exhaustive and can be expensive for large fields or degree bounds.

## Main definitions

* `ReedSolomon.Computable.IsAffineExceptional` and
  `ReedSolomon.Computable.IsScalarExceptional`: predicates with finite witness searches.
* `ReedSolomon.affineMcaErrorRat`: exact affine-combiner error in `ℚ≥0`.
* `ReedSolomon.scalarMcaErrorRat`: exact scalar-combiner error in `ℚ≥0`.

## Main statements

* `ReedSolomon.Computable.exists_isAffineExceptional_iff` and
  `ReedSolomon.Computable.exists_isScalarExceptional_iff`: agreement of the exceptional events.
* `ReedSolomon.ofReal_affineMcaErrorRat`: the affine rational value equals the semantic error.
* `ReedSolomon.ofReal_scalarMcaErrorRat`: the scalar rational value equals the semantic error.

The semantic affine and scalar errors follow Section 1.1 and Section 6 of [CWYZ26].

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon.Computable

open CompPoly Finset

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype ι]

/-- The multiplier `α + βX` represented by a computable polynomial. -/
def affineMultiplier (α β : F) : CPolynomial F :=
  CPolynomial.C α + CPolynomial.C β * CPolynomial.X

/-- The word `i ↦ f i + L.eval (domain i) * g i` using computable polynomials. -/
def combinedWord (domain : ι ↪ F) (f g : ι → F) (L : CPolynomial F) : ι → F :=
  fun i ↦ f i + L.eval (domain i) * g i

/-- Candidate agreements on which one of the two witnesses disagrees with its received word. -/
def lostPositions (domain : ι ↪ F) (f g word : ι → F) (P F₀ G₀ : CPolynomial F) : Finset ι :=
  {i : ι | P.eval (domain i) = word i ∧
    (F₀.eval (domain i) ≠ f i ∨ G₀.eval (domain i) ≠ g i)}

/-- A computable polynomial decomposition with at most `s` lost agreements. -/
def IsLossWitness (domain : ι ↪ F) (f g : ι → F) (s : ℕ) (L P F₀ G₀ : CPolynomial F) : Prop :=
  P = F₀ + L * G₀ ∧
    (lostPositions domain f g (combinedWord domain f g L) P F₀ G₀).card ≤ s

instance (domain : ι ↪ F) (f g : ι → F) (s : ℕ) (L P F₀ G₀ : CPolynomial F) :
    Decidable (IsLossWitness domain f g s L P F₀ G₀) := by
  unfold IsLossWitness
  infer_instance

@[simp]
theorem toPoly_affineMultiplier (α β : F) :
    (affineMultiplier α β).toPoly = ReedSolomon.affineMultiplier α β := by
  simp [affineMultiplier, ReedSolomon.affineMultiplier]

omit [DecidableEq F] [Fintype ι] in
@[simp]
theorem combinedWord_toPoly (domain : ι ↪ F) (f g : ι → F) (L : CPolynomial F) :
    combinedWord domain f g L = ReedSolomon.combinedWord domain f g L.toPoly := by
  classical
  funext i
  simp [combinedWord, ReedSolomon.combinedWord, CPolynomial.eval_toPoly]

/-- The executable loss set equals the filtered mathematical agreement set. -/
theorem lostPositions_eq_filter (domain : ι ↪ F) (f g word : ι → F)
    (P F₀ G₀ : CPolynomial F) :
    lostPositions domain f g word P F₀ G₀ =
      {i ∈ polynomialAgreementSet domain word P.toPoly |
        F₀.toPoly.eval (domain i) ≠ f i ∨ G₀.toPoly.eval (domain i) ≠ g i} := by
  ext i
  simp [lostPositions, polynomialAgreementSet, CPolynomial.eval_toPoly]

@[simp]
theorem lostPositions_toPoly (domain : ι ↪ F) (f g : ι → F) (L P F₀ G₀ : CPolynomial F) :
    lostPositions domain f g (combinedWord domain f g L) P F₀ G₀ =
      agreementLoss domain f g L.toPoly P.toPoly F₀.toPoly G₀.toPoly := by
  simp only [lostPositions_eq_filter, agreementLoss, combinedWord_toPoly]

@[simp]
theorem isLossWitness_iff (domain : ι ↪ F) (f g : ι → F) (s : ℕ)
    (L P F₀ G₀ : CPolynomial F) :
    IsLossWitness domain f g s L P F₀ G₀ ↔
      ReedSolomon.IsLossWitness domain f g s L.toPoly P.toPoly F₀.toPoly G₀.toPoly := by
  have heq : (P = F₀ + L * G₀) ↔ P.toPoly = F₀.toPoly + L.toPoly * G₀.toPoly := by
    rw [← CPolynomial.toPoly_mul, ← CPolynomial.toPoly_add]
    exact CPolynomial.toPoly_inj.symm
  simp only [IsLossWitness, ReedSolomon.IsLossWitness, heq, lostPositions_toPoly]

/-- A candidate has degree at most `d`.
It agrees with `f + (α + βX)g` on at least `A` domain points.
Every decomposition `P = F₀ + (α + βX) G₀` with `deg F₀ ≤ d` and `deg G₀ < d`
loses more than `s` agreements. -/
def IsAffineExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) : Prop :=
  A ≤ #{i : ι | P.val.eval (domain i) = combinedWord domain f g (affineMultiplier α β) i} ∧
    ∀ F₀ : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      ∀ G₀ : ↥(CPolynomial.degreeLT (R := F) d),
        ¬ IsLossWitness domain f g s (affineMultiplier α β) P.val F₀.val G₀.val

instance [Fintype F] (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    Decidable (IsAffineExceptional domain f g d A s α β P) := by
  unfold IsAffineExceptional
  infer_instance

/-- Bounded affine exceptionality is equivalent to the mathematical predicate. -/
theorem isAffineExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    IsAffineExceptional domain f g d A s α β P ↔
      ReedSolomon.IsAffineExceptional domain f g d A s α β P.val.toPoly := by
  have hdeg := CPolynomial.degreeLT_toPoly.mp P.property
  rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE] at hdeg
  unfold IsAffineExceptional ReedSolomon.IsAffineExceptional
  simp only [hdeg, true_and]
  have hcard : #{i : ι | P.val.eval (domain i) =
      combinedWord domain f g (affineMultiplier α β) i} =
      (polynomialAgreementSet domain
        (ReedSolomon.combinedWord domain f g (ReedSolomon.affineMultiplier α β))
        P.val.toPoly).card := by
    congr 1
    ext i
    simp [polynomialAgreementSet, CPolynomial.eval_toPoly]
  rw [hcard]
  simp_rw [isLossWitness_iff, toPoly_affineMultiplier]
  refine and_congr_right fun _ ↦ ?_
  simpa only [← Polynomial.mem_degreeLT, Polynomial.degreeLT_succ_eq_degreeLE,
    Polynomial.mem_degreeLE] using CPolynomial.forall_pair_degreeLT_toPoly_iff (d + 1) d
      (fun F₀ G₀ ↦ ¬ ReedSolomon.IsLossWitness domain f g s
        (ReedSolomon.affineMultiplier α β) P.val.toPoly F₀ G₀)

/-- A candidate has degree at most `d`.
It agrees with `f + αg` on at least `A` domain points.
Every decomposition `P = F₀ + α G₀` with both witness degrees at most `d`
loses more than `s` agreements. -/
def IsScalarExceptional (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) : Prop :=
  A ≤ #{i : ι | P.val.eval (domain i) = combinedWord domain f g (CPolynomial.C α) i} ∧
    ∀ F₀ G₀ : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      ¬ IsLossWitness domain f g s (CPolynomial.C α) P.val F₀.val G₀.val

instance [Fintype F] (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    Decidable (IsScalarExceptional domain f g d A s α P) := by
  unfold IsScalarExceptional
  infer_instance

/-- Bounded scalar exceptionality is equivalent to the mathematical predicate. -/
theorem isScalarExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F)
    (P : ↥(CPolynomial.degreeLT (R := F) (d + 1))) :
    IsScalarExceptional domain f g d A s α P ↔
      ReedSolomon.IsScalarExceptional domain f g d A s α P.val.toPoly := by
  have hdeg := CPolynomial.degreeLT_toPoly.mp P.property
  rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE] at hdeg
  unfold IsScalarExceptional ReedSolomon.IsScalarExceptional
  simp only [hdeg, true_and]
  have hcard : #{i : ι | P.val.eval (domain i) =
      combinedWord domain f g (CPolynomial.C α) i} =
      (polynomialAgreementSet domain
        (ReedSolomon.combinedWord domain f g (Polynomial.C α)) P.val.toPoly).card := by
    congr 1
    ext i
    simp [polynomialAgreementSet, CPolynomial.eval_toPoly]
  rw [hcard]
  simp_rw [isLossWitness_iff, CPolynomial.C_toPoly]
  refine and_congr_right fun _ ↦ ?_
  simpa only [← Polynomial.mem_degreeLT, Polynomial.degreeLT_succ_eq_degreeLE,
    Polynomial.mem_degreeLE] using CPolynomial.forall_pair_degreeLT_toPoly_iff (d + 1) (d + 1)
      (fun F₀ G₀ ↦ ¬ ReedSolomon.IsLossWitness domain f g s
        (Polynomial.C α) P.val.toPoly F₀ G₀)

/-- The bounded candidate search detects every affine exceptional challenge. -/
theorem exists_isAffineExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α β : F) :
    (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      IsAffineExceptional domain f g d A s α β P) ↔
      ∃ P, ReedSolomon.IsAffineExceptional domain f g d A s α β P := by
  simp_rw [isAffineExceptional_iff]
  apply CPolynomial.exists_degreeLT_toPoly_iff_of_degree_lt (d + 1) _
  intro P hP
  rw [← Polynomial.mem_degreeLT, Polynomial.degreeLT_succ_eq_degreeLE,
    Polynomial.mem_degreeLE]
  exact hP.1

/-- The bounded candidate search detects every scalar exceptional challenge. -/
theorem exists_isScalarExceptional_iff (domain : ι ↪ F) (f g : ι → F) (d A s : ℕ) (α : F) :
    (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      IsScalarExceptional domain f g d A s α P) ↔
      ∃ P, ReedSolomon.IsScalarExceptional domain f g d A s α P := by
  simp_rw [isScalarExceptional_iff]
  apply CPolynomial.exists_degreeLT_toPoly_iff_of_degree_lt (d + 1) _
  intro P hP
  rw [← Polynomial.mem_degreeLT, Polynomial.degreeLT_succ_eq_degreeLE,
    Polynomial.mem_degreeLE]
  exact hP.1

end ReedSolomon.Computable

namespace ReedSolomon

open CompPoly Finset

variable {F ι : Type} [Field F] [DecidableEq F] [Fintype F] [Fintype ι]

/-- The exact worst-case affine-combiner error, computed as a nonnegative rational.

The output degree bound is `d`, the agreement threshold is `A`, and the allowed loss is `s`.
Witness degrees are at most `d` and below `d`.
The computation exhausts received word pairs, challenges, candidates, and witnesses. -/
def affineMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) : ℚ≥0 :=
  letI : DecidableEq ι := domain.injective.decidableEq
  Probability.maxEventProbability fun (w : (ι → F) × (ι → F)) (c : F × F) ↦
    decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      Computable.IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P)

/-- The exact worst-case scalar-combiner error, computed as a nonnegative rational.

The output and witness degree bound is `d`, the agreement threshold is `A`, and the allowed loss
is `s`. The computation exhausts received word pairs, challenges, candidates, and witnesses. -/
def scalarMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) : ℚ≥0 :=
  letI : DecidableEq ι := domain.injective.decidableEq
  Probability.maxEventProbability fun (w : (ι → F) × (ι → F)) (α : F) ↦
    decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
      Computable.IsScalarExceptional domain w.1 w.2 d A s α P)

/-- The computed rational affine error equals the semantic error after real embedding. -/
theorem ofReal_affineMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) :
    ENNReal.ofReal (affineMcaErrorRat domain d A s : ℝ) = affineMcaError domain d A s := by
  classical
  let : DecidableEq ι := domain.injective.decidableEq
  unfold affineMcaErrorRat
  rw [Probability.ofReal_maxEventProbability_eq_iSup]
  have hcount (w : (ι → F) × (ι → F)) :
      #{c : F × F | decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
        Computable.IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P) = true} =
      #{c : F × F | ∃ P, IsAffineExceptional domain w.1 w.2 d A s c.1 c.2 P} := by
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact Computable.exists_isAffineExceptional_iff domain w.1 w.2 d A s c.1 c.2
  simp_rw [hcount]
  simp only [affineMcaError, Fintype.card_prod, Nat.cast_mul, pow_two]

/-- The computed rational scalar error equals the semantic error after real embedding. -/
theorem ofReal_scalarMcaErrorRat (domain : ι ↪ F) (d A s : ℕ) :
    ENNReal.ofReal (scalarMcaErrorRat domain d A s : ℝ) = scalarMcaError domain d A s := by
  classical
  let : DecidableEq ι := domain.injective.decidableEq
  unfold scalarMcaErrorRat
  rw [Probability.ofReal_maxEventProbability_eq_iSup]
  have hcount (w : (ι → F) × (ι → F)) :
      #{α : F | decide (∃ P : ↥(CPolynomial.degreeLT (R := F) (d + 1)),
        Computable.IsScalarExceptional domain w.1 w.2 d A s α P) = true} =
      #{α : F | ∃ P, IsScalarExceptional domain w.1 w.2 d A s α P} := by
    congr 1
    ext α
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact Computable.exists_isScalarExceptional_iff domain w.1 w.2 d A s α
  simp_rw [hcount]
  rfl

end ReedSolomon
