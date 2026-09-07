/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum

/-!
# Algebraic bounds for LambdaVM AIR residuals

This module records the polynomial algebra used by the LambdaVM AIR and out-of-domain (OOD)
soundness calculation. It deliberately takes the cleared constraint numerator, the trace
zerofier, and the recovered composition parts as arbitrary polynomials with explicit natural
degree hypotheses. Thus the conclusions do not assume the desired residual-degree bound.

If trace coordinates have degree at most `T + u`, a degree-`d` constraint contributes at most
`(d + 1) * T + d * u` after its denominator is cleared. Recombining `c` composition parts as
`sum j, X ^ j * C_j (X ^ c)` and multiplying by the trace zerofier contributes at most
`(c + 1) * T + c - 1`. The cleared residual has degree bounded by the maximum of these terms.

The second part isolates two root-counting contracts used by the soundness argument. A nonzero
constraint residue among coefficients indexed by `Fin (r + 1)` gives a nonzero challenge
polynomial and hence at most `r` cancelling challenges. A nonzero cleared OOD residual has at
most its natural degree many roots. Establishing that a concrete committed tuple supplies the
stated residue is intentionally outside this algebraic module.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], LambdaVM application and Appendix D.
-/

namespace ArkLibExamples.ReedSolomon.LambdaVM

open Polynomial
open scoped BigOperators

noncomputable section

/-! ## Composition recombination and the cleared OOD residual -/

/-- Recombine `c` composition parts by the standard residue-class formula
`sum j, X ^ j * C_j(X ^ c)`. -/
def compositionRecomposition {F : Type*} [Semiring F] {c : ℕ}
    (parts : Fin c → F[X]) : F[X] :=
  ∑ j : Fin c, X ^ (j : ℕ) * (parts j).comp (X ^ c)

/-- If every composition part has degree at most `T`, their `c`-way recombination has degree at
most `c * T + c - 1`. The positivity hypothesis is the actual LambdaVM case and excludes the
empty recombination, for which this subtraction-shaped presentation is unhelpful. -/
theorem compositionRecomposition_natDegree_le {F : Type*} [Semiring F] [Nontrivial F]
    {c T : ℕ} (hc : 0 < c) (parts : Fin c → F[X])
    (hparts : ∀ j, (parts j).natDegree ≤ T) :
    (compositionRecomposition parts).natDegree ≤ c * T + c - 1 := by
  unfold compositionRecomposition
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  calc
    (X ^ (j : ℕ) * (parts j).comp (X ^ c)).natDegree
        ≤ (X ^ (j : ℕ) : F[X]).natDegree + ((parts j).comp (X ^ c)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (j : ℕ) + (parts j).natDegree * (X ^ c : F[X]).natDegree := by
      apply Nat.add_le_add
      · have hpow : (X ^ (j : ℕ) : F[X]).natDegree ≤
            (j : ℕ) * (X : F[X]).natDegree := Polynomial.natDegree_pow_le
        simpa only [Polynomial.natDegree_X, Nat.mul_one] using hpow
      · exact Polynomial.natDegree_comp_le
    _ ≤ (c - 1) + T * c := by
      apply Nat.add_le_add
      · omega
      · calc
          (parts j).natDegree * (X ^ c : F[X]).natDegree
              ≤ (parts j).natDegree * c := by
            exact Nat.mul_le_mul_left _ <| by
              have hpow : (X ^ c : F[X]).natDegree ≤ c * (X : F[X]).natDegree :=
                Polynomial.natDegree_pow_le
              simpa only [Polynomial.natDegree_X, Nat.mul_one] using hpow
          _ ≤ T * c := Nat.mul_le_mul_right c (hparts j)
    _ = c * T + c - 1 := by
      rw [Nat.mul_comm T c]
      omega

/-! ## Constraint polynomials from weighted trace monomials -/

/-- A finite sum of cleared AIR monomials. Each term has a scalar coefficient, a polynomial
clearing weight, and `factorCount term` trace-coordinate factors. This representation is only an
algebraic degree contract; it does not encode a particular CPU instruction or constraint system. -/
def weightedConstraintPolynomial {F : Type*} [CommSemiring F] {m : ℕ}
    (coefficient : Fin m → F) (clearingWeight : Fin m → F[X])
    (factorCount : Fin m → ℕ)
    (coordinate : (term : Fin m) → Fin (factorCount term) → F[X]) : F[X] :=
  ∑ term : Fin m,
    C (coefficient term) * clearingWeight term * ∏ factor, coordinate term factor

/-- A product of at most `d` trace-coordinate polynomials, each of degree at most `T + u`, has
degree at most `d * (T + u)`. The explicit `factorCount` permits monomials of different total
degrees in the same constraint polynomial. -/
theorem traceMonomial_natDegree_le {F : Type*} [CommSemiring F]
    {T d u factorCount : ℕ} (coordinate : Fin factorCount → F[X])
    (hcount : factorCount ≤ d)
    (hcoordinate : ∀ factor, (coordinate factor).natDegree ≤ T + u) :
    (∏ factor, coordinate factor).natDegree ≤ d * (T + u) := by
  calc
    (∏ factor, coordinate factor).natDegree
        ≤ ∑ factor ∈ (Finset.univ : Finset (Fin factorCount)),
            (coordinate factor).natDegree := by
      simpa using Polynomial.natDegree_prod_le
        (Finset.univ : Finset (Fin factorCount)) coordinate
    _ ≤ ∑ _factor : Fin factorCount, (T + u) := by
      apply Finset.sum_le_sum
      intro factor _
      exact hcoordinate factor
    _ = factorCount * (T + u) := by simp
    _ ≤ d * (T + u) := Nat.mul_le_mul_right (T + u) hcount

/-- If clearing weights have degree at most `T`, every monomial uses at most `d` trace
coordinates, and every coordinate has degree at most `T + u`, then the whole cleared constraint
has degree at most `d * (T + u) + T`. Scalar coefficients contribute no degree. -/
theorem weightedConstraintPolynomial_natDegree_le {F : Type*}
    [CommSemiring F] [Nontrivial F] {m T d u : ℕ}
    (coefficient : Fin m → F) (clearingWeight : Fin m → F[X])
    (factorCount : Fin m → ℕ)
    (coordinate : (term : Fin m) → Fin (factorCount term) → F[X])
    (hweight : ∀ term, (clearingWeight term).natDegree ≤ T)
    (hcount : ∀ term, factorCount term ≤ d)
    (hcoordinate : ∀ term factor, (coordinate term factor).natDegree ≤ T + u) :
    (weightedConstraintPolynomial coefficient clearingWeight factorCount coordinate).natDegree ≤
      d * (T + u) + T := by
  unfold weightedConstraintPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro term _
  calc
    (C (coefficient term) * clearingWeight term *
        ∏ factor, coordinate term factor).natDegree
        ≤ (C (coefficient term) * clearingWeight term).natDegree +
            (∏ factor, coordinate term factor).natDegree := Polynomial.natDegree_mul_le
    _ ≤ T + d * (T + u) := Nat.add_le_add
      ((Polynomial.natDegree_C_mul_le _ _).trans (hweight term))
      (traceMonomial_natDegree_le (coordinate term) (hcount term) (hcoordinate term))
    _ = d * (T + u) + T := Nat.add_comm _ _

/-- The cleared OOD residual: a cleared constraint numerator minus the trace zerofier times the
recombined composition polynomial. -/
def clearedOodResidual {F : Type*} [Ring F] {c : ℕ}
    (zerofier clearedConstraint : F[X]) (parts : Fin c → F[X]) : F[X] :=
  clearedConstraint - zerofier * compositionRecomposition parts

/-- Generic LambdaVM residual-degree bound from actual degree hypotheses on all polynomial
inputs. No hypothesis mentions the degree of `clearedOodResidual` itself. -/
theorem clearedOodResidual_natDegree_le {F : Type*} [Ring F] [Nontrivial F]
    {T d c u : ℕ} (hc : 0 < c) (zerofier clearedConstraint : F[X])
    (parts : Fin c → F[X]) (hzerofier : zerofier.natDegree ≤ T)
    (hconstraint : clearedConstraint.natDegree ≤ d * (T + u) + T)
    (hparts : ∀ j, (parts j).natDegree ≤ T) :
    (clearedOodResidual zerofier clearedConstraint parts).natDegree ≤
      max ((d + 1) * T + d * u) ((c + 1) * T + c - 1) := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · calc
      clearedConstraint.natDegree ≤ d * (T + u) + T := hconstraint
      _ = (d + 1) * T + d * u := by ring
      _ ≤ max ((d + 1) * T + d * u) ((c + 1) * T + c - 1) := le_max_left _ _
  · calc
      (zerofier * compositionRecomposition parts).natDegree
          ≤ zerofier.natDegree + (compositionRecomposition parts).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ T + (c * T + c - 1) :=
        Nat.add_le_add hzerofier (compositionRecomposition_natDegree_le hc parts hparts)
      _ = (c + 1) * T + c - 1 := by
        rw [Nat.add_mul, one_mul]
        omega
      _ ≤ max ((d + 1) * T + d * u) ((c + 1) * T + c - 1) :=
        le_max_right _ _

/-- Direct residual bound for a constraint presented as an explicit sum of weighted trace
monomials. This discharges the cleared-constraint degree premise of
`clearedOodResidual_natDegree_le` from coordinate degrees and monomial multiplicities. -/
theorem clearedOodResidual_natDegree_le_of_weightedMonomials {F : Type*}
    [CommRing F] [Nontrivial F] {m T d c u : ℕ} (hc : 0 < c)
    (zerofier : F[X]) (coefficient : Fin m → F) (clearingWeight : Fin m → F[X])
    (factorCount : Fin m → ℕ)
    (coordinate : (term : Fin m) → Fin (factorCount term) → F[X])
    (parts : Fin c → F[X]) (hzerofier : zerofier.natDegree ≤ T)
    (hweight : ∀ term, (clearingWeight term).natDegree ≤ T)
    (hcount : ∀ term, factorCount term ≤ d)
    (hcoordinate : ∀ term factor, (coordinate term factor).natDegree ≤ T + u)
    (hparts : ∀ j, (parts j).natDegree ≤ T) :
    (clearedOodResidual zerofier
      (weightedConstraintPolynomial coefficient clearingWeight factorCount coordinate)
      parts).natDegree ≤
        max ((d + 1) * T + d * u) ((c + 1) * T + c - 1) := by
  apply clearedOodResidual_natDegree_le hc zerofier _ parts hzerofier
  · exact weightedConstraintPolynomial_natDegree_le coefficient clearingWeight factorCount
      coordinate hweight hcount hcoordinate
  · exact hparts

/-- For a degree-three constraint system, two composition parts, and two early points, the
generic residual bound specializes to `4 * T + 6`. This is the CPU profile used in the
LambdaVM calculation. -/
theorem cpu_clearedOodResidual_natDegree_le {F : Type*} [Ring F] [Nontrivial F]
    {T : ℕ} (zerofier clearedConstraint : F[X]) (parts : Fin 2 → F[X])
    (hzerofier : zerofier.natDegree ≤ T)
    (hconstraint : clearedConstraint.natDegree ≤ 3 * (T + 2) + T)
    (hparts : ∀ j, (parts j).natDegree ≤ T) :
    (clearedOodResidual zerofier clearedConstraint parts).natDegree ≤ 4 * T + 6 := by
  have h := clearedOodResidual_natDegree_le (T := T) (d := 3) (c := 2) (u := 2)
    (by norm_num) zerofier clearedConstraint parts hzerofier hconstraint hparts
  omega

/-- CPU residual bound traced directly to coordinate degrees and constraint multiplicity. Each
clearing weight has degree at most `T`, each constraint monomial contains at most three trace
coordinates of degree at most `T + 2`, and the two composition parts have degree at most `T`. -/
theorem cpu_clearedOodResidual_natDegree_le_of_weightedMonomials {F : Type*}
    [CommRing F] [Nontrivial F] {m T : ℕ} (zerofier : F[X])
    (coefficient : Fin m → F) (clearingWeight : Fin m → F[X])
    (factorCount : Fin m → ℕ)
    (coordinate : (term : Fin m) → Fin (factorCount term) → F[X])
    (parts : Fin 2 → F[X]) (hzerofier : zerofier.natDegree ≤ T)
    (hweight : ∀ term, (clearingWeight term).natDegree ≤ T)
    (hcount : ∀ term, factorCount term ≤ 3)
    (hcoordinate : ∀ term factor, (coordinate term factor).natDegree ≤ T + 2)
    (hparts : ∀ j, (parts j).natDegree ≤ T) :
    (clearedOodResidual zerofier
      (weightedConstraintPolynomial coefficient clearingWeight factorCount coordinate)
      parts).natDegree ≤ 4 * T + 6 := by
  have hconstraint := weightedConstraintPolynomial_natDegree_le coefficient clearingWeight
    factorCount coordinate hweight hcount hcoordinate
  exact cpu_clearedOodResidual_natDegree_le zerofier _ parts hzerofier hconstraint hparts

/-- A violated cleared constraint at a root of the trace zerofier makes the OOD residual
nonzero. This is the reusable algebraic endpoint of the pole/noncancellation argument. -/
theorem clearedOodResidual_ne_zero_of_eval {F : Type*} [Field F]
    {c : ℕ} (zerofier clearedConstraint : F[X]) (parts : Fin c → F[X]) (x : F)
    (hzerofier : zerofier.eval x = 0) (hconstraint : clearedConstraint.eval x ≠ 0) :
    clearedOodResidual zerofier clearedConstraint parts ≠ 0 := by
  intro hzero
  have hresidualEval :
      (clearedOodResidual zerofier clearedConstraint parts).eval x =
        clearedConstraint.eval x := by
    simp [clearedOodResidual, hzerofier]
  have hevalZero : (clearedOodResidual zerofier clearedConstraint parts).eval x = 0 := by
    rw [hzero]
    exact Polynomial.eval_zero
  exact hconstraint (hresidualEval.symm.trans hevalZero)

/-! ## Constraint-combination cancellation -/

/-- The challenge polynomial whose coefficients are the constraint residues at one fixed trace
point. Its evaluation at `β` is the powers combination with exponents zero through `r`. -/
def constraintChallengePolynomial {F : Type*} [CommSemiring F] {r : ℕ}
    (residue : Fin (r + 1) → F) : F[X] :=
  ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (residue i)

/-- Evaluation of the constraint challenge polynomial is the intended powers combination. -/
theorem constraintChallengePolynomial_eval {F : Type*} [CommSemiring F] {r : ℕ}
    (residue : Fin (r + 1) → F) (beta : F) :
    (constraintChallengePolynomial residue).eval beta =
      ∑ i : Fin (r + 1), beta ^ (i : ℕ) * residue i := by
  rw [constraintChallengePolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Polynomial.eval_monomial, mul_comm]

/-- The challenge polynomial has natural degree at most the largest exponent `r`. -/
theorem constraintChallengePolynomial_natDegree_le {F : Type*} [CommSemiring F] {r : ℕ}
    (residue : Fin (r + 1) → F) :
    (constraintChallengePolynomial residue).natDegree ≤ r := by
  unfold constraintChallengePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le _).trans (Fin.is_le i)

/-- The coefficient at an allowed challenge exponent is the corresponding constraint residue. -/
@[simp]
theorem constraintChallengePolynomial_coeff {F : Type*} [CommSemiring F] {r : ℕ}
    (residue : Fin (r + 1) → F) (i : Fin (r + 1)) :
    (constraintChallengePolynomial residue).coeff (i : ℕ) = residue i := by
  simp [constraintChallengePolynomial, Polynomial.coeff_monomial, Fin.val_inj]

/-- If at least one constraint has a nonzero residue at the fixed trace point, the challenge
polynomial is nonzero. Thus cancellations can only occur at its roots. -/
theorem constraintChallengePolynomial_ne_zero {F : Type*} [CommSemiring F] {r : ℕ}
    (residue : Fin (r + 1) → F) (hresidue : ∃ i, residue i ≠ 0) :
    constraintChallengePolynomial residue ≠ 0 := by
  obtain ⟨i, hi⟩ := hresidue
  intro hzero
  have hcoeff : residue i = 0 := by
    calc
      residue i = (constraintChallengePolynomial residue).coeff (i : ℕ) :=
        (constraintChallengePolynomial_coeff residue i).symm
      _ = (0 : F[X]).coeff (i : ℕ) := congrArg (fun p : F[X] ↦ p.coeff (i : ℕ)) hzero
      _ = 0 := Polynomial.coeff_zero _
  exact hi hcoeff

/-- Constraint-combination challenges that cancel the residue at a fixed trace point. -/
def badConstraintChallenges {F : Type*} [Field F] [DecidableEq F] {r : ℕ}
    (residue : Fin (r + 1) → F) : Finset F :=
  (constraintChallengePolynomial residue).roots.toFinset

/-- At most `r` challenges cancel a powers combination having at least one nonzero residue. -/
theorem badConstraintChallenges_card_le {F : Type*} [Field F] [DecidableEq F] {r : ℕ}
    (residue : Fin (r + 1) → F) (hresidue : ∃ i, residue i ≠ 0) :
    (badConstraintChallenges residue).card ≤ r := by
  have hnonzero := constraintChallengePolynomial_ne_zero residue hresidue
  by_cases hzero : constraintChallengePolynomial residue = 0
  · exact (hnonzero hzero).elim
  · exact (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' _).trans (constraintChallengePolynomial_natDegree_le residue)

/-- Outside the bad challenge set, the powers combination of the residues is nonzero. -/
theorem constraintCombination_ne_zero_of_not_mem {F : Type*} [Field F] [DecidableEq F]
    {r : ℕ} (residue : Fin (r + 1) → F) (hresidue : ∃ i, residue i ≠ 0)
    (beta : F) (hbeta : beta ∉ badConstraintChallenges residue) :
    ∑ i : Fin (r + 1), beta ^ (i : ℕ) * residue i ≠ 0 := by
  rw [← constraintChallengePolynomial_eval]
  rw [badConstraintChallenges, Multiset.mem_toFinset,
    Polynomial.mem_roots (constraintChallengePolynomial_ne_zero residue hresidue)] at hbeta
  exact hbeta

/-- The CPU combination with exponents zero through `49` has at most `49` cancelling
challenges. The conclusion is conditional only on at least one nonzero constraint residue. -/
theorem cpu_badConstraintChallenges_card_le {F : Type*} [Field F] [DecidableEq F]
    (residue : Fin 50 → F) (hresidue : ∃ i, residue i ≠ 0) :
    (badConstraintChallenges (r := 49) residue).card ≤ 49 := by
  exact badConstraintChallenges_card_le residue hresidue

/-! ## OOD root counting -/

/-- OOD challenges at which a cleared residual vanishes. -/
def badOodChallenges {F : Type*} [Field F] [DecidableEq F] (residual : F[X]) : Finset F :=
  residual.roots.toFinset

/-- A residual of natural degree at most `D` vanishes at at most `D` OOD challenges. -/
theorem badOodChallenges_card_le {F : Type*} [Field F] [DecidableEq F]
    (residual : F[X]) {D : ℕ} (hresidual : residual ≠ 0)
    (hdegree : residual.natDegree ≤ D) :
    (badOodChallenges residual).card ≤ D := by
  by_cases hzero : residual = 0
  · exact (hresidual hzero).elim
  · exact (Multiset.toFinset_card_le _).trans <| (Polynomial.card_roots' _).trans hdegree

/-- Outside its root set, a nonzero cleared residual evaluates nontrivially. -/
theorem eval_ne_zero_of_not_mem_badOodChallenges {F : Type*} [Field F] [DecidableEq F]
    (residual : F[X]) (hresidual : residual ≠ 0) (z : F)
    (hz : z ∉ badOodChallenges residual) : residual.eval z ≠ 0 := by
  rw [badOodChallenges, Multiset.mem_toFinset,
    Polynomial.mem_roots hresidual] at hz
  exact hz

end

end ArkLibExamples.ReedSolomon.LambdaVM
