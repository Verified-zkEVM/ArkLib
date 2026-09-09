/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ToCompPoly.Univariate.Basic
import CompPoly.Univariate.Deriv
import CompPoly.Univariate.EuclideanAlgorithm
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Perfect

/-!
# Executable squarefree support of a finite-field polynomial

The zero-derivative branch of squarefree support extraction cannot discard the
polynomial: in positive characteristic it can be a nonconstant `p`-th power.
This file first supplies the executable inverse-Frobenius contraction needed by
that branch.  Unlike `PerfectRing.frobeniusEquiv`, the inverse below computes by
finite-field exponentiation.
-/

namespace CompPoly.CPolynomial

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Executable inverse of Frobenius on a finite field. -/
def inverseFrobenius (a : F) : F :=
  a ^ (Fintype.card F / p)

@[simp] theorem inverseFrobenius_pow (a : F) :
    inverseFrobenius p a ^ p = a := by
  have hchar : ringChar F = p :=
    CharP.ringChar_of_prime_eq_zero Fact.out (CharP.cast_eq_zero F p)
  have hdiv : p ∣ Fintype.card F :=
    (prime_dvd_char_iff_dvd_card (R := F) p).mp (hchar ▸ dvd_rfl)
  rw [inverseFrobenius, ← pow_mul, Nat.div_mul_cancel hdiv]
  exact FiniteField.pow_card a

theorem inverseFrobenius_eq_frobeniusEquiv_symm (a : F) :
    inverseFrobenius p a = (frobeniusEquiv F p).symm a := by
  apply (frobeniusEquiv F p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_def, inverseFrobenius_pow]

variable [BEq F] [LawfulBEq F]

/-- Compress exponents by the characteristic and apply inverse Frobenius to
the retained coefficients. This is the computable `p`-th root used when the
formal derivative vanishes. -/
def frobeniusContract (f : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray <| Array.ofFn fun i : Fin (f.natDegree / p + 1) ↦
    inverseFrobenius p (f.coeff (i * p))

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem coeff_frobeniusContract (f : CPolynomial F) (i : ℕ) :
    (frobeniusContract p f).coeff i =
      if i < f.natDegree / p + 1 then
        inverseFrobenius p (f.coeff (i * p))
      else 0 := by
  rw [frobeniusContract, CPolynomial.coeff_ofArray]
  simp only [Array.getD, Array.size_ofFn]
  split <;> simp_all

theorem frobeniusContract_toPoly (f : CPolynomial F) :
    (frobeniusContract p f).toPoly =
      (Polynomial.contract p f.toPoly).map (frobeniusEquiv F p).symm.toRingHom := by
  ext i
  rw [← CPolynomial.coeff_toPoly, coeff_frobeniusContract,
    Polynomial.coeff_map, Polynomial.coeff_contract (Fact.out : Nat.Prime p).ne_zero]
  split_ifs with hi
  · rw [← CPolynomial.coeff_toPoly]
    exact inverseFrobenius_eq_frobeniusEquiv_symm p _
  · have hp : 0 < p := (Fact.out : Nat.Prime p).pos
    have hdegree : f.toPoly.natDegree < i * p := by
      apply (Nat.div_lt_iff_lt_mul hp).mp
      rw [← CPolynomial.natDegree_toPoly]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdegree]
    simp

/-- When the derivative vanishes, executable contraction is an exact `p`-th
root. This is the kernel fact needed by the inseparable recursion branch. -/
theorem frobeniusContract_pow_eq (f : CPolynomial F)
    (hderiv : f.derivative = 0) : frobeniusContract p f ^ p = f := by
  apply toPoly_injective
  rw [toPoly_pow, frobeniusContract_toPoly]
  have hmap :
      ((Polynomial.contract p f.toPoly).map (frobeniusEquiv F p).symm.toRingHom).map
          (frobenius F p) = Polynomial.contract p f.toPoly := by
    rw [Polynomial.map_map]
    ext i
    simp
  rw [← Polynomial.map_frobenius_expand]
  rw [Polynomial.map_expand, hmap]
  apply Polynomial.expand_contract p
  · simpa only [derivative_toPoly, toPoly_zero] using congrArg CPolynomial.toPoly hderiv
  · exact (Fact.out : Nat.Prime p).ne_zero

end CompPoly.CPolynomial
