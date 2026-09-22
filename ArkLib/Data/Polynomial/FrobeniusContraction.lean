/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FractionFieldResultant
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Frobenius contraction over a coefficient ring without zero divisors

Let `R` be a commutative ring without zero divisors of characteristic `p`. A polynomial
`P : R[X]` of positive degree whose derivative vanishes has `p ≠ 0`, is `expand R p Q` for
`Q = contract p P`, and `Q` has smaller positive degree. Iterating, `P = expand R (p ^ e) G` for a
polynomial `G` over `R` with nonzero derivative, and `G.natDegree * p ^ e = P.natDegree`. The
coefficients of `G` are coefficients of `P`: no fraction field is introduced. Irreducibility of
`P` descends to `G`. A polynomial with nonzero derivative is not the expansion of any polynomial
by `p`, so the exponent `e` is maximal. In characteristic zero the derivative of a
positive-degree polynomial is nonzero, and `e = 0`.

Over a GCD domain, an irreducible `G` with nonzero derivative stays irreducible over the
fraction field by Gauss's lemma, and is separable there.

## Main statements

* `Polynomial.exists_frobeniusContraction`: the terminal contraction and its degree identity.
* `Polynomial.exists_irreducible_frobeniusContraction`: the same for an irreducible polynomial,
  with an irreducible terminal polynomial.
* `Polynomial.exists_frobeniusContraction_fractionRing`: over a GCD domain, the terminal
  polynomial is irreducible and separable over the fraction field.
* `Polynomial.not_exists_expand_of_derivative_ne_zero`: maximality of the contraction.
-/

@[expose] public section

namespace Polynomial

section NoZeroDivisors

variable {R : Type*} [CommRing R] [NoZeroDivisors R] (p : ℕ) [CharP R p]

/-- In characteristic `p` without zero divisors, a positive-degree polynomial `P` is the
expansion `expand R (p ^ e) G` of a polynomial `G` over the same ring with nonzero derivative and
positive degree, and `G.natDegree * p ^ e = P.natDegree`. -/
theorem exists_frobeniusContraction (P : R[X]) (hP : 0 < P.natDegree) :
    ∃ e : ℕ, ∃ G : R[X],
      derivative G ≠ 0 ∧
      expand R (p ^ e) G = P ∧
      G.natDegree * p ^ e = P.natDegree ∧
      0 < G.natDegree := by
  induction hN : P.natDegree using Nat.strong_induction_on generalizing P with
  | h N ih =>
      by_cases hder : derivative P = 0
      · have : Nontrivial R := ⟨⟨P.leadingCoeff, 0, leadingCoeff_ne_zero.mpr
          (ne_zero_of_natDegree_gt hP)⟩⟩
        rcases eq_or_ne p 0 with rfl | hp
        · have : CharZero R := CharP.charP_to_charZero R
          exact absurd (derivative_eq_zero.mp hder) hP.ne'
        have hp1 : 1 < p := by
          have := CharP.char_ne_one R p
          omega
        let Q := contract p P
        have hQP : expand R p Q = P := expand_contract p hder hp
        have hdeg : Q.natDegree * p = P.natDegree := by
          rw [← natDegree_expand p Q, hQP]
        have hQpos : 0 < Q.natDegree := by
          by_contra hQ
          rw [Nat.eq_zero_of_not_pos hQ, zero_mul] at hdeg
          omega
        have hQlt : Q.natDegree < P.natDegree := by
          rw [← hdeg]
          exact lt_mul_of_one_lt_right hQpos hp1
        obtain ⟨e, G, hGder, hGQ, hGdeg, hGpos⟩ :=
          ih Q.natDegree (by omega) Q hQpos rfl
        refine ⟨e + 1, G, hGder, ?_, ?_, hGpos⟩
        · rw [pow_succ', ← expand_expand, hGQ, hQP]
        · rw [pow_succ, ← mul_assoc, hGdeg, hdeg, hN]
      · exact ⟨0, P, hder, by simp, by simpa using hN, hP⟩

/-- If `P` is irreducible of positive degree, the terminal polynomial `G` of
`exists_frobeniusContraction` is irreducible as well. -/
theorem exists_irreducible_frobeniusContraction {P : R[X]}
    (hPpos : 0 < P.natDegree) (hP : Irreducible P) :
    ∃ e : ℕ, ∃ G : R[X],
      derivative G ≠ 0 ∧
      expand R (p ^ e) G = P ∧
      G.natDegree * p ^ e = P.natDegree ∧
      0 < G.natDegree ∧
      Irreducible G := by
  obtain ⟨e, G, hGder, hGP, hGdeg, hGpos⟩ := exists_frobeniusContraction p P hPpos
  refine ⟨e, G, hGder, hGP, hGdeg, hGpos, ?_⟩
  have : Nontrivial R := ⟨⟨P.leadingCoeff, 0, leadingCoeff_ne_zero.mpr hP.ne_zero⟩⟩
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have hpe : p ^ e ≠ 0 := by
    intro h
    rw [h, mul_zero] at hGdeg
    omega
  apply of_irreducible_expand hpe
  rwa [hGP]

omit [NoZeroDivisors R] in
/-- In characteristic `p`, a polynomial with nonzero derivative is not the expansion of any
polynomial by `p`. -/
theorem not_exists_expand_of_derivative_ne_zero {G : R[X]} (hG : derivative G ≠ 0) :
    ¬∃ H : R[X], expand R p H = G := by
  rintro ⟨H, rfl⟩
  apply hG
  rw [derivative_expand, CharP.cast_eq_zero, zero_mul, mul_zero]

end NoZeroDivisors

section FractionRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K] (p : ℕ) [CharP R p]

/-- Over a GCD domain of characteristic `p`, the terminal polynomial `G` of the Frobenius
contraction of an irreducible positive-degree polynomial is irreducible over `R`, and its image
over the fraction field `K` is irreducible and separable. -/
theorem exists_frobeniusContraction_fractionRing {P : R[X]}
    (hPpos : 0 < P.natDegree) (hP : Irreducible P) :
    ∃ e : ℕ, ∃ G : R[X],
      derivative G ≠ 0 ∧
      expand R (p ^ e) G = P ∧
      G.natDegree * p ^ e = P.natDegree ∧
      0 < G.natDegree ∧
      Irreducible G ∧
      Irreducible (G.map (algebraMap R K)) ∧
      (G.map (algebraMap R K)).Separable := by
  obtain ⟨e, G, hGder, hGP, hGdeg, hGpos, hGirr⟩ :=
    exists_irreducible_frobeniusContraction p hPpos hP
  refine ⟨e, G, hGder, hGP, hGdeg, hGpos, hGirr, ?_,
    separable_map_of_irreducible_of_derivative_ne_zero G hGirr hGder⟩
  exact ((hGirr.isPrimitive hGpos.ne').irreducible_iff_irreducible_map_fraction_map).mp hGirr

end FractionRing

end Polynomial
