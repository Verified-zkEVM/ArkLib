/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FrobeniusContraction
import Mathlib.Algebra.Field.ZMod

/-!
# Acceptance tests for the Frobenius contraction

The examples cover:

* the two-level polynomial `X ^ (p ^ 2) + C a * X ^ p`, which contracts once to `X ^ p + C a * X`
  and no further;
* in characteristic zero every contraction witness has `e = 0`;
* positive degree is needed: in characteristic two the constant `1` has no contraction witness;
* the nonmonic linear polynomial `C a * X + 1` over a GCD domain is irreducible and separable over
  the fraction field;
* the primitivity, mapped-derivative and mapped-degree facts for the terminal polynomial, derived
  from `exists_frobeniusContraction_fractionRing` and Mathlib.
-/

open Polynomial

section TwoLevel

variable {R : Type*} [CommRing R] [NoZeroDivisors R] (p : ℕ) [CharP R p] [Fact p.Prime]

/-- `X ^ (p ^ 2) + C a * X ^ p` is the expansion by `p` of `X ^ p + C a * X`. For `a ≠ 0` the
latter has nonzero derivative `C a`, so it is not a further expansion by `p`. -/
example (a : R) (ha : a ≠ 0) :
    let G : R[X] := X ^ p + C a * X
    let P : R[X] := X ^ (p ^ 2) + C a * X ^ p
    derivative G ≠ 0 ∧
      expand R (p ^ 1) G = P ∧
      G.natDegree * p ^ 1 = P.natDegree ∧
      0 < G.natDegree ∧
      ¬∃ H : R[X], expand R p H = G := by
  dsimp only
  have : Nontrivial R := ⟨⟨a, 0, ha⟩⟩
  have hder : derivative (X ^ p + C a * X : R[X]) ≠ 0 := by
    rw [derivative_add, derivative_X_pow, CharP.cast_eq_zero, C_0, zero_mul, zero_add,
      derivative_C_mul_X]
    exact C_ne_zero.mpr ha
  have hexpand : expand R (p ^ 1) (X ^ p + C a * X) = X ^ (p ^ 2) + C a * X ^ p := by
    rw [pow_one, map_add, map_pow, expand_X, map_mul, expand_C, expand_X, ← pow_mul, pow_two]
  have hGdeg : (X ^ p + C a * X : R[X]).natDegree = p := by
    rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow, natDegree_C_mul_X a ha]
    exact (Fact.out : p.Prime).one_lt
  have hPdeg : (X ^ (p ^ 2) + C a * X ^ p : R[X]).natDegree = p ^ 2 := by
    rw [← hexpand, natDegree_expand, hGdeg, pow_one, pow_two]
  refine ⟨hder, hexpand, ?_, ?_, not_exists_expand_of_derivative_ne_zero p hder⟩
  · rw [hGdeg, hPdeg, pow_one, pow_two]
  · rw [hGdeg]
    exact (Fact.out : p.Prime).pos

end TwoLevel

/-- In characteristic zero every witness of `exists_frobeniusContraction` has `e = 0` and
`G = P`. -/
example (P : ℚ[X]) (hP : 0 < P.natDegree) :
    ∃ G : ℚ[X], derivative G ≠ 0 ∧ G = P := by
  obtain ⟨e, G, hGder, hGP, hGdeg, -⟩ := exists_frobeniusContraction 0 P hP
  rcases e with _ | e
  · exact ⟨G, hGder, by simpa using hGP⟩
  · rw [zero_pow (Nat.succ_ne_zero e), mul_zero] at hGdeg
    omega

/-- Positive degree is needed in `exists_frobeniusContraction`: over `ZMod 2` the constant `1`
is not the expansion of any positive-degree polynomial with the degree identity. -/
example :
    ¬∃ e : ℕ, ∃ G : (ZMod 2)[X],
      derivative G ≠ 0 ∧
      expand (ZMod 2) (2 ^ e) G = 1 ∧
      G.natDegree * 2 ^ e = (1 : (ZMod 2)[X]).natDegree ∧
      0 < G.natDegree := by
  rintro ⟨e, G, -, -, hGdeg, hGpos⟩
  rw [natDegree_one] at hGdeg
  have : 0 < G.natDegree * 2 ^ e := Nat.mul_pos hGpos (Nat.two_pow_pos e)
  omega

section FractionRing

variable {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K] (p : ℕ) [CharP R p]

/-- The terminal polynomial of `exists_frobeniusContraction_fractionRing` is primitive, its
mapped derivative is nonzero, and mapping preserves its degree. -/
example {P : R[X]} (hPpos : 0 < P.natDegree) (hP : Irreducible P) :
    ∃ e : ℕ, ∃ G : R[X],
      derivative G ≠ 0 ∧
      expand R (p ^ e) G = P ∧
      G.natDegree * p ^ e = P.natDegree ∧
      0 < G.natDegree ∧
      G.IsPrimitive ∧
      Irreducible (G.map (algebraMap R K)) ∧
      derivative (G.map (algebraMap R K)) ≠ 0 ∧
      (G.map (algebraMap R K)).Separable ∧
      (G.map (algebraMap R K)).natDegree = G.natDegree := by
  obtain ⟨e, G, hGder, hGP, hGdeg, hGpos, hGirr, hmapirr, hmapsep⟩ :=
    exists_frobeniusContraction_fractionRing (K := K) p hPpos hP
  refine ⟨e, G, hGder, hGP, hGdeg, hGpos, hGirr.isPrimitive hGpos.ne', hmapirr, ?_, hmapsep,
    natDegree_map_eq_of_injective (IsFractionRing.injective R K) G⟩
  rw [derivative_map]
  exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hGder

/-- The nonmonic linear polynomial `C a * X + 1` is irreducible over `R`; its terminal
contraction is itself, which is irreducible and separable over the fraction field. -/
example (a : R) (ha : a ≠ 0) :
    ∃ e : ℕ, ∃ G : R[X],
      expand R (p ^ e) G = C a * X + 1 ∧
      Irreducible (G.map (algebraMap R K)) ∧
      (G.map (algebraMap R K)).Separable := by
  have hirr : Irreducible (C a * X + 1 : R[X]) := by
    simpa only [C_1] using irreducible_C_mul_X_add_C ha isRelPrime_one_right
  have hdeg : 0 < (C a * X + 1 : R[X]).natDegree := by
    rw [← C_1, natDegree_linear ha]
    exact Nat.one_pos
  obtain ⟨e, G, -, hGP, -, -, -, hmapirr, hmapsep⟩ :=
    exists_frobeniusContraction_fractionRing (K := K) p hdeg hirr
  exact ⟨e, G, hGP, hmapirr, hmapsep⟩

end FractionRing

/-- Over `ℤ` in characteristic zero, `2 * X + 1` stays irreducible and is separable over `ℚ`. -/
example :
    Irreducible ((C 2 * X + 1 : ℤ[X]).map (algebraMap ℤ ℚ)) ∧
      ((C 2 * X + 1 : ℤ[X]).map (algebraMap ℤ ℚ)).Separable := by
  have hirr : Irreducible (C 2 * X + 1 : ℤ[X]) := by
    simpa only [C_1] using irreducible_C_mul_X_add_C (two_ne_zero : (2 : ℤ) ≠ 0)
      isRelPrime_one_right
  have hdeg : 0 < (C 2 * X + 1 : ℤ[X]).natDegree := by
    rw [← C_1, natDegree_linear two_ne_zero]
    exact Nat.one_pos
  obtain ⟨e, G, -, hGP, hGdeg, -, -, hmapirr, hmapsep⟩ :=
    exists_frobeniusContraction_fractionRing (K := ℚ) 0 hdeg hirr
  rcases e with _ | e
  · rw [pow_zero, expand_one] at hGP
    rw [← hGP]
    exact ⟨hmapirr, hmapsep⟩
  · rw [zero_pow (Nat.succ_ne_zero e), mul_zero] at hGdeg
    omega
