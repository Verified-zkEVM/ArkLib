/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Polynomial.Expand

/-!
# Frobenius contraction over an integral coefficient ring

In positive characteristic, repeatedly contracting a positive-degree polynomial whose derivative
vanishes eventually produces a polynomial with nonzero derivative.  All contractions stay over
the original coefficient ring: no fraction field or algebraic closure is introduced here.

This file proves only coefficient-preserving contraction, its exact degree identity, and the
resulting irreducibility and maximality facts.  It does not assert separability over an arbitrary
coefficient ring, or any geometric or agreement bound.
-/

@[expose] public section

namespace Polynomial

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] (p : ℕ) [CharP R p] [Fact p.Prime]

/-- A positive-degree polynomial in prime characteristic is an iterated Frobenius expansion of a
positive-degree polynomial with nonzero derivative.  The contracted polynomial remains over the
original coefficient ring, and its degree accounts exactly for the extracted prime power. -/
theorem exists_frobeniusContraction (P : R[X]) (hP : 0 < P.natDegree) :
    ∃ e : ℕ, ∃ G : R[X],
      derivative G ≠ 0 ∧
      expand R (p ^ e) G = P ∧
      G.natDegree * (p ^ e) = P.natDegree ∧
      0 < G.natDegree := by
  induction hN : P.natDegree using Nat.strong_induction_on generalizing P with
  | h N ih =>
      by_cases hder : derivative P = 0
      · let Q := contract p P
        have hQP : expand R p Q = P := expand_contract p hder (Fact.out : p.Prime).ne_zero
        have hdeg : Q.natDegree * p = P.natDegree := by
          rw [← natDegree_expand p Q, hQP]
        have hQpos : 0 < Q.natDegree := by
          by_contra hQ
          have hQzero : Q.natDegree = 0 := Nat.eq_zero_of_not_pos hQ
          rw [hQzero, zero_mul] at hdeg
          exact (Nat.ne_of_gt hP) hdeg.symm
        have hQlt : Q.natDegree < P.natDegree := by
          calc
            Q.natDegree = Q.natDegree * 1 := by rw [mul_one]
            _ < Q.natDegree * p :=
              Nat.mul_lt_mul_of_pos_left (Fact.out : p.Prime).one_lt hQpos
            _ = P.natDegree := hdeg
        obtain ⟨e, G, hGder, hGQ, hGdeg, hGpos⟩ :=
          ih Q.natDegree (by simpa only [hN] using hQlt) Q hQpos rfl
        refine ⟨e + 1, G, hGder, ?_, ?_, hGpos⟩
        · rw [pow_succ', ← expand_expand, hGQ, hQP]
        · rw [pow_succ, ← mul_assoc, hGdeg, hdeg, hN]
      · exact ⟨0, P, hder, by simp, by simpa using hN, hP⟩

/-- Irreducibility descends through the prime-power expansion returned by
`exists_frobeniusContraction`. -/
theorem exists_irreducible_frobeniusContraction {P : R[X]} (hPpos : 0 < P.natDegree)
    (hP : Irreducible P) :
    ∃ e : ℕ, ∃ G : R[X],
      derivative G ≠ 0 ∧
      expand R (p ^ e) G = P ∧
      G.natDegree * (p ^ e) = P.natDegree ∧
      0 < G.natDegree ∧
      Irreducible G := by
  obtain ⟨e, G, hGder, hGP, hGdeg, hGpos⟩ := exists_frobeniusContraction p P hPpos
  refine ⟨e, G, hGder, hGP, hGdeg, hGpos, ?_⟩
  apply of_irreducible_expand_pow (Fact.out : p.Prime).ne_zero
  rwa [hGP]

omit [IsDomain R] [Fact p.Prime] in
/-- A polynomial with nonzero derivative is not itself a nontrivial Frobenius expansion. -/
theorem not_exists_expand_of_derivative_ne_zero {G : R[X]} (hG : derivative G ≠ 0) :
    ¬∃ H : R[X], expand R p H = G := by
  rintro ⟨H, rfl⟩
  apply hG
  rw [derivative_expand, CharP.cast_eq_zero, zero_mul, mul_zero]

omit [IsDomain R] [Fact p.Prime] in
/-- Maximality of a contracted equation: no positive further prime-power expansion remains once
its derivative is nonzero. -/
theorem not_exists_expand_primePow_succ_of_derivative_ne_zero {G : R[X]}
    (hG : derivative G ≠ 0) (k : ℕ) :
    ¬∃ H : R[X], expand R (p ^ (k + 1)) H = G := by
  rintro ⟨H, hH⟩
  apply not_exists_expand_of_derivative_ne_zero p hG
  refine ⟨expand R (p ^ k) H, ?_⟩
  rw [expand_expand, ← pow_succ']
  exact hH

/-- A two-level canary for contraction over the original coefficient ring.  The polynomial
`X ^ (p ^ 2) + a * X ^ p` contracts once to `X ^ p + a * X`; a nonzero `a` makes the terminal
derivative nonzero and prevents a further Frobenius contraction. -/
theorem frobeniusContraction_twoLevel_canary (a : R) (ha : a ≠ 0) :
    let G : R[X] := X ^ p + C a * X
    let P : R[X] := X ^ (p ^ 2) + C a * X ^ p
    derivative G ≠ 0 ∧
      expand R (p ^ 1) G = P ∧
      G.natDegree * (p ^ 1) = P.natDegree ∧
      0 < G.natDegree ∧
      ¬∃ H : R[X], expand R p H = G := by
  dsimp only
  have hder : derivative (X ^ p + C a * X : R[X]) ≠ 0 := by
    rw [derivative_add, derivative_X_pow, CharP.cast_eq_zero, C_0, zero_mul, zero_add,
      derivative_C_mul_X]
    exact C_ne_zero.mpr ha
  have hexpand :
      expand R (p ^ 1) (X ^ p + C a * X) = X ^ (p ^ 2) + C a * X ^ p := by
    rw [pow_one, map_add, map_pow, expand_X, map_mul, expand_C, expand_X, ← pow_mul,
      pow_two]
  have hGdeg : (X ^ p + C a * X : R[X]).natDegree = p := by
    calc
      (X ^ p + C a * X : R[X]).natDegree = (X ^ p : R[X]).natDegree := by
        apply natDegree_add_eq_left_of_natDegree_lt
        rw [natDegree_X_pow, natDegree_C_mul_X a ha]
        exact (Fact.out : p.Prime).one_lt
      _ = p := natDegree_X_pow p
  have hPdeg : (X ^ (p ^ 2) + C a * X ^ p : R[X]).natDegree = p ^ 2 := by
    rw [← hexpand, natDegree_expand, hGdeg, pow_one, pow_two]
  refine ⟨hder, hexpand, ?_, ?_, not_exists_expand_of_derivative_ne_zero p hder⟩
  · rw [hGdeg, hPdeg, pow_one, pow_two]
  · rw [hGdeg]
    exact (Fact.out : p.Prime).pos

end

end Polynomial
