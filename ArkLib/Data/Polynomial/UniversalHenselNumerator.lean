/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jieyi Long, Quang Dao
-/

import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Universal implicit-function numerators

This ring-valued recurrence constructs branch-independent cleared Taylor numerators from a
shifted bivariate polynomial and a designated slope. It commutes with every coefficient ring map.
The definition alone does not assert an implicit-root identity: that requires a compatible
nonzero slope and a root equation, proved separately by consumers.

The outer variable of `Rshift` is the root increment; the inner variable is the parameter
increment. The constant coefficient of the prior prefix is deliberately zero.

## References

Adapted from Jieyi Long's universal numerator construction, building on Remco Bloemen's BCHKS
formalization (Apache-2.0):
https://github.com/proximity-prize/proximity-prize/blob/19bc7d3e21b2261257e1961acd720b2c395d87e1/ProximityPrize/SubmissionLower/BCHKSUniversalNumerator.lean
The recurrence is defined directly here, without importing the donor's Hensel engine.
-/

namespace Polynomial.UniversalHenselNumerator

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Previously constructed positive-index numerators, strictly before index `n`. -/
noncomputable def positivePrefix (prior : ℕ → A) (n : ℕ) : Polynomial A :=
  ∑ i ∈ Finset.Ico 1 n, monomial i (prior i)

/-- The prefix has precisely the positive coefficients before the current index. -/
theorem positivePrefix_coeff (prior : ℕ → A) (n i : ℕ) :
    (positivePrefix prior n).coeff i = if 0 < i ∧ i < n then prior i else 0 := by
  classical
  simp [positivePrefix, coeff_monomial, Nat.succ_le_iff]

@[simp] theorem positivePrefix_zero (prior : ℕ → A) : positivePrefix prior 0 = 0 := by
  simp [positivePrefix]

@[simp] theorem positivePrefix_coeff_self (prior : ℕ → A) (n : ℕ) :
    (positivePrefix prior n).coeff n = 0 := by
  simp [positivePrefix_coeff]

/-- One residual summand; its denominator padding does not depend on a composition of `n-a`. -/
noncomputable def residualTerm (Rshift : Polynomial (Polynomial A)) (s : A)
    (n a b : ℕ) (prior : ℕ → A) : A :=
  ((Rshift.coeff b).coeff a) * s ^ (2 * a + b - 2) *
    ((positivePrefix prior n) ^ b).coeff (n - a)

/-- Cleared residual step with a declared outer-degree cap `d`; used at positive indices. -/
noncomputable def numeratorStep (Rshift : Polynomial (Polynomial A)) (s : A)
    (d n : ℕ) (prior : ℕ → A) : A :=
  -∑ a ∈ Finset.range (n + 1),
    ∑ b ∈ Finset.range (d + 1), residualTerm Rshift s n a b prior

/-- Universal cleared numerators. Index zero is unused; each successor sees only its prior. -/
noncomputable def numerators (Rshift : Polynomial (Polynomial A)) (s : A) (d : ℕ) : ℕ → A
  | 0 => 0
  | t + 1 => numeratorStep Rshift s d (t + 1)
      (fun i ↦ if i ≤ t then numerators Rshift s d i else 0)
termination_by n => n
decreasing_by omega

@[simp] theorem numerators_zero (Rshift : Polynomial (Polynomial A)) (s : A) (d : ℕ) :
    numerators Rshift s d 0 = 0 := by
  rw [numerators]

theorem numerators_succ (Rshift : Polynomial (Polynomial A)) (s : A) (d t : ℕ) :
    numerators Rshift s d (t + 1) = numeratorStep Rshift s d (t + 1)
      (fun i ↦ if i ≤ t then numerators Rshift s d i else 0) := by
  rw [numerators]

/-- Prefix formation commutes with coefficient specialization. -/
theorem positivePrefix_map (f : A →+* B) (prior : ℕ → A) (n : ℕ) :
    (positivePrefix prior n).map f = positivePrefix (fun i ↦ f (prior i)) n := by
  classical
  simp [positivePrefix, Polynomial.map_sum]

/-- Residual summands commute with arbitrary coefficient ring maps. -/
theorem residualTerm_map (f : A →+* B) (Rshift : Polynomial (Polynomial A)) (s : A)
    (n a b : ℕ) (prior : ℕ → A) :
    f (residualTerm Rshift s n a b prior) =
      residualTerm (Rshift.map (mapRingHom f)) (f s) n a b (fun i ↦ f (prior i)) := by
  have hPcoeff : f (((positivePrefix prior n) ^ b).coeff (n - a)) =
      ((positivePrefix (fun i ↦ f (prior i)) n) ^ b).coeff (n - a) := by
    rw [← coeff_map, Polynomial.map_pow, positivePrefix_map]
  have hRcoeff : f ((Rshift.coeff b).coeff a) =
      ((Rshift.map (mapRingHom f)).coeff b).coeff a := by simp
  simp only [residualTerm, map_mul, map_pow, hPcoeff, hRcoeff]

/-- One recurrence step commutes with arbitrary coefficient ring maps. -/
theorem numeratorStep_map (f : A →+* B) (Rshift : Polynomial (Polynomial A)) (s : A)
    (d n : ℕ) (prior : ℕ → A) :
    f (numeratorStep Rshift s d n prior) =
      numeratorStep (Rshift.map (mapRingHom f)) (f s) d n (fun i ↦ f (prior i)) := by
  classical
  simp only [numeratorStep, map_neg, map_sum, residualTerm_map]

/-- The same universal numerator specializes to the recurrence in every coefficient ring. -/
theorem numerators_map (f : A →+* B) (Rshift : Polynomial (Polynomial A)) (s : A) (d : ℕ)
    (n : ℕ) :
    f (numerators Rshift s d n) = numerators (Rshift.map (mapRingHom f)) (f s) d n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ t =>
      rw [numerators_succ, numerators_succ, numeratorStep_map]
      congr 2
      funext i
      by_cases hi : i ≤ t
      · simp only [hi, if_true]
        exact ih i (by omega)
      · simp [hi]

end Polynomial.UniversalHenselNumerator
