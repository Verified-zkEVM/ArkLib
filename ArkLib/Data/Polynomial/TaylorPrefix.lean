/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

/-!
# Polynomials from finite Hasse--Taylor prefixes

This file constructs the unique degree-`< K` polynomial with prescribed first `K` Hasse
coefficients at a chosen center.  The construction translates an explicit coefficient polynomial
back from the displacement variable, and is valid over every commutative ring.  In particular, it
uses no factorial denominators or characteristic bounds.

The main declarations are:

* `Polynomial.centeredCoefficientPrefix`, the polynomial reconstructed from a finite coefficient
  prefix;
* `Polynomial.coeff_taylor_centeredCoefficientPrefix` and
  `Polynomial.hasseJet_centeredCoefficientPrefix`, its coefficient and finite-jet specifications;
* `Polynomial.degree_centeredCoefficientPrefix_lt`, its strict degree bound;
* `Polynomial.centeredCoefficientPrefix_succ`, the one-coefficient extension law.

These declarations are ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/Taylor/Numerator.lean` at ArkLib
revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`.  The owner here is independent of Reed--Solomon
codes and differential root finding.
-/

@[expose] public section

open scoped BigOperators

namespace Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- The degree-`< K` polynomial whose first `K` Hasse coefficients at `center` are `c 0`, ...,
`c (K - 1)`.

The finite sum is first formed in the displacement variable and then translated back to the
original variable. -/
def centeredCoefficientPrefix (center : R) (c : ℕ → R) (K : ℕ) : R[X] :=
  taylor (-center) (∑ i : Fin K, monomial i.val (c i.val))

/-- Translating a centered coefficient prefix to the origin recovers its explicit monomial sum. -/
theorem taylor_centeredCoefficientPrefix (center : R) (c : ℕ → R) (K : ℕ) :
    taylor center (centeredCoefficientPrefix center c K) =
      ∑ i : Fin K, monomial i.val (c i.val) := by
  unfold centeredCoefficientPrefix
  rw [taylor_taylor, add_neg_cancel, taylor_zero]

/-- The translated prefix has exactly the prescribed coefficients below `K` and zero coefficients
at and above `K`. -/
theorem coeff_taylor_centeredCoefficientPrefix (center : R) (c : ℕ → R) (K i : ℕ) :
    (taylor center (centeredCoefficientPrefix center c K)).coeff i =
      if i < K then c i else 0 := by
  classical
  rw [taylor_centeredCoefficientPrefix, finsetSum_coeff]
  by_cases hi : i < K
  · rw [ite_eq_left hi]
    rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin K)]
    · simp
    · intro j _ hj
      rw [coeff_monomial, ite_eq_right]
      exact fun h ↦ hj (Fin.ext h)
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_monomial, ite_eq_right]
    intro h
    exact hi (h ▸ j.isLt)

/-- The Hasse coefficient at the chosen center is the prescribed entry below `K`, and zero at and
above `K`. -/
theorem hasseCoeffAt_centeredCoefficientPrefix (center : R) (c : ℕ → R) (K i : ℕ) :
    hasseCoeffAt center i (centeredCoefficientPrefix center c K) =
      if i < K then c i else 0 := by
  rw [hasseCoeffAt_apply, ← taylor_coeff, coeff_taylor_centeredCoefficientPrefix]

/-- A centered coefficient prefix has degree strictly below its length, including at length zero. -/
theorem degree_centeredCoefficientPrefix_lt (center : R) (c : ℕ → R) (K : ℕ) :
    (centeredCoefficientPrefix center c K).degree < K := by
  rw [centeredCoefficientPrefix, degree_taylor]
  simpa only [C_mul_X_pow_eq_monomial] using
    degree_sum_fin_lt (fun i : Fin K ↦ c i.val)

/-- A centered coefficient prefix belongs to the corresponding strict-degree submodule. -/
theorem centeredCoefficientPrefix_mem_degreeLT (center : R) (c : ℕ → R) (K : ℕ) :
    centeredCoefficientPrefix center c K ∈ degreeLT R K := by
  rw [mem_degreeLT]
  exact degree_centeredCoefficientPrefix_lt center c K

/-- The order-`K` Hasse jet of a length-`K` prefix is its prescribed coefficient vector. -/
@[simp]
theorem hasseJet_centeredCoefficientPrefix (center : R) (c : ℕ → R) (K : ℕ) :
    hasseJet K center (centeredCoefficientPrefix center c K) = fun i ↦ c i.val := by
  funext i
  rw [hasseJet_eq_taylor_coeff, coeff_taylor_centeredCoefficientPrefix, ite_eq_left i.isLt]

/-- Every shorter Hasse jet of a centered coefficient prefix is the corresponding initial segment
of its prescribed coefficients. -/
theorem hasseJet_centeredCoefficientPrefix_of_le (center : R) (c : ℕ → R) {m K : ℕ}
    (hmK : m ≤ K) :
    hasseJet m center (centeredCoefficientPrefix center c K) = fun i ↦ c i.val := by
  funext i
  rw [hasseJet_eq_taylor_coeff, coeff_taylor_centeredCoefficientPrefix,
    ite_eq_left (i.isLt.trans_le hmK)]

/-- The empty centered coefficient prefix is the zero polynomial. -/
@[simp]
theorem centeredCoefficientPrefix_zero (center : R) (c : ℕ → R) :
    centeredCoefficientPrefix center c 0 = 0 := by
  simp [centeredCoefficientPrefix]

/-- Appending one coefficient adds the corresponding power of `X - center`. -/
theorem centeredCoefficientPrefix_succ (center : R) (c : ℕ → R) (K : ℕ) :
    centeredCoefficientPrefix center c (K + 1) =
      centeredCoefficientPrefix center c K + C (c K) * (X - C center) ^ K := by
  apply taylor_injective center
  rw [map_add, taylor_centeredCoefficientPrefix, taylor_centeredCoefficientPrefix,
    Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  congr 1
  rw [taylor_mul, taylor_C, taylor_pow]
  simp [taylor_X, C_mul_X_pow_eq_monomial]

end

end Polynomial
