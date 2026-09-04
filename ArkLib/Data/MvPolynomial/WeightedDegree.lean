/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted-degree bounds for multivariate polynomials

This file packages the polynomials whose monomial weights are bounded by a natural number as an
`R`-submodule.  Unlike `weightedTotalDegree`, the support formulation records the intended
zero-polynomial convention directly: the zero polynomial belongs to every bound, including bound
zero.

The bound is additive under multiplication.  Consequently, the weight-zero piece is also closed
under multiplication, while a positive fixed bound is not in general.
-/

noncomputable section

open Finsupp Module

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The `R`-submodule of multivariate polynomials all of whose monomials have `w`-weight at most
`d`. -/
def restrictWeightedDegree (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R {m | m.weight w ≤ d}

/-- Membership in `restrictWeightedDegree` is exactly the pointwise weight bound on support. -/
theorem mem_restrictWeightedDegree {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R} :
    p ∈ restrictWeightedDegree (R := R) w d ↔ ∀ m ∈ p.support, m.weight w ≤ d := by
  rfl

/-- The support formulation agrees with mathlib's `weightedTotalDegree`.  In particular, it gives
the zero polynomial weighted total degree zero, hence membership at bound zero. -/
theorem mem_restrictWeightedDegree_iff_weightedTotalDegree_le {w : σ → ℕ} {d : ℕ}
    {p : MvPolynomial σ R} :
    p ∈ restrictWeightedDegree (R := R) w d ↔ p.weightedTotalDegree w ≤ d := by
  rw [mem_restrictWeightedDegree, weightedTotalDegree, Finset.sup_le_iff]

/-- Increasing the degree bound enlarges the bounded submodule. -/
theorem restrictWeightedDegree_mono (w : σ → ℕ) {d e : ℕ} (hde : d ≤ e) :
    restrictWeightedDegree (R := R) w d ≤ restrictWeightedDegree (R := R) w e := by
  exact restrictSupport_mono R fun _ hm => Nat.le_trans hm hde

/-- A monomial is bounded exactly when its exponent has bounded weight, unless its coefficient
vanishes. -/
@[simp]
theorem monomial_mem_restrictWeightedDegree (w : σ → ℕ) (d : ℕ) (m : σ →₀ ℕ) (r : R) :
    monomial m r ∈ restrictWeightedDegree (R := R) w d ↔ m.weight w ≤ d ∨ r = 0 := by
  simpa only [restrictWeightedDegree, Set.mem_ofPred_eq] using
    (monomial_mem_restrictSupport (R := R) (s := {m | m.weight w ≤ d}) (m := m) (r := r))

/-- Constant polynomials have weighted degree at most every natural-number bound. -/
@[simp]
theorem C_mem_restrictWeightedDegree (w : σ → ℕ) (d : ℕ) (r : R) :
    C r ∈ restrictWeightedDegree (R := R) w d := by
  change monomial (0 : σ →₀ ℕ) r ∈ restrictWeightedDegree (R := R) w d
  exact (monomial_mem_restrictWeightedDegree w d 0 r).mpr (Or.inl (by simp))

/-- The variable `X i` lies in every bound at least its assigned weight. -/
theorem X_mem_restrictWeightedDegree (w : σ → ℕ) (d : ℕ) (i : σ) (hi : w i ≤ d) :
    X i ∈ restrictWeightedDegree (R := R) w d := by
  rw [X, monomial_mem_restrictWeightedDegree]
  simp [weight_single, hi]

/-- Weighted-degree bounds add under multiplication. -/
theorem mul_mem_restrictWeightedDegree {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ restrictWeightedDegree (R := R) w d)
    (hq : q ∈ restrictWeightedDegree (R := R) w e) :
    p * q ∈ restrictWeightedDegree (R := R) w (d + e) := by
  classical
  rw [mem_restrictWeightedDegree] at hp hq ⊢
  intro m hm
  rw [mem_support_iff, coeff_mul] at hm
  obtain ⟨⟨a, b⟩, hab, hcoeff⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have ha : a ∈ p.support := mem_support_iff.mpr (left_ne_zero_of_mul hcoeff)
  have hb : b ∈ q.support := mem_support_iff.mpr (right_ne_zero_of_mul hcoeff)
  rw [← Finset.mem_antidiagonal.mp hab, map_add]
  exact Nat.add_le_add (hp a ha) (hq b hb)

/-- The `n`th power of a polynomial of weighted degree at most `d` has weighted degree at most
`n * d`. -/
theorem pow_mem_restrictWeightedDegree {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictWeightedDegree (R := R) w d) (n : ℕ) :
    p ^ n ∈ restrictWeightedDegree (R := R) w (n * d) := by
  induction n with
  | zero => simpa using C_mem_restrictWeightedDegree (R := R) w 0 (1 : R)
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact mul_mem_restrictWeightedDegree ih hp

/-- A zero-weight variable, and every power of it, belongs to the weight-zero piece.  No
positivity hypothesis belongs in the generic bounded-degree API. -/
theorem X_pow_mem_restrictWeightedDegree_zero {w : σ → ℕ} {i : σ} (hi : w i = 0) (n : ℕ) :
    X i ^ n ∈ restrictWeightedDegree (R := R) w 0 := by
  simpa using pow_mem_restrictWeightedDegree
    (X_mem_restrictWeightedDegree (R := R) w 0 i (by simp [hi])) n

/-- If every variable has positive weight, an exponent of weight zero is the zero exponent. -/
theorem eq_zero_of_mem_restrictWeightedDegree_zero {w : σ → ℕ} (hw : ∀ i, w i ≠ 0)
    {p : MvPolynomial σ R} (hp : p ∈ restrictWeightedDegree (R := R) w 0)
    {m : σ →₀ ℕ} (hm : m ∈ p.support) :
    m = 0 := by
  let hnt : Finsupp.NonTorsionWeight ℕ w := Finsupp.nonTorsionWeight_of ℕ w hw
  apply (@Finsupp.weight_eq_zero_iff_eq_zero σ ℕ _ _ _ _ w hnt).mp
  exact Nat.eq_zero_of_le_zero ((mem_restrictWeightedDegree.mp hp) m hm)

/-- With positive weights, the weight-zero piece consists only of constants. -/
theorem eq_C_coeff_zero_of_mem_restrictWeightedDegree_zero {w : σ → ℕ} (hw : ∀ i, w i ≠ 0)
    {p : MvPolynomial σ R} (hp : p ∈ restrictWeightedDegree (R := R) w 0) :
    p = C (coeff 0 p) := by
  ext m
  by_cases hm : m = 0
  · subst m
    simp
  · have hm_support : m ∉ p.support :=
      fun hmem => hm (eq_zero_of_mem_restrictWeightedDegree_zero hw hp hmem)
    rw [notMem_support_iff.mp hm_support]
    exact (coeff_C_of_ne_zero (R := R) hm (coeff 0 p)).symm

/-- The weight-zero bounded piece is a subalgebra.  This is the fixed-bound multiplication closure
that remains valid without incorrectly claiming the same for a positive bound. -/
def weightedDegreeZeroSubalgebra (w : σ → ℕ) : Subalgebra R (MvPolynomial σ R) where
  carrier := restrictWeightedDegree (R := R) w 0
  add_mem' := (restrictWeightedDegree (R := R) w 0).add_mem
  mul_mem' hp hq := by simpa using mul_mem_restrictWeightedDegree hp hq
  algebraMap_mem' r := by
    rw [algebraMap_eq]
    exact C_mem_restrictWeightedDegree w 0 r

@[simp]
theorem mem_weightedDegreeZeroSubalgebra {w : σ → ℕ} {p : MvPolynomial σ R} :
    p ∈ weightedDegreeZeroSubalgebra (R := R) w ↔
      p ∈ restrictWeightedDegree (R := R) w 0 :=
  Iff.rfl

/-- The monomial basis restricted to exponents of weight at most `d`. -/
def basisRestrictWeightedDegree (w : σ → ℕ) (d : ℕ) :
    Basis {m : σ →₀ ℕ // m.weight w ≤ d} R (restrictWeightedDegree (R := R) w d) :=
  basisRestrictSupport R {m | m.weight w ≤ d}

/-- With finitely many variables and positive weights, the bounded weighted-degree submodule is
finitely generated. -/
theorem restrictWeightedDegree_fg [Finite σ] (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (d : ℕ) :
    (restrictWeightedDegree (R := R) w d).FG := by
  rw [← Module.Finite.iff_fg]
  let finiteExponents : Finite {m : σ →₀ ℕ // m.weight w ≤ d} :=
    (Finsupp.finite_of_nat_weight_le w hw d).to_subtype
  exact @Module.Finite.of_basis R (restrictWeightedDegree (R := R) w d)
    {m : σ →₀ ℕ // m.weight w ≤ d} _ _ _ finiteExponents
    (basisRestrictWeightedDegree (R := R) w d)

/-! ### A nonuniform-weight mutation canary -/

/-- For weights `(1, 2)`, both `X₀²` and `X₁` meet bound two, while `X₁²` does not.  This rejects
implementations that accidentally replace the supplied weights by uniform total degree. -/
theorem nonuniformWeight_canary :
    let w : Fin 2 → ℕ := ![1, 2]
    (X 0 ^ 2 + X 1 : MvPolynomial (Fin 2) ℤ) ∈ restrictWeightedDegree w 2 ∧
      (X 1 ^ 2 : MvPolynomial (Fin 2) ℤ) ∉ restrictWeightedDegree w 2 := by
  dsimp
  constructor
  · apply (restrictWeightedDegree (R := ℤ) ![1, 2] 2).add_mem
    · simpa using pow_mem_restrictWeightedDegree
        (X_mem_restrictWeightedDegree (R := ℤ) ![1, 2] 1 0 (by decide)) 2
    · exact X_mem_restrictWeightedDegree ![1, 2] 2 1 (by decide)
  · rw [X_pow_eq_monomial, monomial_mem_restrictWeightedDegree]
    norm_num [weight_single]

end MvPolynomial
