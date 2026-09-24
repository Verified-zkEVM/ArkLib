/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Clearing a common-power denominator in a multivariate substitution

Let `Q` be a multivariate polynomial and suppose each variable `i` is to be replaced by a
fraction `N i / S ^ d i` with a common denominator `S`. If every monomial `m` of `Q` has
`∑ d i * m i ≤ H`, then `S ^ H * Q(N / S ^ d)` is a polynomial expression in `S` and the `N i`.
`MvPolynomial.clearedSubstitution` is this expression, written as an explicit finite sum over the
support of `Q`. It is defined in any commutative semiring and needs no division.

## Main statements

* `MvPolynomial.clearedSubstitution`, the cleared numerator.
* `MvPolynomial.map_clearedSubstitution`: after a ring hom `φ` into a field with `φ S ≠ 0`, the
  cleared numerator equals `φ S ^ H` times the rational substitution. This needs the budget
  hypothesis on the support of `Q`.
* `MvPolynomial.ringHom_clearedSubstitution` and `MvPolynomial.clearedSubstitution_map`: ring
  homs on the target and on the coefficients commute with the construction, with no hypothesis.
* `MvPolynomial.totalDegree_clearedSubstitution_le_of_coeff`: if `S` has total degree at most `b`
  and each `N i` has total degree at most `d i * b + 1`, the numerator has total degree at most
  `H * b + v`, where `v` bounds the degree of each monomial of `Q` plus the degree of its mapped
  coefficient. `MvPolynomial.totalDegree_clearedSubstitution` is the case of the coefficient map
  `C`, with `v = totalDegree Q`.
* `MvPolynomial.weightedTotalDegree_clearedSubstitution_le_of_coeff`: the weighted form used to
  derive total-degree and coordinate-degree bounds.
* `MvPolynomial.degreeOf_clearedSubstitution`: a bound on one variable degree of the numerator
  from corresponding bounds on `S` and the `N i`.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

open scoped BigOperators

variable {F R E τ : Type*} [CommSemiring F] [CommSemiring R] [Field E]

/-- The cleared numerator `∑ m ∈ Q.support, f (Q.coeff m) * ∏ i, N i ^ m i * S ^ (H - w m)`,
where `w m = ∑ i, d i * m i` is the denominator weight of `m`.

When every monomial of `Q` has `w m ≤ H`, this is `S ^ H` times `Q` evaluated at
`N i / S ^ d i` (`map_clearedSubstitution`). Without that hypothesis, natural subtraction truncates
`H - w m` to zero on the monomials that exceed the budget, and the identity fails. -/
def clearedSubstitution (f : F →+* R) (S : R) (N : τ → R) (d : τ → ℕ)
    (H : ℕ) (Q : MvPolynomial τ F) : R :=
  ∑ m ∈ Q.support, f (Q.coeff m) *
    (∏ i ∈ m.support, N i ^ m i) * S ^ (H - Finsupp.weight d m)

/-- A ring hom applied to a cleared numerator is the cleared numerator of the mapped data. There
is no invertibility or budget hypothesis. -/
theorem ringHom_clearedSubstitution {T : Type*} [CommSemiring T]
    (f : F →+* R) (φ : R →+* T) (S : R) (N : τ → R) (d : τ → ℕ)
    (H : ℕ) (Q : MvPolynomial τ F) :
    φ (clearedSubstitution f S N d H Q) =
      clearedSubstitution (φ.comp f) (φ S) (fun i ↦ φ (N i)) d H Q := by
  classical
  simp [clearedSubstitution]

/-- Mapping the coefficients of `Q` first gives the same cleared numerator as composing the ring
homs. This holds even when the coefficient map sends some coefficients to zero and so shrinks the
support. -/
theorem clearedSubstitution_map {A : Type*} [CommSemiring A]
    (f : F →+* A) (g : A →+* R) (S : R) (N : τ → R) (d : τ → ℕ)
    (H : ℕ) (Q : MvPolynomial τ F) :
    clearedSubstitution g S N d H (map f Q) =
      clearedSubstitution (g.comp f) S N d H Q := by
  classical
  unfold clearedSubstitution
  simp only [coeff_map, RingHom.comp_apply]
  apply Finset.sum_subset (support_map_subset f Q)
  intro m _ hm
  have hzero : f (Q.coeff m) = 0 := by
    simpa only [notMem_support_iff, coeff_map] using hm
  simp [hzero]

/-- Under a ring hom `φ` into a field with `φ S ≠ 0`, the cleared numerator is `φ S ^ H` times
the rational substitution `Q(φ (N i) / φ S ^ d i)`.

The budget hypothesis `hQ` is needed: a monomial with denominator weight above `H` would require
a negative power of `φ S`, which the numerator truncates to `φ S ^ 0`. -/
theorem map_clearedSubstitution (f : F →+* R) (φ : R →+* E) (S : R)
    (hS : φ S ≠ 0) (N : τ → R) (d : τ → ℕ) (H : ℕ) (Q : MvPolynomial τ F)
    (hQ : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H) :
    φ (clearedSubstitution f S N d H Q) =
      φ S ^ H * eval₂ (φ.comp f) (fun i ↦ φ (N i) / φ S ^ d i) Q := by
  classical
  rw [clearedSubstitution, map_sum, eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [map_mul, map_prod, map_pow, RingHom.comp_apply, div_pow, ← pow_mul]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hweight : (∑ i ∈ m.support, d i * m i) = Finsupp.weight d m := by
    simp [Finsupp.weight_apply, Finsupp.sum, Nat.mul_comm]
  rw [hweight]
  have he : φ S ^ (H - Finsupp.weight d m) * φ S ^ Finsupp.weight d m = φ S ^ H := by
    rw [← pow_add, Nat.sub_add_cancel (hQ m hm)]
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (eq_div_iff (pow_ne_zero _ hS)).mpr
  rw [mul_assoc, he]
  ring

private theorem weightedTotalDegree_finsetSum_le {K σ ι : Type*} [CommSemiring K]
    (w : σ → ℕ) (s : Finset ι) (P : ι → MvPolynomial σ K) (d : ℕ)
    (hP : ∀ i ∈ s, (P i).weightedTotalDegree w ≤ d) :
    (∑ i ∈ s, P i).weightedTotalDegree w ≤ d := by
  classical
  unfold MvPolynomial.weightedTotalDegree
  exact AddMonoidAlgebra.supDegree_sum_le.trans
    (Finset.sup_le fun i hi ↦ hP i hi)

/-- A weighted-degree bound for a cleared numerator from weighted bounds on its inputs. -/
theorem weightedTotalDegree_clearedSubstitution_le_of_coeff {A K σ : Type*} [CommSemiring A]
    [CommSemiring K] (f : A →+* MvPolynomial σ K) (S : MvPolynomial σ K)
    (N : τ → MvPolynomial σ K) (d e : τ → ℕ) (w : σ → ℕ)
    (H b v : ℕ) (Q : MvPolynomial τ A)
    (hS : S.weightedTotalDegree w ≤ b)
    (hN : ∀ i, (N i).weightedTotalDegree w ≤ d i * b + e i)
    (hQ : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hv : ∀ m ∈ Q.support,
      (f (Q.coeff m)).weightedTotalDegree w + Finsupp.weight e m ≤ v) :
    (clearedSubstitution f S N d H Q).weightedTotalDegree w ≤ H * b + v := by
  classical
  rw [clearedSubstitution]
  refine weightedTotalDegree_finsetSum_le w Q.support
    (fun m ↦ f (Q.coeff m) * (∏ i ∈ m.support, N i ^ m i) *
      S ^ (H - Finsupp.weight d m)) (H * b + v) ?_
  intro m hm
  have hprod : (∏ i ∈ m.support, N i ^ m i).weightedTotalDegree w ≤
      Finsupp.weight d m * b + Finsupp.weight e m := by
    calc
      _ ≤ ∑ i ∈ m.support, (N i ^ m i).weightedTotalDegree w := by
        exact AddMonoidAlgebra.supDegree_prod_le (R := K) (A := σ →₀ ℕ) (B := ℕ)
          (D := Finsupp.weight w) (map_zero (Finsupp.weight w))
          (fun a b ↦ map_add (Finsupp.weight w) a b)
      _ ≤ ∑ i ∈ m.support, m i * (d i * b + e i) := by
        apply Finset.sum_le_sum
        intro i _
        exact (weightedTotalDegree_pow_le w (N i) (m i)).trans
          (Nat.mul_le_mul_left _ (hN i))
      _ = Finsupp.weight d m * b + Finsupp.weight e m := by
        simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hpow := (weightedTotalDegree_pow_le w S (H - Finsupp.weight d m)).trans
    (Nat.mul_le_mul_left _ hS)
  have hbudget := Nat.sub_add_cancel (hQ m hm)
  have hmul := weightedTotalDegree_mul_le w
    (f (Q.coeff m) * ∏ i ∈ m.support, N i ^ m i)
    (S ^ (H - Finsupp.weight d m))
  have hcoeff := weightedTotalDegree_mul_le w (f (Q.coeff m))
    (∏ i ∈ m.support, N i ^ m i)
  nlinarith [hv m hm]

/-- Total-degree bound for a cleared numerator with any coefficient map `f` into a polynomial
ring. If `S` has total degree at most `b`, each `N i` has total degree at most `d i * b + 1`,
every monomial of `Q` fits the budget `H`, and every monomial `m` of `Q` satisfies
`(f (Q.coeff m)).totalDegree + m.degree ≤ v`, then the numerator has total degree at most
`H * b + v`.

The shape `d i * b + 1` is the one produced by a numerator with denominator `S ^ d i` that is
linear up to the cleared powers of `S`; the bound is then stable under the recursion. The last
hypothesis is monomialwise, so a coefficient map that raises degrees is charged only on the
monomials where it does. -/
theorem totalDegree_clearedSubstitution_le_of_coeff {A K σ : Type*} [CommSemiring A]
    [CommSemiring K] (f : A →+* MvPolynomial σ K)
    (S : MvPolynomial σ K) (N : τ → MvPolynomial σ K) (d : τ → ℕ)
    (H b v : ℕ) (Q : MvPolynomial τ A)
    (hS : S.totalDegree ≤ b) (hN : ∀ i, (N i).totalDegree ≤ d i * b + 1)
    (hQ : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hv : ∀ m ∈ Q.support, (f (Q.coeff m)).totalDegree + m.degree ≤ v) :
    (clearedSubstitution f S N d H Q).totalDegree ≤ H * b + v := by
  have hS' : S.weightedTotalDegree (1 : σ → ℕ) ≤ b := by
    simpa only [weightedTotalDegree_one] using hS
  have hN' i : (N i).weightedTotalDegree (1 : σ → ℕ) ≤ d i * b + 1 := by
    simpa only [weightedTotalDegree_one] using hN i
  have hv' (m : τ →₀ ℕ) (hm : m ∈ Q.support) :
      (f (Q.coeff m)).weightedTotalDegree (1 : σ → ℕ) +
        Finsupp.weight (1 : τ → ℕ) m ≤ v := by
    have h := hv m hm
    rw [← weightedTotalDegree_one, Finsupp.degree_eq_weight_one] at h
    exact h
  rw [← weightedTotalDegree_one]
  exact weightedTotalDegree_clearedSubstitution_le_of_coeff f S N d (fun _ ↦ 1)
    (fun _ ↦ 1) H b v Q hS' hN' hQ hv'

/-- Total-degree bound for a cleared numerator over a polynomial ring. If `S` has total degree
at most `b`, each `N i` has total degree at most `d i * b + 1`, every monomial of `Q` fits the
budget `H`, and `Q` has total degree at most `v`, then the numerator has total degree at most
`H * b + v`. This is `totalDegree_clearedSubstitution_le_of_coeff` with the coefficient map
`C`. -/
theorem totalDegree_clearedSubstitution {K σ : Type*} [CommSemiring K]
    (S : MvPolynomial σ K) (N : τ → MvPolynomial σ K) (d : τ → ℕ)
    (H b v : ℕ) (Q : MvPolynomial τ K)
    (hS : S.totalDegree ≤ b) (hN : ∀ i, (N i).totalDegree ≤ d i * b + 1)
    (hQ : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hv : Q.totalDegree ≤ v) :
    (clearedSubstitution C S N d H Q).totalDegree ≤ H * b + v := by
  refine totalDegree_clearedSubstitution_le_of_coeff C S N d H b v Q hS hN hQ fun m hm ↦ ?_
  rw [totalDegree_C, zero_add]
  exact (le_totalDegree hm).trans hv

/-- If `S` has degree at most `b` in `i`, each `N j` has degree at most `d j * b + w j`,
every monomial of `Q` fits denominator budget `H`, and its `w`-weight is at most `v`, then the
cleared numerator has degree at most `H * b + v` in `i`. -/
theorem degreeOf_clearedSubstitution {R σ ι : Type*} [CommSemiring R]
    (i : σ) (S : MvPolynomial σ R) (N : ι → MvPolynomial σ R) (d w : ι → ℕ)
    (H b v : ℕ) (Q : MvPolynomial ι R)
    (hS : S.degreeOf i ≤ b) (hN : ∀ j, (N j).degreeOf i ≤ d j * b + w j)
    (hden : ∀ m ∈ Q.support, Finsupp.weight d m ≤ H)
    (hw : ∀ m ∈ Q.support, Finsupp.weight w m ≤ v) :
    (clearedSubstitution C S N d H Q).degreeOf i ≤ H * b + v := by
  classical
  have hS' : S.weightedTotalDegree (Pi.single i 1) ≤ b := by
    simpa only [weightedTotalDegree_piSingle] using hS
  have hN' j : (N j).weightedTotalDegree (Pi.single i 1) ≤ d j * b + w j := by
    simpa only [weightedTotalDegree_piSingle] using hN j
  have hw' (m : ι →₀ ℕ) (hm : m ∈ Q.support) :
      (C (Q.coeff m) : MvPolynomial σ R).weightedTotalDegree (Pi.single i 1) +
        Finsupp.weight w m ≤ v := by
    simpa only [weightedTotalDegree_C, zero_add] using hw m hm
  rw [← weightedTotalDegree_piSingle]
  exact weightedTotalDegree_clearedSubstitution_le_of_coeff C S N d w
    (Pi.single i 1) H b v Q hS' hN' hden hw'

end

end MvPolynomial
