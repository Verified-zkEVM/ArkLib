/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import ArkLib.ToMathlib.RingTheory.Ideal.Separator
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertRadical

/-!
# Affine Hilbert polynomials of a finite family of components

Let `I : ι → Ideal (MvPolynomial σ k)` be a finite family of ideals, `k` a field and `σ` finite.
Suppose there are separators `s i` whose classes are non-zero-divisors on the quotient by `I i`
and with `s i ∈ I j` for `j ≠ i`. Multiplication by `s i` maps the quotient by `I i` into the
quotient by `⨅ j, I j`, and the sum of these maps is injective: projecting to the quotient by
`I i` kills every summand except the `i`-th, where it is multiplication by the non-zero-divisor
`s i`. When `totalDegree (s i) ≤ b i ≤ N`, the map sends the pieces of degree `N - b i` into the
piece of degree `N`, so
`∑ i, affineHilbertFunction (I i) (N - b i) ≤ affineHilbertFunction (⨅ i, I i) N`.

Passing to polynomials, the shifts by `b i` do not change coefficients in degrees at least the
natural degree. For every `d` at least the natural degree of the affine Hilbert polynomial of
`⨅ i, I i`, the coefficients in degree `d` satisfy
`∑ i, (affineHilbertPolynomial (I i)).coeff d ≤ (affineHilbertPolynomial (⨅ i, I i)).coeff d`.
A component of smaller dimension has coefficient `0` in degree `d`, so it contributes nothing.

Pairwise incomparable prime ideals admit such separators
(`Ideal.exists_separators_of_pairwise_not_le`), and so do the minimal primes over any ideal `J`,
whose intersection is `J.radical`. The affine Hilbert polynomial of `J.radical` has the same
natural degree as that of `J` and is at most it at large natural numbers. Hence, in every degree
`d ≥ natDegree (affineHilbertPolynomial J)`, the coefficients of the minimal primes sum to at most
the coefficient of `J`. Combined with the principal-cut degree drop, this bounds the components of
`I ⊔ span {f}` for a regular `f` of total degree at most `b`: their coefficients in degree
`natDegree P - 1` sum to at most `b * natDegree P * leadingCoeff P`, where `P` is the affine
Hilbert polynomial of `I`.

## Main statements

* `MvPolynomial.sum_affineHilbertFunction_le_iInf`: the Hilbert-function inequality for a family
  with regular separators.
* `MvPolynomial.exists_sum_affineHilbertFunction_le_iInf`: separators and the inequality for
  pairwise incomparable primes.
* `MvPolynomial.sum_coeff_affineHilbertPolynomial_le_of_separators`,
  `MvPolynomial.sum_coeff_affineHilbertPolynomial_le_iInf`: the coefficient inequality.
* `MvPolynomial.sum_coeff_affineHilbertPolynomial_minimalPrimes_le`: the minimal primes of an ideal.
* `MvPolynomial.principalCut_sum_coeff_affineHilbertPolynomial_minimalPrimes_le`,
  `MvPolynomial.principalCut_sum_factorial_mul_leadingCoeff_minimalPrimes_le`: the components of
  a principal cut.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, namespace
`AffineHilbert`.

From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PrimeFamily.lean`: `familySeparatorLift`,
`filteredFamilySeparatorLift`, `separatorFamilyMap` and `separatorFamilyMap_injective` were proof
devices for `sum_shifted_hilbertFunction_le_iInf`; they are private here, and the public result is
`sum_affineHilbertFunction_le_iInf`. The source assumed that each `I i` is prime and `s i ∉ I i`;
here it is enough that the class of `s i` is a non-zero-divisor on the quotient by `I i`, which is
what the injectivity uses. `exists_separators_sum_shifted_hilbertFunction_le_iInf` is
`exists_sum_affineHilbertFunction_le_iInf`, with the separator construction moved to
`Ideal.exists_separators_of_pairwise_not_le` in `ArkLib.ToMathlib.RingTheory.Ideal.Separator`, and
with the source's threshold `N ≥ Finset.univ.sup (totalDegree ∘ s)` written as
`∀ i, totalDegree (s i) ≤ N`.

From `ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/PrimeFamilyCoefficient.lean`:
`sum_hilbertPolynomial_coeff_le_iInf` is `sum_coeff_affineHilbertPolynomial_le_iInf`, a corollary
of `sum_coeff_affineHilbertPolynomial_le_of_separators`. The source's hypothesis that every
component has natural degree at most `d` is dropped: it follows from the bound for `⨅ i, I i`,
because the Hilbert polynomial decreases in degree along inclusions. The three `ℚ[X]` lemmas of
that file are `Polynomial.coeff_nonneg_of_natDegree_le_of_eventually_eval_natCast_nonneg`,
`Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le` and
`Polynomial.coeff_taylor_of_natDegree_le` in `ArkLib.ToMathlib.Polynomial.EventualGrowth`.

From `ArkLib/ToMathlib/AlgebraicGeometry/PrincipalCut/ComponentCoefficient.lean`:
`principalCut_sum_minimalPrime_coeff_le` is
`principalCut_sum_coeff_affineHilbertPolynomial_minimalPrimes_le` and
`principalCut_sum_minimalPrime_factorial_le` is
`principalCut_sum_factorial_mul_leadingCoeff_minimalPrimes_le`. The source assumed that `P` is
prime and `f ∉ P`; here the class of `f` is a non-zero-divisor on the quotient, as in
`MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le`. The source's case
split on `P ⊔ span {f} = ⊤` is not needed. The general statement for the minimal primes of any
ideal, `sum_coeff_affineHilbertPolynomial_minimalPrimes_le`, is new. The source's
`minimalPrimesFinset` and `mem_minimalPrimesFinset` are `Ideal.minimalPrimesFinset` and
`Ideal.mem_minimalPrimesFinset`, its private `minimalPrime_pairwise_incomparable` is
`Ideal.not_le_of_mem_minimalPrimes`, and its private `iInf_minimalPrimes_eq_radical` is
Mathlib's `Ideal.sInf_minimalPrimes`.

The factorial statement keeps the source's hypothesis that every minimal prime of the cut has
natural degree exactly `natDegree P - 1`. For polynomial rings over a field this purity holds,
but its proof needs the equality of the Hilbert-polynomial degree with the Krull dimension, which
is not formalized here.
-/

@[expose] public section

noncomputable section

open Filter Polynomial

namespace MvPolynomial

variable {k σ ι : Type*} [Field k]

/-! ### The Hilbert function of a family with separators -/

/-- Multiplication by `s`, as a `k`-linear map from the quotient by `I` to the quotient by `K`,
when `s * I ⊆ K`. -/
private def mulQuotient (I K : Ideal (MvPolynomial σ k)) (s : MvPolynomial σ k)
    (h : ∀ p ∈ I, s * p ∈ K) : (MvPolynomial σ k ⧸ I) →ₗ[k] MvPolynomial σ k ⧸ K :=
  (I.restrictScalars k).liftQ ((Ideal.Quotient.mkₐ k K).toLinearMap ∘ₗ LinearMap.mulLeft k s)
    fun p hp ↦ by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h p hp)

private theorem mulQuotient_mk {I K : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}
    (h : ∀ p ∈ I, s * p ∈ K) (p : MvPolynomial σ k) :
    mulQuotient I K s h (Ideal.Quotient.mk I p) = Ideal.Quotient.mk K (s * p) :=
  rfl

/-- Multiplication by a separator `s i` sends `I i` into `⨅ j, I j`. -/
private theorem mul_mem_iInf {I : ι → Ideal (MvPolynomial σ k)} {s : ι → MvPolynomial σ k}
    (hmem : ∀ i j, i ≠ j → s i ∈ I j) (i : ι) : ∀ p ∈ I i, s i * p ∈ ⨅ j, I j := by
  classical
  intro p hp
  refine Ideal.mem_iInf.mpr fun j ↦ ?_
  by_cases hij : i = j
  · subst hij
    exact (I i).mul_mem_left _ hp
  · exact (I j).mul_mem_right _ (hmem i j hij)

/-- The sum over `i` of multiplication by `s i` on the pieces of degree `N - b i`. -/
private def separatorMap [Fintype ι] (I : ι → Ideal (MvPolynomial σ k)) (s : ι → MvPolynomial σ k)
    (hmem : ∀ i j, i ≠ j → s i ∈ I j) (b : ι → ℕ) (N : ℕ) :
    ((i : ι) → quotientDegreeLE (I i) (N - b i)) →ₗ[k] MvPolynomial σ k ⧸ ⨅ i, I i :=
  ∑ i, mulQuotient (I i) (⨅ j, I j) (s i) (mul_mem_iInf hmem i) ∘ₗ
    (quotientDegreeLE (I i) (N - b i)).subtype ∘ₗ LinearMap.proj i

/-- Let `I : ι → Ideal (MvPolynomial σ k)` be a finite family and `s i` separators: the class of
`s i` is a non-zero-divisor on the quotient by `I i`, and `s i ∈ I j` for `j ≠ i`. If
`totalDegree (s i) ≤ b i ≤ N` for every `i`, then
`∑ i, affineHilbertFunction (I i) (N - b i) ≤ affineHilbertFunction (⨅ i, I i) N`.

Multiplication by the `s i` gives an injective linear map from the product of the pieces of
degree `N - b i` into the piece of degree `N` of the quotient by `⨅ i, I i`. Both separator
conditions are needed for injectivity, and `b i ≤ N` is needed for the degree count: for `b i > N`
the piece of degree `N - b i = 0` contains `1`, which is sent to the class of `s i`, of total
degree `b i`. For a prime `I i`, the regularity condition is `s i ∉ I i`. -/
theorem sum_affineHilbertFunction_le_iInf [Finite σ] [Fintype ι]
    {I : ι → Ideal (MvPolynomial σ k)} {s : ι → MvPolynomial σ k}
    (hreg : ∀ i, IsLeftRegular (Ideal.Quotient.mk (I i) (s i)))
    (hmem : ∀ i j, i ≠ j → s i ∈ I j) {b : ι → ℕ} (hdeg : ∀ i, (s i).totalDegree ≤ b i)
    {N : ℕ} (hN : ∀ i, b i ≤ N) :
    ∑ i, affineHilbertFunction (I i) (N - b i) ≤ affineHilbertFunction (⨅ i, I i) N := by
  classical
  set Φ := separatorMap I s hmem b N
  have hΦ : ∀ x, Φ x ∈ quotientDegreeLE (⨅ i, I i) N := by
    intro x
    simp only [Φ, separatorMap, LinearMap.sum_apply, LinearMap.comp_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨p, hp, hpx⟩ := mem_quotientDegreeLE.mp (x i).2
    simp only [LinearMap.proj_apply, Submodule.subtype_apply, ← hpx, mulQuotient_mk]
    refine mk_mem_quotientDegreeLE ((totalDegree_mul _ _).trans ?_)
    have := hdeg i
    have := hN i
    omega
  have hker : ∀ x, Φ x = 0 → x = 0 := by
    intro x hx
    funext i
    apply Subtype.ext
    have hfac := congrArg (Ideal.Quotient.factor (iInf_le I i)) hx
    simp only [Φ, separatorMap, LinearMap.sum_apply, LinearMap.comp_apply,
      map_sum, map_zero] at hfac
    rw [Finset.sum_eq_single i] at hfac
    · obtain ⟨p, -, hpx⟩ := mem_quotientDegreeLE.mp (x i).2
      simp only [LinearMap.proj_apply, Submodule.subtype_apply, ← hpx, mulQuotient_mk,
        Ideal.Quotient.factor_mk, map_mul] at hfac
      simp only [Pi.zero_apply, ZeroMemClass.coe_zero, ← hpx]
      exact hreg i (hfac.trans (mul_zero _).symm)
    · intro j _ hji
      obtain ⟨p, -, hpx⟩ := mem_quotientDegreeLE.mp (x j).2
      simp only [LinearMap.proj_apply, Submodule.subtype_apply, ← hpx, mulQuotient_mk,
        Ideal.Quotient.factor_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ((I i).mul_mem_right _ (hmem j i hji))
    · exact fun h ↦ absurd (Finset.mem_univ i) h
  have hinj : Function.Injective Φ := fun x y hxy ↦
    sub_eq_zero.mp (hker _ ((map_sub Φ x y).trans (sub_eq_zero.mpr hxy)))
  have (i : ι) : Module.Free k (quotientDegreeLE (I i) (N - b i)) :=
    Module.Free.of_divisionRing k _
  simp only [affineHilbertFunction]
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_injective (f := Φ.codRestrict _ hΦ)
    fun x y hxy ↦ hinj (congrArg Subtype.val hxy)

/-- A finite family of pairwise incomparable prime ideals has separators `s` with
`s i ∈ P j ↔ i ≠ j`, and then
`∑ i, affineHilbertFunction (P i) (N - totalDegree (s i)) ≤ affineHilbertFunction (⨅ i, P i) N`
for every `N` at least every `totalDegree (s i)`. Incomparability is needed for the separators to
exist: if `P j ≤ P i` with `j ≠ i`, no element lies in `P j` but not in `P i`. -/
theorem exists_sum_affineHilbertFunction_le_iInf [Finite σ] [Fintype ι]
    {P : ι → Ideal (MvPolynomial σ k)} (hP : ∀ i, (P i).IsPrime)
    (hinc : Pairwise fun i j ↦ ¬P i ≤ P j) :
    ∃ s : ι → MvPolynomial σ k, (∀ i j, s i ∈ P j ↔ i ≠ j) ∧
      ∀ N, (∀ i, (s i).totalDegree ≤ N) →
        ∑ i, affineHilbertFunction (P i) (N - (s i).totalDegree) ≤
          affineHilbertFunction (⨅ i, P i) N := by
  obtain ⟨s, hs⟩ := Ideal.exists_separators_of_pairwise_not_le hP hinc
  refine ⟨s, hs, fun N hN ↦ sum_affineHilbertFunction_le_iInf (fun i ↦ ?_)
    (fun i j hij ↦ (hs i j).mpr hij) (fun _ ↦ le_rfl) hN⟩
  have := hP i
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    (mt Ideal.Quotient.eq_zero_iff_mem.mp fun h ↦ (hs i i).mp h rfl)

/-! ### Coefficients of the affine Hilbert polynomials -/

/-- For a finite family `I` with separators as in `sum_affineHilbertFunction_le_iInf`, and every
`d` at least the natural degree of the affine Hilbert polynomial of `⨅ i, I i`,
`∑ i, (affineHilbertPolynomial (I i)).coeff d ≤ (affineHilbertPolynomial (⨅ i, I i)).coeff d`.

The Hilbert-function inequality with `b i = totalDegree (s i)` compares, at large `N`, the sum of
the shifted polynomials `taylor (-b i) (affineHilbertPolynomial (I i))` with the polynomial of
`⨅ i, I i`. Each `I i` contains `⨅ j, I j`, so its polynomial has natural degree at most `d`, and
the shift does not change its coefficient in degree `d`. A component of natural degree below `d`
contributes `0`. The bound on `d` is needed: for `d` below the natural degree of the right side the
coefficients are not comparable in general. -/
theorem sum_coeff_affineHilbertPolynomial_le_of_separators [Finite σ] [Fintype ι]
    {I : ι → Ideal (MvPolynomial σ k)} {s : ι → MvPolynomial σ k}
    (hreg : ∀ i, IsLeftRegular (Ideal.Quotient.mk (I i) (s i)))
    (hmem : ∀ i j, i ≠ j → s i ∈ I j) {d : ℕ}
    (hd : (affineHilbertPolynomial (⨅ i, I i)).natDegree ≤ d) :
    ∑ i, (affineHilbertPolynomial (I i)).coeff d ≤
      (affineHilbertPolynomial (⨅ i, I i)).coeff d := by
  have hdeg : ∀ i, (affineHilbertPolynomial (I i)).natDegree ≤ d := fun i ↦
    (natDegree_affineHilbertPolynomial_le_of_le (iInf_le I i)).trans hd
  set b : ι → ℕ := fun i ↦ (s i).totalDegree
  set S : ℚ[X] := ∑ i, taylor (-(b i : ℚ)) (affineHilbertPolynomial (I i))
  have hS : S.natDegree ≤ d :=
    natDegree_sum_le_of_forall_le _ _ fun i _ ↦ (natDegree_taylor _ _).trans_le (hdeg i)
  have hSd : S.coeff d = ∑ i, (affineHilbertPolynomial (I i)).coeff d := by
    simp only [S, finsetSum_coeff, coeff_taylor_of_natDegree_le _ (hdeg _)]
  rw [← hSd]
  refine coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hS hd ?_
  choose T hT using fun i ↦ exists_eval_affineHilbertPolynomial (I i)
  filter_upwards [eventually_eval_affineHilbertPolynomial (⨅ i, I i),
    eventually_ge_atTop (∑ i, (T i + b i))] with N hN hNT
  have hle : ∀ i, T i + b i ≤ N := fun i ↦
    (Finset.single_le_sum (f := fun i ↦ T i + b i) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans hNT
  have hbN : ∀ i, b i ≤ N := fun i ↦ (Nat.le_add_left _ _).trans (hle i)
  have hTN : ∀ i, T i ≤ N - b i := fun i ↦ Nat.le_sub_of_add_le (hle i)
  calc S.eval (N : ℚ) = ∑ i, (affineHilbertPolynomial (I i)).eval ((N - b i : ℕ) : ℚ) := by
        simp only [S, eval_finsetSum, taylor_eval]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Nat.cast_sub (hbN i), sub_eq_add_neg]
    _ = ∑ i, (affineHilbertFunction (I i) (N - b i) : ℚ) :=
        Finset.sum_congr rfl fun i _ ↦ hT i _ (hTN i)
    _ ≤ affineHilbertFunction (⨅ i, I i) N := by
        exact_mod_cast sum_affineHilbertFunction_le_iInf hreg hmem (fun _ ↦ le_rfl) hbN
    _ = (affineHilbertPolynomial (⨅ i, I i)).eval (N : ℚ) := hN.symm

/-- For a finite family of pairwise incomparable prime ideals and every `d` at least the natural
degree of the affine Hilbert polynomial of their intersection, the coefficients in degree `d` of
the components sum to at most that of the intersection. Components of smaller dimension have
coefficient `0` in degree `d`. -/
theorem sum_coeff_affineHilbertPolynomial_le_iInf [Finite σ] [Fintype ι]
    {P : ι → Ideal (MvPolynomial σ k)} (hP : ∀ i, (P i).IsPrime)
    (hinc : Pairwise fun i j ↦ ¬P i ≤ P j) {d : ℕ}
    (hd : (affineHilbertPolynomial (⨅ i, P i)).natDegree ≤ d) :
    ∑ i, (affineHilbertPolynomial (P i)).coeff d ≤
      (affineHilbertPolynomial (⨅ i, P i)).coeff d := by
  obtain ⟨s, hs⟩ := Ideal.exists_separators_of_pairwise_not_le hP hinc
  refine sum_coeff_affineHilbertPolynomial_le_of_separators (s := s) (fun i ↦ ?_)
    (fun i j hij ↦ (hs i j).mpr hij) hd
  have := hP i
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    (mt Ideal.Quotient.eq_zero_iff_mem.mp fun h ↦ (hs i i).mp h rfl)

/-- For an ideal `J` and every `d` at least the natural degree of its affine Hilbert polynomial,
the coefficients in degree `d` of the affine Hilbert polynomials of the minimal primes over `J`
sum to at most the coefficient of `J`.

The minimal primes are finitely many, pairwise incomparable, and intersect in `J.radical`
(Mathlib's `Ideal.sInf_minimalPrimes`), so `sum_coeff_affineHilbertPolynomial_le_iInf` bounds the
sum by the coefficient of `J.radical`. The radical has a polynomial of the same natural degree
(`natDegree_affineHilbertPolynomial_radical`) that is eventually at most that of `J`. For `J = ⊤`
both sides are `0`. -/
theorem sum_coeff_affineHilbertPolynomial_minimalPrimes_le [Finite σ]
    (J : Ideal (MvPolynomial σ k)) {d : ℕ} (hd : (affineHilbertPolynomial J).natDegree ≤ d) :
    ∑ Q ∈ J.minimalPrimesFinset, (affineHilbertPolynomial Q).coeff d ≤
      (affineHilbertPolynomial J).coeff d := by
  have hrad : (⨅ Q : J.minimalPrimesFinset, (Q : Ideal (MvPolynomial σ k))) = J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact le_antisymm
      (le_sInf fun Q hQ ↦ iInf_le_of_le ⟨Q, Ideal.mem_minimalPrimesFinset.mpr hQ⟩ le_rfl)
      (le_iInf fun Q ↦ sInf_le (Ideal.mem_minimalPrimesFinset.mp Q.2))
  have hraddeg : (affineHilbertPolynomial J.radical).natDegree ≤ d := by
    rwa [natDegree_affineHilbertPolynomial_radical]
  have hcomp := sum_coeff_affineHilbertPolynomial_le_iInf
    (P := fun Q : J.minimalPrimesFinset ↦ (Q : Ideal (MvPolynomial σ k)))
    (fun Q ↦ (Ideal.mem_minimalPrimesFinset.mp Q.2).isPrime)
    (fun Q R hQR ↦ Ideal.not_le_of_mem_minimalPrimes (Ideal.mem_minimalPrimesFinset.mp Q.2)
      (Ideal.mem_minimalPrimesFinset.mp R.2) (Subtype.coe_injective.ne hQR))
    (hrad ▸ hraddeg)
  rw [hrad, Finset.sum_coe_sort J.minimalPrimesFinset
    (fun Q ↦ (affineHilbertPolynomial Q).coeff d)] at hcomp
  exact hcomp.trans (coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hraddeg hd
    (eventually_eval_affineHilbertPolynomial_le_of_le J.le_radical))

/-- The components of a principal cut. Let the class of `f` be a non-zero-divisor on the quotient
by `I`, let `totalDegree f ≤ b`, and let `P` be the affine Hilbert polynomial of `I`. The
coefficients in degree `natDegree P - 1` of the affine Hilbert polynomials of the minimal primes
over `I ⊔ span {f}` sum to at most `b * natDegree P * leadingCoeff P`.

This combines `sum_coeff_affineHilbertPolynomial_minimalPrimes_le` with the principal-cut degree
drop `principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le`. No purity is assumed: a
minimal prime of smaller dimension has coefficient `0` in this degree. Regularity of `f` is
needed as in the degree drop: for `I = span {X ^ 2}` in one variable and `f = X`, the only minimal
prime is `span {X}`, with coefficient `1` in degree `0`, while the bound is `0`. For a prime `I`,
regularity is `f ∉ I`. -/
theorem principalCut_sum_coeff_affineHilbertPolynomial_minimalPrimes_le [Finite σ]
    {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hf : IsLeftRegular (Ideal.Quotient.mk I f)) {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ (I ⊔ Ideal.span {f}).minimalPrimesFinset,
        (affineHilbertPolynomial Q).coeff ((affineHilbertPolynomial I).natDegree - 1) ≤
      (b : ℚ) * (affineHilbertPolynomial I).natDegree *
        (affineHilbertPolynomial I).leadingCoeff :=
  let ⟨hdeg, hcoeff⟩ := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hf hfdeg
  (sum_coeff_affineHilbertPolynomial_minimalPrimes_le _ hdeg).trans hcoeff

/-- The components of a principal cut, in leading-coefficient form. With the hypotheses of
`principalCut_sum_coeff_affineHilbertPolynomial_minimalPrimes_le`, suppose also that every minimal
prime over `I ⊔ span {f}` has affine Hilbert polynomial of natural degree exactly
`natDegree P - 1`. Then
`∑ Q, (natDegree P - 1)! * leadingCoeff Q ≤ b * (natDegree P)! * leadingCoeff P`.

The factorials turn leading coefficients into the multiplicities `d! * leadingCoeff`. The purity
hypothesis turns the coefficients of the previous theorem into leading coefficients; without it a
lower-dimensional minimal prime would contribute its positive leading coefficient to the left
side. For `natDegree P = 0` the bound holds because the leading coefficient of `P` is
nonnegative. -/
theorem principalCut_sum_factorial_mul_leadingCoeff_minimalPrimes_le [Finite σ]
    {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hf : IsLeftRegular (Ideal.Quotient.mk I f)) {b : ℕ} (hfdeg : f.totalDegree ≤ b)
    (hpure : ∀ Q ∈ (I ⊔ Ideal.span {f}).minimalPrimesFinset,
      (affineHilbertPolynomial Q).natDegree = (affineHilbertPolynomial I).natDegree - 1) :
    ∑ Q ∈ (I ⊔ Ideal.span {f}).minimalPrimesFinset,
        (((affineHilbertPolynomial I).natDegree - 1).factorial : ℚ) *
          (affineHilbertPolynomial Q).leadingCoeff ≤
      (b : ℚ) * ((affineHilbertPolynomial I).natDegree.factorial : ℚ) *
        (affineHilbertPolynomial I).leadingCoeff := by
  have hlc : 0 ≤ (affineHilbertPolynomial I).leadingCoeff :=
    leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg
      (eventually_eval_affineHilbertPolynomial_nonneg I)
  have hsum : ∑ Q ∈ (I ⊔ Ideal.span {f}).minimalPrimesFinset,
      (affineHilbertPolynomial Q).leadingCoeff ≤
      (b : ℚ) * (affineHilbertPolynomial I).natDegree *
        (affineHilbertPolynomial I).leadingCoeff := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun Q hQ ↦ ?_)
      (principalCut_sum_coeff_affineHilbertPolynomial_minimalPrimes_le hf hfdeg)
    rw [leadingCoeff, hpure Q hQ]
  rw [← Finset.mul_sum]
  generalize (affineHilbertPolynomial I).natDegree = d at hsum ⊢
  cases d with
  | zero =>
    simp only [CharP.cast_eq_zero, mul_zero, zero_mul] at hsum
    simp only [Nat.zero_sub, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
    exact hsum.trans (mul_nonneg (Nat.cast_nonneg b) hlc)
  | succ e =>
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
    calc (e.factorial : ℚ) * _ ≤ e.factorial * ((b : ℚ) * (e + 1 : ℕ) *
          (affineHilbertPolynomial I).leadingCoeff) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
      _ = _ := by ring

end MvPolynomial
