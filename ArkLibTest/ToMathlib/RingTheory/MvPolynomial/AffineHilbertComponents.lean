/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComponents

/-!
# Acceptance tests for Hilbert functions and polynomials of ideal families

In one variable the points `X₀ = 0` and `X₀ = 1` are separated by `X₀ - 1` and `X₀`, and the
separator inequality gives `2 ≤ affineHilbertFunction (span {X₀} ⊓ span {X₀ - 1}) N` for `N ≥ 1`.
Two copies of `span {X₀}` with the separator `X₀` satisfy every hypothesis except regularity, and
the conclusion would read `2 ≤ 1`, so regularity is needed. The examples also derive the
source-shaped statements: the separator theorem with the threshold
`Finset.univ.sup (fun i ↦ (s i).totalDegree)`, the coefficient sum with its redundant degree bound
on the components, and the prime forms of the principal-cut component bounds.
-/

open MvPolynomial

namespace AffineHilbertComponentsTest

/-- If `h - g` is a unit, the class of `h` modulo `g` is a unit, hence regular. -/
theorem isLeftRegular_mk_of_isUnit_sub {R : Type*} [CommRing R] {g h : R}
    (hgh : IsUnit (h - g)) : IsLeftRegular (Ideal.Quotient.mk (Ideal.span {g}) h) := by
  have : Ideal.Quotient.mk (Ideal.span {g}) h = Ideal.Quotient.mk (Ideal.span {g}) (h - g) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self g), sub_zero]
  rw [this]
  exact (hgh.map _).isRegular.left

/-- A principal ideal whose generator vanishes at a point is proper. -/
theorem span_ne_top_of_eval_eq_zero {g : MvPolynomial (Fin 1) ℚ} (a : Fin 1 → ℚ)
    (hg : eval a g = 0) : Ideal.span {g} ≠ ⊤ := by
  intro h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp ((Ideal.eq_top_iff_one _).mp h)
  have := congrArg (eval a) hq
  simp [hg] at this

/-- The two points `X₀ = 0` and `X₀ = 1` of the line. -/
noncomputable abbrev twoPoints : Fin 2 → Ideal (MvPolynomial (Fin 1) ℚ) :=
  ![Ideal.span {X 0}, Ideal.span {X 0 - C 1}]

/-- The separators `X₀ - 1` and `X₀` of the two points. -/
noncomputable abbrev twoPointSeparators : Fin 2 → MvPolynomial (Fin 1) ℚ := ![X 0 - C 1, X 0]

/-- Each separator is regular modulo its own point, because it differs from the generator of that
point by a unit. -/
theorem twoPoints_regular (i : Fin 2) :
    IsLeftRegular (Ideal.Quotient.mk (twoPoints i) (twoPointSeparators i)) := by
  fin_cases i
  · change IsLeftRegular (Ideal.Quotient.mk (Ideal.span {X 0}) (X 0 - C 1))
    exact isLeftRegular_mk_of_isUnit_sub
      (by rw [sub_sub_cancel_left, map_one]; exact isUnit_one.neg)
  · change IsLeftRegular (Ideal.Quotient.mk (Ideal.span {X 0 - C 1}) (X 0))
    exact isLeftRegular_mk_of_isUnit_sub (by rw [sub_sub_cancel, map_one]; exact isUnit_one)

/-- Each separator lies in the ideal of the other point. -/
theorem twoPoints_mem (i j : Fin 2) (hij : i ≠ j) : twoPointSeparators i ∈ twoPoints j := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · change X 0 - C 1 ∈ Ideal.span {X 0 - C 1}
    exact Ideal.mem_span_singleton_self _
  · change X 0 ∈ Ideal.span {X 0}
    exact Ideal.mem_span_singleton_self _
  · exact absurd rfl hij

/-- Both separators have total degree at most `1`. -/
theorem twoPoints_totalDegree (i : Fin 2) : (twoPointSeparators i).totalDegree ≤ 1 := by
  fin_cases i
  · change (X 0 - C 1 : MvPolynomial (Fin 1) ℚ).totalDegree ≤ 1
    exact (totalDegree_sub_C_le _ _).trans (totalDegree_X 0).le
  · change (X 0 : MvPolynomial (Fin 1) ℚ).totalDegree ≤ 1
    exact (totalDegree_X 0).le

/-- Both point ideals are proper. -/
theorem twoPoints_ne_top (i : Fin 2) : twoPoints i ≠ ⊤ := by
  fin_cases i
  · change Ideal.span {X 0} ≠ ⊤
    exact span_ne_top_of_eval_eq_zero 0 (by simp)
  · change Ideal.span {X 0 - C 1} ≠ ⊤
    exact span_ne_top_of_eval_eq_zero 1 (by simp)

/-- The separator inequality for the two points: for `N ≥ 1`, the quotient by the ideal of both
points has at least two dimensions in degree `N`, one from each point. -/
example {N : ℕ} (hN : 1 ≤ N) : 2 ≤ affineHilbertFunction (⨅ i, twoPoints i) N := by
  have h := sum_affineHilbertFunction_le_iInf (b := fun _ ↦ 1) twoPoints_regular twoPoints_mem
    twoPoints_totalDegree (fun _ ↦ hN)
  rw [Fin.sum_univ_two] at h
  have h0 := one_le_affineHilbertFunction (twoPoints_ne_top 0) (N - 1)
  have h1 := one_le_affineHilbertFunction (twoPoints_ne_top 1) (N - 1)
  omega

/-- The regularity hypothesis is needed. For the family `span {X₀}, span {X₀}` with separator `X₀`
for both, each separator lies in the other ideal and has total degree `1`, but the class of `X₀`
is `0`. The separator inequality at `N = 1` would read `1 + 1 ≤ 1`, since the quotient by
`span {X₀}` has one dimension in every degree. -/
example :
    (∀ i j : Fin 2, i ≠ j → (X 0 : MvPolynomial (Fin 1) ℚ) ∈ Ideal.span {X 0}) ∧
      ¬ IsLeftRegular (Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) (X 0)) ∧
      ¬ (∑ _i : Fin 2,
          affineHilbertFunction (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) (1 - 1) ≤
        affineHilbertFunction (⨅ _i : Fin 2, Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) 1) := by
  have hmk : Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) (X 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hne := span_ne_top_of_eval_eq_zero (g := (X 0 : MvPolynomial (Fin 1) ℚ)) 0 (by simp)
  refine ⟨fun _ _ _ ↦ Ideal.mem_span_singleton_self _, fun hreg ↦ ?_, fun hle ↦ ?_⟩
  · rw [hmk] at hreg
    have := hreg (show (0 : MvPolynomial (Fin 1) ℚ ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) *
      1 = 0 * 0 by simp)
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem] at this
    exact hne ((Ideal.eq_top_iff_one _).mpr this)
  · rw [iInf_const, Fin.sum_univ_two] at hle
    have h0 := one_le_affineHilbertFunction hne (1 - 1)
    have h1 : (affineHilbertFunction (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) 1 : ℚ) = 1 := by
      rw [affineHilbertFunction_span_singleton (X_ne_zero 0) (totalDegree_X 0).le,
        totalDegree_X, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num [Nat.choose]
    have h1' : affineHilbertFunction (Ideal.span {(X 0 : MvPolynomial (Fin 1) ℚ)}) 1 = 1 := by
      exact_mod_cast h1
    omega

/-- For a prime `P` and `f ∉ P`, the class of `f` is regular modulo `P`. -/
theorem isLeftRegular_mk_of_isPrime {k σ : Type*} [Field k] {P : Ideal (MvPolynomial σ k)}
    (hP : P.IsPrime) {f : MvPolynomial σ k} (hfP : f ∉ P) :
    IsLeftRegular (Ideal.Quotient.mk P f) := by
  have := hP
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    (mt Ideal.Quotient.eq_zero_iff_mem.mp hfP)

variable {k σ ι : Type*} [Field k] [Finite σ] [Fintype ι]

/-- The source's `exists_separators_sum_shifted_hilbertFunction_le_iInf`: separate conditions on
the separators and the common threshold `Finset.univ.sup (fun i ↦ (s i).totalDegree)`. -/
example (P : ι → Ideal (MvPolynomial σ k)) (hP : ∀ i, (P i).IsPrime)
    (hinc : ∀ ⦃i j⦄, i ≠ j → ¬P i ≤ P j) :
    ∃ s : ι → MvPolynomial σ k,
      (∀ i, s i ∉ P i) ∧ (∀ i j, i ≠ j → s i ∈ P j) ∧
      ∀ N ≥ Finset.univ.sup (fun i ↦ (s i).totalDegree),
        ∑ i, affineHilbertFunction (P i) (N - (s i).totalDegree) ≤
          affineHilbertFunction (⨅ i, P i) N := by
  obtain ⟨s, hs, hle⟩ := exists_sum_affineHilbertFunction_le_iInf hP hinc
  exact ⟨s, fun i h ↦ (hs i i).mp h rfl, fun i j hij ↦ (hs i j).mpr hij,
    fun N hN ↦ hle N fun i ↦ (Finset.le_sup (f := fun i ↦ (s i).totalDegree)
      (Finset.mem_univ i)).trans hN⟩

/-- The source's `sum_hilbertPolynomial_coeff_le_iInf`, with its degree bound `hPdeg` on the
components, which the general statement does not need. -/
example (P : ι → Ideal (MvPolynomial σ k)) (hP : ∀ i, (P i).IsPrime)
    (hinc : ∀ ⦃i j⦄, i ≠ j → ¬P i ≤ P j) (d : ℕ)
    (_hPdeg : ∀ i, (affineHilbertPolynomial (P i)).natDegree ≤ d)
    (hInfDeg : (affineHilbertPolynomial (⨅ i, P i)).natDegree ≤ d) :
    ∑ i, (affineHilbertPolynomial (P i)).coeff d ≤
      (affineHilbertPolynomial (⨅ i, P i)).coeff d :=
  sum_coeff_affineHilbertPolynomial_le_iInf hP hinc hInfDeg

/-- The source's `principalCut_sum_minimalPrime_coeff_le`, for a prime `P` and `f ∉ P`. -/
example {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime) {f : MvPolynomial σ k} (hfP : f ∉ P)
    {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    let J := P ⊔ Ideal.span {f}
    let d := (affineHilbertPolynomial P).natDegree
    ∑ Q ∈ J.minimalPrimesFinset, (affineHilbertPolynomial Q).coeff (d - 1) ≤
      (b : ℚ) * d * (affineHilbertPolynomial P).leadingCoeff :=
  principalCut_sum_coeff_affineHilbertPolynomial_minimalPrimes_le
    (isLeftRegular_mk_of_isPrime hP hfP) hfdeg

/-- The source's `principalCut_sum_minimalPrime_factorial_le`, for a prime `P` and `f ∉ P`. -/
example {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime) {f : MvPolynomial σ k} (hfP : f ∉ P)
    {b : ℕ} (hfdeg : f.totalDegree ≤ b)
    (hchildren : ∀ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimesFinset,
      (affineHilbertPolynomial Q).natDegree = (affineHilbertPolynomial P).natDegree - 1) :
    ∑ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimesFinset,
        (((affineHilbertPolynomial P).natDegree - 1).factorial : ℚ) *
          (affineHilbertPolynomial Q).leadingCoeff ≤
      (b : ℚ) * ((affineHilbertPolynomial P).natDegree.factorial : ℚ) *
        (affineHilbertPolynomial P).leadingCoeff :=
  principalCut_sum_factorial_mul_leadingCoeff_minimalPrimes_le
    (isLeftRegular_mk_of_isPrime hP hfP) hfdeg hchildren

/-- For a prime `J`, the only minimal prime over `J` is `J`, so the sum in
`sum_coeff_affineHilbertPolynomial_minimalPrimes_le` has the single term `J` and the bound holds
with equality. -/
example (J : Ideal (MvPolynomial σ k)) [J.IsPrime] (d : ℕ) :
    ∑ Q ∈ J.minimalPrimesFinset, (affineHilbertPolynomial Q).coeff d =
      (affineHilbertPolynomial J).coeff d := by
  rw [Ideal.minimalPrimesFinset_of_isPrime, Finset.sum_singleton]

end AffineHilbertComponentsTest
