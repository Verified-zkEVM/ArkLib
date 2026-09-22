/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPurity
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Acceptance tests for purity and the Bézout bound of principal cuts

These examples use the public API through an ordinary import. In `ℚ[x, y]` they compute from
purity that the prime `(x)` has a Hilbert polynomial of natural degree one, bound its affine
degree by one with the Bézout bound, and evaluate the degree potential of the cut. The boundary
examples show that the Bézout bound fails without `f ∉ P` and that the normalization degree count
needs injectivity. The last examples restate purity, the Bézout bound and the cut
potential with primality of `P` as an explicit argument.
-/

open MvPolynomial

namespace AffineHilbertPurityTest

/-- The coordinate ring `ℚ[x, y]` of the plane. -/
local notation "R₂" => MvPolynomial (Fin 2) ℚ

/-- The prime `(x)` of `ℚ[x, y]`. -/
theorem isPrime_span_X0 : (Ideal.span {(X 0 : R₂)}).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime

/-- `x` is not in the zero ideal. -/
theorem X0_notMem_bot : (X 0 : R₂) ∉ (⊥ : Ideal R₂) :=
  fun h ↦ X_ne_zero 0 ((Submodule.mem_bot ℚ).mp h)

/-- `(x)` is the only minimal prime of the cut of `⊥` by `x`. -/
theorem minimalPrimes_cut_X0 :
    ((⊥ : Ideal R₂) ⊔ Ideal.span {X 0}).minimalPrimes =
      {Ideal.span {X 0}} := by
  have := isPrime_span_X0
  rw [bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self]

/-- Purity computes a Hilbert polynomial: `(x)` is a component of the cut of `⊥` by `x`, so its
Hilbert polynomial has natural degree `2 - 1 = 1`. -/
theorem natDegree_affineHilbertPolynomial_span_X0 :
    (affineHilbertPolynomial (Ideal.span {(X 0 : R₂)})).natDegree = 1 := by
  have h := principalCut_natDegree_affineHilbertPolynomial_add_one
    (P := (⊥ : Ideal R₂)) (f := X 0) X0_notMem_bot
    (minimalPrimes_cut_X0.symm ▸ Set.mem_singleton _)
  rw [natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

/-- The Bézout bound for the cut of `⊥` by the linear form `x`: the component `(x)` has affine
degree at most `1 * affineDegree ⊥ = 1`. -/
example : affineDegree (Ideal.span {(X 0 : R₂)}) ≤ 1 := by
  have h := principalCut_sum_affineDegree_minimalPrimes_le (P := (⊥ : Ideal R₂)) (f := X 0)
    (b := 1)     X0_notMem_bot (by rw [totalDegree_X])
  have hfin : ((⊥ : Ideal R₂) ⊔ Ideal.span {X 0}).minimalPrimesFinset =
      {Ideal.span {X 0}} := by
    ext Q
    rw [Ideal.mem_minimalPrimesFinset, minimalPrimes_cut_X0, Finset.mem_singleton,
      Set.mem_singleton_iff]
  rwa [hfin, Finset.sum_singleton, affineDegree_bot, Nat.cast_one, one_mul] at h

/-- The degree potential of the cut of `⊥` by `x`, keeping the components that avoid `1`, is at
most `affineDegree ⊥ * 1 ^ 2 = 1`. -/
example : ∑ Q ∈ ((⊥ : Ideal R₂) ⊔ Ideal.span {X 0}).retainedMinimalPrimes 1,
      affineDegree Q * ((1 : ℕ) : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤ 1 := by
  have h := sum_affineDegree_mul_pow_retainedMinimalPrimes_le (P := (⊥ : Ideal R₂)) 1 (f := X 0)
    (b := 1) (by rw [totalDegree_X])
  rwa [affineDegree_bot, Nat.cast_one, one_pow, mul_one] at h

/-- The Bézout bound for the components of the cut of `⊥` by `x` that avoid `x - 1`: their
affine degrees sum to at most `1 * affineDegree ⊥ = 1`. -/
example : ∑ Q ∈ ((⊥ : Ideal R₂) ⊔ Ideal.span {X 0}).retainedMinimalPrimes (X 0 - 1),
      affineDegree Q ≤ 1 := by
  have h := principalCut_sum_affineDegree_retainedMinimalPrimes_le (P := (⊥ : Ideal R₂))
    (X 0 - 1) (f := X 0) (b := 1) X0_notMem_bot (by rw [totalDegree_X])
  rwa [affineDegree_bot, Nat.cast_one, one_mul] at h

/-- The hypothesis `f ∉ P` is needed for the Bézout bound: for `P = ⊥` and `f = 0 ∈ P` with
`b = 0`, the only minimal prime of the cut is `⊥`, of affine degree `1`, while the bound would
be `0`. -/
example : ¬ ∑ Q ∈ ((⊥ : Ideal R₂) ⊔ Ideal.span {0}).minimalPrimesFinset,
      affineDegree Q ≤ ((0 : ℕ) : ℚ) * affineDegree (⊥ : Ideal R₂) := by
  have hfin : ((⊥ : Ideal R₂) ⊔ Ideal.span {0}).minimalPrimesFinset =
      {⊥} := by
    ext Q
    rw [Ideal.mem_minimalPrimesFinset, Ideal.span_singleton_zero, bot_sup_eq,
      Ideal.minimalPrimes_eq_subsingleton_self, Finset.mem_singleton, Set.mem_singleton_iff]
  rw [hfin, Finset.sum_singleton, affineDegree_bot]
  norm_num

/-- The hypothesis `f ∉ P` is needed for purity: for `f ∈ P` the prime `P` is a minimal prime of
the cut, and its natural degree does not drop. -/
example (P : Ideal R₂) [P.IsPrime] :
    P ∈ (P ⊔ Ideal.span {0}).minimalPrimes ∧
      (affineHilbertPolynomial P).natDegree + 1 ≠ (affineHilbertPolynomial P).natDegree := by
  refine ⟨?_, by omega⟩
  rw [Ideal.span_singleton_zero, sup_bot_eq, Ideal.minimalPrimes_eq_subsingleton_self]
  rfl

/-- Injectivity is needed in `natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective`:
the quotient map `ℚ[x] → ℚ[x] ⧸ ⊤` is finite, but the natural degree of `H(⊤)` is `0`, not the
number `1` of variables of the source. -/
example : (Ideal.Quotient.mkₐ ℚ (⊤ : Ideal (MvPolynomial (Fin 1) ℚ))).Finite ∧
    (affineHilbertPolynomial (⊤ : Ideal (MvPolynomial (Fin 1) ℚ))).natDegree ≠
      Nat.card (Fin 1) := by
  refine ⟨RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  rw [natDegree_affineHilbertPolynomial_eq_zero_iff.mpr inferInstance, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

/-- Purity of principal cuts, with primality of `P` as an explicit argument. -/
example {F σ : Type*} [Field F] [Finite σ] {P J : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {f : MvPolynomial σ F} (hf : f ∉ P) (hJ : J ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    (affineHilbertPolynomial J).natDegree + 1 = (affineHilbertPolynomial P).natDegree :=
  principalCut_natDegree_affineHilbertPolynomial_add_one hf hJ

/-- The Bézout bound, with primality of `P` as an explicit argument. -/
example {F σ : Type*} [Field F] [Finite σ] {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {f : MvPolynomial σ F} (hfP : f ∉ P) {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ (P ⊔ Ideal.span {f}).minimalPrimesFinset, affineDegree Q ≤ (b : ℚ) * affineDegree P :=
  principalCut_sum_affineDegree_minimalPrimes_le hfP hfdeg

/-- The degree potential for the family that is `{P}` when `f ∈ P` and the retained minimal
primes of `P ⊔ span {f}` otherwise. The hypothesis `s ∉ P` identifies this family with the
retained minimal primes; the hypothesis `1 ≤ b` is not used. -/
example {F σ : Type*} [Field F] [Finite σ] {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s f : MvPolynomial σ F} [Decidable (f ∈ P)] (hs : s ∉ P) {b : ℕ} (_hb : 1 ≤ b)
    (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ (if f ∈ P then {P} else (P ⊔ Ideal.span {f}).retainedMinimalPrimes s),
        affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤
      affineDegree P * (b : ℚ) ^ (affineHilbertPolynomial P).natDegree := by
  have hfam : (if f ∈ P then {P} else (P ⊔ Ideal.span {f}).retainedMinimalPrimes s) =
      (P ⊔ Ideal.span {f}).retainedMinimalPrimes s := by
    split_ifs with hf
    · exact (Ideal.retainedMinimalPrimes_sup_span_of_mem hf hs).symm
    · rfl
  rw [hfam]
  exact sum_affineDegree_mul_pow_retainedMinimalPrimes_le s hfdeg

end AffineHilbertPurityTest
