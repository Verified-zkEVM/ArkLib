/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AwayPresentation

/-!
# Acceptance tests for the presentation of a principal localization

The examples use the public API through an ordinary import. For `I = ⊥` in `ℚ[x]` and `s = x`,
the localization is `ℚ[x, x⁻¹]`; the two Hilbert-function bounds sandwich its presentation
Hilbert function between `N + 1` and `2 * N + 1`, and its Hilbert polynomial has natural degree
`1`. For `s = 0` the localization is the zero ring: its presentation ideal is `⊤`, which shows that
the regularity hypothesis is needed in the lower bound, and the polynomial ring in no variables
surjects onto it, which shows that regularity is needed in the variable-count bound. The last
examples derive the source statements, which assumed that `I` is prime and `s ∉ I`.
-/

open MvPolynomial

namespace AwayPresentationTest

local notation "B" => (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))

/-- The class of `x` is regular on the domain `ℚ[x] ⧸ ⊥`. -/
theorem isLeftRegular_X : IsLeftRegular (Ideal.Quotient.mk B (X 0)) :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero fun h ↦
    X_ne_zero (0 : Fin 1) ((Submodule.mem_bot _).mp (Ideal.Quotient.eq_zero_iff_mem.mp h))

/-- The localization of `ℚ[x]` away from `0` is the zero ring. -/
theorem subsingleton_away_zero : Subsingleton (Localization.Away (Ideal.Quotient.mk B 0)) :=
  IsLocalization.subsingleton (M := Submonoid.powers (Ideal.Quotient.mk B 0))
    ⟨1, by simp⟩

/-- Localizing away from `0` gives the presentation ideal `⊤`. -/
theorem awayPresentationIdeal_zero : awayPresentationIdeal B 0 = ⊤ := by
  have := subsingleton_away_zero
  rw [Ideal.eq_top_iff_one, mem_awayPresentationIdeal]
  exact Subsingleton.elim _ _

/-- The sandwich for `ℚ[x, x⁻¹]`: `N + 1 ≤ H(K, N) ≤ 2 * N + 1`, from
`H(⊥, N) = N + 1` in one variable and `totalDegree x = 1`. -/
example (N : ℕ) :
    N + 1 ≤ affineHilbertFunction (awayPresentationIdeal B (X 0)) N ∧
      affineHilbertFunction (awayPresentationIdeal B (X 0)) N ≤ 2 * N + 1 := by
  have hlo := affineHilbertFunction_le_awayPresentationIdeal isLeftRegular_X N
  have hhi := affineHilbertFunction_awayPresentationIdeal_le B (X 0) N
  rw [affineHilbertFunction_bot, Nat.card_eq_fintype_card, Fintype.card_fin,
    Nat.choose_one_right] at hlo hhi
  rw [totalDegree_X] at hhi
  omega

/-- `ℚ[x, x⁻¹]` has dimension `1`: its presentation ideal has Hilbert polynomial of natural
degree `1`. -/
example : (affineHilbertPolynomial (awayPresentationIdeal B (X 0))).natDegree = 1 := by
  rw [natDegree_affineHilbertPolynomial_awayPresentationIdeal isLeftRegular_X,
    natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Regularity is needed in `affineHilbertFunction_le_awayPresentationIdeal`: localizing `ℚ[x]`
away from `0` gives `H(K, 0) = 0 < 1 = H(⊥, 0)`. -/
example : ¬ affineHilbertFunction B 0 ≤ affineHilbertFunction (awayPresentationIdeal B 0) 0 := by
  rw [awayPresentationIdeal_zero, affineHilbertFunction_top, affineHilbertFunction_bot]
  simp

/-- The upper bound needs no hypothesis: it holds for `s = 0`. -/
example (N : ℕ) : affineHilbertFunction (awayPresentationIdeal B 0) N ≤
    affineHilbertFunction B ((totalDegree (0 : MvPolynomial (Fin 1) ℚ) + 1) * N) :=
  affineHilbertFunction_awayPresentationIdeal_le B 0 N

/-- Regularity is needed in `natDegree_affineHilbertPolynomial_le_card_of_surjective_away`: the
polynomial ring in no variables surjects onto the zero ring `ℚ[x]` localized away from `0`, but
the Hilbert polynomial of `⊥` has natural degree `1 > 0`. -/
example : ∃ g : MvPolynomial (Fin 0) ℚ →ₐ[ℚ] Localization.Away (Ideal.Quotient.mk B 0),
    Function.Surjective g ∧ Nat.card (Fin 0) < (affineHilbertPolynomial B).natDegree := by
  have := subsingleton_away_zero
  refine ⟨aeval fun i ↦ i.elim0, fun y ↦ ⟨0, Subsingleton.elim _ _⟩, ?_⟩
  simp

/-! ### Source-shaped statements -/

variable {k σ τ : Type*} [Field k]

/-- For a prime `P` and `s ∉ P`, the class of `s` is regular on the domain `k[σ] ⧸ P`. -/
theorem isLeftRegular_of_isPrime {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime)
    {s : MvPolynomial σ k} (hs : s ∉ P) : IsLeftRegular (Ideal.Quotient.mk P s) :=
  have := hP
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)

/-- The source's `hilbertFunction_le_awayPresentation_hilbertFunction_two_mul`. -/
example [Finite σ] {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime) {s : MvPolynomial σ k}
    (hs : s ∉ P) (N : ℕ) :
    affineHilbertFunction P N ≤ affineHilbertFunction (awayPresentationIdeal P s) (2 * N) :=
  (affineHilbertFunction_le_awayPresentationIdeal (isLeftRegular_of_isPrime hP hs) N).trans
    (affineHilbertFunction_mono _ (by omega))

/-- The source's `awayPresentation_hilbertFunction_le_hilbertFunction_rescaled`. -/
example [Finite σ] {P : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k} (N : ℕ) :
    affineHilbertFunction (awayPresentationIdeal P s) N ≤
      affineHilbertFunction P (N + N * s.totalDegree) := by
  have h := affineHilbertFunction_awayPresentationIdeal_le P s N
  rwa [show (s.totalDegree + 1) * N = N + N * s.totalDegree by ring] at h

/-- The source's `hilbertPolynomial_natDegree_le_of_surjective_away_algHom`. -/
example [Finite σ] [Finite τ] {J : Ideal (MvPolynomial τ k)} (_hJ : J.IsPrime)
    {t : MvPolynomial τ k} (_ht : t ∉ J)
    {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime) {s : MvPolynomial σ k} (hs : s ∉ P)
    (g : Localization.Away (Ideal.Quotient.mk J t) →ₐ[k]
      Localization.Away (Ideal.Quotient.mk P s))
    (hg : Function.Surjective g) :
    (affineHilbertPolynomial P).natDegree ≤ (affineHilbertPolynomial J).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_surjective_away_away (isLeftRegular_of_isPrime hP hs)
    g hg

/-- The source's `hilbertPolynomial_natDegree_le_of_adjoin_eq_top_away`. -/
example [Finite σ] [Finite τ] {P : Ideal (MvPolynomial σ k)} (hP : P.IsPrime)
    {s : MvPolynomial σ k} (hs : s ∉ P) (x : τ → Localization.Away (Ideal.Quotient.mk P s))
    (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    (affineHilbertPolynomial P).natDegree ≤ Nat.card τ :=
  natDegree_affineHilbertPolynomial_le_card_of_adjoin_eq_top_away
    (isLeftRegular_of_isPrime hP hs) x hx

end AwayPresentationTest
