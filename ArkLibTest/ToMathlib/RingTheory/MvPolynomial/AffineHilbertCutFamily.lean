/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCutFamily
import ArkLib.ToMathlib.RingTheory.Nullstellensatz.CutFamily
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Acceptance tests for the Bézout potential of iterated retained cut families

These examples use the public API through an ordinary import. In `ℚ[x, y]` they compute the family
of `{⊥}` cut by `x` and then by `x²` to be `{(x)}`, and read off from the potential bound that
`affineDegree (x) ≤ 2` and, with the total-degree corollary for the cuts `[x, x]`, that
`affineDegree (x) ≤ 1`. The boundary example shows that the total-degree corollary needs `1 ≤ b`.
The last examples derive the one-cut potential bound and the properties of the iterated family of
a single prime from the general statements.
-/

open MvPolynomial

namespace AffineHilbertCutFamilyTest

/-- The coordinate ring `ℚ[x, y]` of the plane. -/
local notation "R₂" => MvPolynomial (Fin 2) ℚ

/-- The prime `(x)` of `ℚ[x, y]`. -/
theorem isPrime_span_X0 : (Ideal.span {(X 0 : R₂)}).IsPrime :=
  (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime

/-- `1 ∉ (x)`. -/
theorem one_notMem_span_X0 : (1 : R₂) ∉ Ideal.span {(X 0 : R₂)} := fun h ↦
  isPrime_span_X0.ne_top ((Ideal.eq_top_iff_one _).mpr h)

/-- Cutting `{⊥}` by `x` and then by any `g ∈ (x)`, keeping primes that avoid `1`, gives `{(x)}`.
The second cut changes nothing by `Ideal.retainedCutFamily_of_forall_mem`. -/
theorem iteratedRetainedCutFamily_X0 {g : R₂} (hg : g ∈ Ideal.span {(X 0 : R₂)}) :
    Ideal.iteratedRetainedCutFamily {(⊥ : Ideal R₂)} 1 [X 0, g] = {Ideal.span {X 0}} := by
  have := isPrime_span_X0
  have hfirst : Ideal.retainedCutFamily {(⊥ : Ideal R₂)} 1 (X 0) = {Ideal.span {X 0}} := by
    ext Q
    simp only [Ideal.mem_retainedCutFamily, Finset.mem_singleton, exists_eq_left, bot_sup_eq,
      Ideal.mem_retainedMinimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff, and_iff_left_iff_imp]
    rintro rfl
    exact one_notMem_span_X0
  rw [Ideal.iteratedRetainedCutFamily_cons, hfirst, Ideal.iteratedRetainedCutFamily_cons,
    Ideal.iteratedRetainedCutFamily_nil]
  refine Ideal.retainedCutFamily_of_forall_mem fun P hP ↦ ?_
  rw [Finset.mem_singleton.mp hP]
  exact ⟨isPrime_span_X0, one_notMem_span_X0, hg⟩

/-- `natDegree H((x)) = 1`: `(x)` is the component of the cut of `⊥` by `x`, so purity lowers
`natDegree H(⊥) = 2` by one. -/
theorem natDegree_affineHilbertPolynomial_span_X0 :
    (affineHilbertPolynomial (Ideal.span {(X 0 : R₂)})).natDegree = 1 := by
  have := isPrime_span_X0
  have h := principalCut_natDegree_affineHilbertPolynomial_add_one
    (P := (⊥ : Ideal R₂)) (f := X 0) (fun h ↦ X_ne_zero 0 ((Submodule.mem_bot ℚ).mp h))
    (by rw [bot_sup_eq, Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
  rw [natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

/-- The potential bound for the cuts `[x, x²]` with `b = 2`:
`affineDegree (x) * 2 ^ 1 ≤ affineDegree ⊥ * 2 ^ 2`, so `affineDegree (x) ≤ 2`. -/
example : affineDegree (Ideal.span {(X 0 : R₂)}) ≤ 2 := by
  have h := sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le
    (Ps := {(⊥ : Ideal R₂)}) (fun P hP ↦ Finset.mem_singleton.mp hP ▸ Ideal.isPrime_bot) 1
    (b := 2) (cuts := [X 0, X 0 ^ 2]) (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · rw [totalDegree_X]; norm_num
      · rw [totalDegree_X_pow])
  rw [iteratedRetainedCutFamily_X0 (Ideal.mem_span_singleton.mpr (dvd_pow_self _ two_ne_zero)),
    Finset.sum_singleton, Finset.sum_singleton, natDegree_affineHilbertPolynomial_span_X0,
    affineDegree_bot, natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  norm_num at h
  linarith

/-- The total-degree corollary for the cuts `[x, x]` with `b = 1`: `affineDegree (x) ≤ 1`. -/
example : affineDegree (Ideal.span {(X 0 : R₂)}) ≤ 1 := by
  have h := sum_affineDegree_iteratedRetainedCutFamily_le
    (Ps := {(⊥ : Ideal R₂)}) (fun P hP ↦ Finset.mem_singleton.mp hP ▸ Ideal.isPrime_bot) 1
    le_rfl (cuts := [X 0, X 0]) (by simp [totalDegree_X])
  rwa [iteratedRetainedCutFamily_X0 (Ideal.mem_span_singleton_self _), Finset.sum_singleton,
    Finset.sum_singleton, affineDegree_bot, Nat.cast_one, one_pow, mul_one] at h

/-- The total-degree corollary needs `1 ≤ b`: for `b = 0`, no cuts, and `Ps = {⊥}` in one
variable, the left side is `affineDegree ⊥ = 1` and the right side is `1 * 0 ^ 1 = 0`. -/
example (s : MvPolynomial (Fin 1) ℚ) :
    ¬ ∑ Q ∈ Ideal.iteratedRetainedCutFamily {(⊥ : Ideal (MvPolynomial (Fin 1) ℚ))} s [],
        affineDegree Q ≤
      ∑ P ∈ {(⊥ : Ideal (MvPolynomial (Fin 1) ℚ))},
        affineDegree P * ((0 : ℕ) : ℚ) ^ (affineHilbertPolynomial P).natDegree := by
  rw [Ideal.iteratedRetainedCutFamily_nil, Finset.sum_singleton, Finset.sum_singleton,
    affineDegree_bot, natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  norm_num

/-- The one-cut potential bound, the case `cuts = [f]`. The hypotheses `s ∉ P` and `1 ≤ b` are
not used. -/
example {F σ : Type*} [Field F] [Finite σ] (Ps : Finset (Ideal (MvPolynomial σ F)))
    (hprime : ∀ P ∈ Ps, P.IsPrime) {s f : MvPolynomial σ F} (_hopen : ∀ P ∈ Ps, s ∉ P) {b : ℕ}
    (_hb : 1 ≤ b) (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ Ideal.retainedCutFamily Ps s f,
        affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤
      ∑ P ∈ Ps, affineDegree P * (b : ℚ) ^ (affineHilbertPolynomial P).natDegree :=
  sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le hprime s (cuts := [f])
    (by simpa using hfdeg)

/-- For a prime `P` with `s ∉ P`, every member of the iterated family of `{P}` is a prime above
`P` containing the cuts and avoiding `s`, the potential does not increase, and the family covers
the points of `P` off `s = 0` on which the cuts vanish. The hypothesis `1 ≤ b` is not used. -/
example {F σ E : Type*} [Field F] [Finite σ] [Field E] [Algebra F E]
    {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime) {s : MvPolynomial σ F} (hs : s ∉ P) {b : ℕ}
    (_hb : 1 ≤ b) (cuts : List (MvPolynomial σ F)) (hdeg : ∀ f ∈ cuts, f.totalDegree ≤ b) :
    let T := Ideal.iteratedRetainedCutFamily {P} s cuts
    (∀ Q ∈ T, Q.IsPrime ∧ P ≤ Q ∧ s ∉ Q ∧ ∀ f ∈ cuts, f ∈ Q) ∧
      (∑ Q ∈ T, affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤
        affineDegree P * (b : ℚ) ^ (affineHilbertPolynomial P).natDegree) ∧
      ∀ x : σ → E, x ∈ zeroLocus E P → aeval x s ≠ 0 →
        (∀ f ∈ cuts, aeval x f = 0) → ∃ Q ∈ T, x ∈ zeroLocus E Q := by
  intro T
  have hprime : ∀ Q ∈ ({P} : Finset (Ideal (MvPolynomial σ F))), Q.IsPrime :=
    fun Q hQ ↦ Finset.mem_singleton.mp hQ ▸ hP
  refine ⟨fun Q hQ ↦ ?_, ?_, fun x hxP hxs hcuts ↦ ?_⟩
  · obtain ⟨P₀, hP₀, hP₀Q, hcutsQ⟩ := Ideal.exists_le_of_mem_iteratedRetainedCutFamily hQ
    rw [Finset.mem_singleton.mp hP₀] at hP₀Q
    exact ⟨Ideal.isPrime_of_mem_iteratedRetainedCutFamily hprime s cuts hQ, hP₀Q,
      Ideal.notMem_of_mem_iteratedRetainedCutFamily
        (fun Q hQ ↦ Finset.mem_singleton.mp hQ ▸ hs) cuts hQ, hcutsQ⟩
  · simpa using sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le hprime s hdeg
  · obtain ⟨Q, hQ, -, hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus
      (Finset.mem_singleton_self P) hxP hxs hcuts
    exact ⟨Q, hQ, hxQ⟩

end AffineHilbertCutFamilyTest
