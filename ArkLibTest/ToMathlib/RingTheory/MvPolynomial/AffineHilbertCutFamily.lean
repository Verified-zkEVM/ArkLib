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
The last examples derive the source's one-cut potential bound and its singleton specification
`iteratedRetainedCutFamily_singleton_spec` from the general statements. For the hypersurface
`x = 0` cut by `xy`, the hypersurface potential bound gives `affineDegree (x) ≤ 1`, and the
source's statements about `hypersurfacePrimeFamily` and `hypersurfaceCutFamily` are derived from
the general ones.
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

/-- The source's `sum_retainedCutFamily_affineDegree_mul_pow_le`: the case `cuts = [f]`. Its
hypotheses `s ∉ P` and `1 ≤ b` are not needed. -/
example {F σ : Type*} [Field F] [Finite σ] (Ps : Finset (Ideal (MvPolynomial σ F)))
    (hprime : ∀ P ∈ Ps, P.IsPrime) {s f : MvPolynomial σ F} (_hopen : ∀ P ∈ Ps, s ∉ P) {b : ℕ}
    (_hb : 1 ≤ b) (hfdeg : f.totalDegree ≤ b) :
    ∑ Q ∈ Ideal.retainedCutFamily Ps s f,
        affineDegree Q * (b : ℚ) ^ (affineHilbertPolynomial Q).natDegree ≤
      ∑ P ∈ Ps, affineDegree P * (b : ℚ) ^ (affineHilbertPolynomial P).natDegree :=
  sum_affineDegree_mul_pow_iteratedRetainedCutFamily_le hprime s (cuts := [f])
    (by simpa using hfdeg)

/-- The source's `iteratedRetainedCutFamily_singleton_spec`, derived from the general statements.
Its hypothesis `1 ≤ b` is not needed. -/
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

/-! ### Hypersurface cut families -/

/-- The only retained minimal prime of the hypersurface `x = 0`, for `s = 1`, is `(x)`. -/
theorem retainedMinimalPrimes_span_X0 :
    (Ideal.span {(X 0 : R₂)}).retainedMinimalPrimes 1 = {Ideal.span {X 0}} := by
  have := isPrime_span_X0
  ext Q
  simp only [Ideal.mem_retainedMinimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
    Set.mem_singleton_iff, Finset.mem_singleton, and_iff_left_iff_imp]
  rintro rfl
  exact one_notMem_span_X0

/-- The hypersurface potential bound for `g = x` (so `v = 1`) cut by `xy` with `b = 2`: the family
stays `{(x)}`, and the bound `affineDegree (x) * 2 ^ 1 ≤ 1 * 2 ^ (2 - 1)` gives
`affineDegree (x) ≤ 1`. -/
example : affineDegree (Ideal.span {(X 0 : R₂)}) ≤ 1 := by
  have h := sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le
    (g := (X 0 : R₂)) (X_ne_zero 0) 1 (v := 1) (b := 2) (by rw [totalDegree_X])
    (cuts := [X 0 * X 1]) (by
      intro f hf
      rw [List.mem_singleton.mp hf]
      exact (totalDegree_mul _ _).trans (by simp [totalDegree_X]))
  have hfam : Ideal.iteratedRetainedCutFamily ((Ideal.span {(X 0 : R₂)}).retainedMinimalPrimes 1)
      1 [X 0 * X 1] = {Ideal.span {X 0}} := by
    rw [retainedMinimalPrimes_span_X0, Ideal.iteratedRetainedCutFamily_cons,
      Ideal.iteratedRetainedCutFamily_nil]
    refine Ideal.retainedCutFamily_of_forall_mem fun P hP ↦ ?_
    rw [Finset.mem_singleton.mp hP]
    exact ⟨isPrime_span_X0, one_notMem_span_X0,
      Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)⟩
  rw [hfam, Finset.sum_singleton, natDegree_affineHilbertPolynomial_span_X0,
    Nat.card_eq_fintype_card, Fintype.card_fin] at h
  norm_num at h
  linarith

section Source

variable {F σ : Type*} [Field F] [Finite σ]

/-- The source's `hypersurfacePrimeFamily_prime_open`, for its family
`(Ideal.span {g}).retainedMinimalPrimes s`. -/
example (g s : MvPolynomial σ F) {P : Ideal (MvPolynomial σ F)}
    (hP : P ∈ (Ideal.span {g}).retainedMinimalPrimes s) : P.IsPrime ∧ s ∉ P :=
  ⟨(Ideal.mem_retainedMinimalPrimes.mp hP).1.isPrime, (Ideal.mem_retainedMinimalPrimes.mp hP).2⟩

/-- The source's `hypersurfacePrimeFamily_dimension`. -/
example (g s : MvPolynomial σ F) (hg : g ≠ 0) {P : Ideal (MvPolynomial σ F)}
    (hP : P ∈ (Ideal.span {g}).retainedMinimalPrimes s) :
    (affineHilbertPolynomial P).natDegree = Nat.card σ - 1 := by
  have h := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton hg
    (Ideal.mem_retainedMinimalPrimes.mp hP).1
  omega

/-- The source's `hypersurfacePrimeFamily_potential_le`. -/
example (g s : MvPolynomial σ F) (hg : g ≠ 0) {v B : ℕ} (hv : g.totalDegree ≤ v) :
    ∑ P ∈ (Ideal.span {g}).retainedMinimalPrimes s,
        affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree ≤
      (v : ℚ) * (B : ℚ) ^ (Nat.card σ - 1) :=
  sum_affineDegree_mul_pow_retainedMinimalPrimes_span_singleton_le hg s hv B

/-- The source's `hypersurfaceCutFamily_spec`, for its family
`Ideal.iteratedRetainedCutFamily ((Ideal.span {g}).retainedMinimalPrimes s) s cuts`. -/
theorem source_hypersurfaceCutFamily_spec (g s : MvPolynomial σ F)
    (cuts : List (MvPolynomial σ F)) {P : Ideal (MvPolynomial σ F)}
    (hP : P ∈ Ideal.iteratedRetainedCutFamily ((Ideal.span {g}).retainedMinimalPrimes s) s cuts) :
    P.IsPrime ∧ s ∉ P ∧ g ∈ P ∧ ∀ f ∈ cuts, f ∈ P := by
  obtain ⟨P₀, hP₀, hle, hcuts⟩ := Ideal.exists_le_of_mem_iteratedRetainedCutFamily hP
  exact ⟨Ideal.isPrime_of_mem_iteratedRetainedCutFamily
      (fun _ hQ ↦ (Ideal.mem_retainedMinimalPrimes.mp hQ).1.isPrime) s cuts hP,
    Ideal.notMem_of_mem_iteratedRetainedCutFamily
      (fun _ hQ ↦ (Ideal.mem_retainedMinimalPrimes.mp hQ).2) cuts hP,
    hle ((Ideal.mem_retainedMinimalPrimes.mp hP₀).1.le (Ideal.mem_span_singleton_self g)),
    hcuts⟩

/-- The source's `hypersurfaceCutFamily_covers`. -/
example {E : Type*} [Field E] [Algebra F E] (g s : MvPolynomial σ F)
    (cuts : List (MvPolynomial σ F)) (x : σ → E) (hg : aeval x g = 0) (hs : aeval x s ≠ 0)
    (hcuts : ∀ f ∈ cuts, aeval x f = 0) :
    ∃ P ∈ Ideal.iteratedRetainedCutFamily ((Ideal.span {g}).retainedMinimalPrimes s) s cuts,
      x ∈ zeroLocus E P := by
  obtain ⟨P₀, hP₀, hxP₀⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus (Ideal.span {g}) s x
    (mem_zeroLocus_iff_le_ker_aeval.mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr hg))) hs
  obtain ⟨P, hP, -, hxP⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus hP₀ hxP₀ hs hcuts
  exact ⟨P, hP, hxP⟩

/-- The source's `hypersurfaceCutFamily_potential_le`; its hypothesis `1 ≤ B` is not needed. -/
example (g s : MvPolynomial σ F) (hg : g ≠ 0) {v B : ℕ} (hv : g.totalDegree ≤ v)
    (_hB : 1 ≤ B) (cuts : List (MvPolynomial σ F)) (hcuts : ∀ f ∈ cuts, f.totalDegree ≤ B) :
    ∑ P ∈ Ideal.iteratedRetainedCutFamily ((Ideal.span {g}).retainedMinimalPrimes s) s cuts,
        affineDegree P * (B : ℚ) ^ (affineHilbertPolynomial P).natDegree ≤
      (v : ℚ) * (B : ℚ) ^ (Nat.card σ - 1) :=
  sum_affineDegree_mul_pow_iteratedRetainedCutFamily_span_singleton_le hg s hv hcuts

/-- The source's `hypersurfaceCutFamily_dimension_le`. -/
example (g s : MvPolynomial σ F) (hg : g ≠ 0) (cuts : List (MvPolynomial σ F))
    {P : Ideal (MvPolynomial σ F)}
    (hP : P ∈ Ideal.iteratedRetainedCutFamily ((Ideal.span {g}).retainedMinimalPrimes s) s cuts) :
    (affineHilbertPolynomial P).natDegree ≤ Nat.card σ - 1 :=
  natDegree_affineHilbertPolynomial_le_of_mem hg
    (source_hypersurfaceCutFamily_spec g s cuts hP).2.2.1

end Source

end AffineHilbertCutFamilyTest
