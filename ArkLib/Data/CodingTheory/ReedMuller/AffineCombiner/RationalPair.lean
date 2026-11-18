/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Exceptional coefficient vectors for one rational pair on a grid

Let `K₀ ⊆ F` be finite fields of sizes `q₀ ≤ q`, and let `n = q₀ᵏ` be the size of the grid `K₀ᵏ`.
Fix rational functions `F₀, G₀` in the fraction field of `F[X₁, …, Xₖ]`.
These results formalize Lemma A.1 of [CWYZ26], at agreement loss `n / q₀ = q₀ᵏ⁻¹`.
The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

Suppose `F₀, G₀` are polynomials of total degrees `≤ d` and `< d`.
An exceptional candidate `F₀ + L_α G₀` loses more than `q₀ᵏ⁻¹` agreement points.
At each lost point the value of `L_α` is fixed by the pair and the received words.
By (7.1), the lost points include `k + 1` points whose values determine `α`.
So at most `n choose (k + 1)` coefficient vectors are exceptional.

Otherwise, the vectors `α` for which `F₀ + L_α G₀` is a polynomial of total degree at most `d`
lie on one affine line, so there are at most `q` of them.
For two such vectors `α ≠ α'`, the product `L_{α - α'} G₀` is a polynomial.
If `G₀` is not a polynomial, a nonzero such `L_σ` is prime and divides every other one.
If `G₀` is a polynomial of total degree at least `d`, every difference has a constant multiplier.
Combining the cases gives at most `max q (n choose (k + 1))` exceptional vectors.

The paper's degree bound `d = ρ q₀` is positive.
The last three main statements need `1 ≤ d`.
At `d = 0` the pair `F₀ = G₀ = 0` is not a witness pair, since no total degree is below zero.
Every coefficient vector then keeps `F₀ + L_α G₀ = 0` a polynomial, so the count can be `q^{k+1}`.

## Main statements

* `ReedSolomon.eval_reedMullerMultiplier_eq_of_mem_reedMullerAgreementLoss`: a lost point fixes
  the multiplier value.
* `ReedSolomon.card_isReedMullerExceptional_add_mul_le`: the polynomial witness case.
* `ReedSolomon.exists_forall_eq_smul_of_reedMullerMultiplier_mul_eq`: the coefficient vectors
  making `L_σ G₀` a polynomial are multiples of one vector.
* `ReedSolomon.card_reedMuller_fractionRing_combination_le`: compatibility outside the witness
  degree bounds.
* `ReedSolomon.card_isReedMullerExceptional_fractionRing_le`: the bound for every rational pair.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial Finset ReedMuller

variable {K₀ : Type*} [Field K₀] [Fintype K₀] {F : Type*} [Field F] [DecidableEq F]
  [Algebra K₀ F] {k : ℕ}

/-- Fix polynomials `F₀, G₀` and received words `f, g` on the grid `K₀ᵏ`.
Two coefficient vectors whose candidates `F₀ + L_α G₀` both lose the grid point `z` take the
same multiplier value at `z`. -/
theorem eval_reedMullerMultiplier_eq_of_mem_reedMullerAgreementLoss
    {f g : (Fin k → K₀) → F} {F₀ G₀ : MvPolynomial (Fin k) F} {α α' : Fin (k + 1) → F}
    {z : Fin k → K₀}
    (h : z ∈ reedMullerAgreementLoss f g (reedMullerMultiplier α)
      (F₀ + reedMullerMultiplier α * G₀) F₀ G₀)
    (h' : z ∈ reedMullerAgreementLoss f g (reedMullerMultiplier α')
      (F₀ + reedMullerMultiplier α' * G₀) F₀ G₀) :
    eval (gridPoint F z) (reedMullerMultiplier α) =
      eval (gridPoint F z) (reedMullerMultiplier α') := by
  rw [mem_reedMullerAgreementLoss, reedMullerCombinedWord_apply, map_add, map_mul] at h h'
  set a := eval (gridPoint F z) (reedMullerMultiplier α)
  set a' := eval (gridPoint F z) (reedMullerMultiplier α')
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', -⟩ := h'
  have hG : eval (gridPoint F z) G₀ ≠ g z := by
    intro hG
    rw [hG] at h1
    exact h2.elim (fun h ↦ h (by linear_combination h1)) (fun h ↦ h hG)
  have : (a - a') * (eval (gridPoint F z) G₀ - g z) = 0 := by
    linear_combination h1 - h1'
  rcases mul_eq_zero.mp this with h | h
  · linear_combination h
  · exact absurd (sub_eq_zero.mp h) hG

open Classical in
/-- Let `K₀ ⊆ F` be finite fields of sizes `q₀` and `q`, and let `n = q₀ᵏ`.
If `deg F₀ ≤ d` and `deg G₀ < d` in total degree, at most `n choose (k + 1)` coefficient vectors
`α ∈ F^{k+1}` make `F₀ + L_α G₀` exceptional with agreement loss `q₀ᵏ⁻¹`. -/
theorem card_isReedMullerExceptional_add_mul_le [Fintype F] (f g : (Fin k → K₀) → F) {d A : ℕ}
    (F₀ G₀ : MvPolynomial (Fin k) F) (hF : F₀.totalDegree ≤ d) (hG : G₀.totalDegree < d) :
    #{α : Fin (k + 1) → F | IsReedMullerExceptional f g d A (Fintype.card K₀ ^ (k - 1)) α
      (F₀ + reedMullerMultiplier α * G₀)} ≤ (Fintype.card K₀ ^ k).choose (k + 1) := by
  set E : Finset (Fin (k + 1) → F) := {α : Fin (k + 1) → F | IsReedMullerExceptional f g d A
    (Fintype.card K₀ ^ (k - 1)) α (F₀ + reedMullerMultiplier α * G₀)}
  have hloss : ∀ α ∈ E, ∃ t ⊆ reedMullerAgreementLoss f g (reedMullerMultiplier α)
      (F₀ + reedMullerMultiplier α * G₀) F₀ G₀, #t = k + 1 ∧ ∀ σ : Fin (k + 1) → F,
        (∀ z ∈ t, σ 0 + ∑ i, σ i.succ * algebraMap K₀ F (z i) = 0) → σ = 0 := by
    intro α hα
    have h := (mem_filter.mp hα).2.2.2 F₀ G₀ hF hG
    exact exists_subset_card_eq_forall_add_sum_eq_zero _
      (by by_contra hlt; exact h ⟨rfl, by omega⟩)
  choose! t ht using hloss
  calc #E ≤ #(powersetCard (k + 1) (univ : Finset (Fin k → K₀))) := by
        refine card_le_card_of_injOn t (fun α hα ↦ ?_) (fun α hα α' hα' hαα' ↦ ?_)
        · simpa using (ht α hα).2.1
        have hmem : ∀ z ∈ t α, eval (gridPoint F z) (reedMullerMultiplier α) =
            eval (gridPoint F z) (reedMullerMultiplier α') := fun z hz ↦
          eval_reedMullerMultiplier_eq_of_mem_reedMullerAgreementLoss ((ht α hα).1 hz)
            ((ht α' hα').1 (hαα' ▸ hz))
        refine sub_eq_zero.mp ((ht α hα).2.2 (α - α') fun z hz ↦ ?_)
        have := hmem z hz
        simp only [eval_reedMullerMultiplier, gridPoint_apply] at this
        simp only [Pi.sub_apply, sub_mul, sum_sub_distrib]
        linear_combination this
    _ = (Fintype.card K₀ ^ k).choose (k + 1) := by simp

omit [DecidableEq F] in
/-- Let `G₀` be a rational function over `F` in `k` variables, and let `1 ≤ d`.
Suppose `G₀` is not a polynomial of total degree below `d`.
Then some vector `v ∈ F^{k+1}` has the following property.
Whenever `L_σ G₀` is a polynomial of total degree at most `d`, `σ` is a multiple of `v`. -/
theorem exists_forall_eq_smul_of_reedMullerMultiplier_mul_eq {d : ℕ} (hd : 1 ≤ d)
    (G₀ : FractionRing (MvPolynomial (Fin k) F))
    (hG : ¬ ∃ G₁ : MvPolynomial (Fin k) F,
      algebraMap _ (FractionRing (MvPolynomial (Fin k) F)) G₁ = G₀ ∧ G₁.totalDegree < d) :
    ∃ v : Fin (k + 1) → F, ∀ σ : Fin (k + 1) → F, ∀ H : MvPolynomial (Fin k) F,
      H.totalDegree ≤ d →
      algebraMap _ (FractionRing (MvPolynomial (Fin k) F)) (reedMullerMultiplier σ) * G₀ =
        algebraMap _ _ H → ∃ c : F, σ = c • v := by
  set ι := algebraMap (MvPolynomial (Fin k) F) (FractionRing (MvPolynomial (Fin k) F))
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have hL0 : ∀ σ : Fin (k + 1) → F, reedMullerMultiplier σ = 0 → σ = 0 := fun σ h ↦
    reedMullerMultiplier_injective (by rw [h, reedMullerMultiplier_zero])
  by_cases hpoly : ∃ G₁, ι G₁ = G₀
  · obtain ⟨G₁, rfl⟩ := hpoly
    have hdG : d ≤ G₁.totalDegree := by
      by_contra h
      exact hG ⟨G₁, rfl, by omega⟩
    have hG₁ : G₁ ≠ 0 := by
      rintro rfl
      simp at hdG
      omega
    refine ⟨Pi.single 0 1, fun σ H hH hσ ↦ ⟨σ 0, ?_⟩⟩
    rw [← map_mul] at hσ
    have hσ' := hι hσ
    by_cases hL : reedMullerMultiplier σ = 0
    · simp [hL0 σ hL]
    have hdeg := totalDegree_mul_of_isDomain hL hG₁
    rw [hσ'] at hdeg
    have hσ0 : (reedMullerMultiplier σ).totalDegree = 0 := by omega
    funext j
    refine Fin.cases (by simp) (fun i ↦ ?_) j
    simp [succ_eq_zero_of_totalDegree_reedMullerMultiplier_eq_zero hσ0 i, Fin.succ_ne_zero]
  by_cases hex : ∃ σ₁ H₁, σ₁ ≠ 0 ∧ ι (reedMullerMultiplier σ₁) * G₀ = ι H₁
  swap
  · refine ⟨0, fun σ H _ hσ ↦ ⟨0, ?_⟩⟩
    by_contra hne
    exact hex ⟨σ, H, by simpa using hne, hσ⟩
  obtain ⟨σ₁, H₁, hσ₁, h₁⟩ := hex
  have hL₁ : reedMullerMultiplier σ₁ ≠ 0 := fun h ↦ hσ₁ (hL0 σ₁ h)
  have hdeg₁ : (reedMullerMultiplier σ₁).totalDegree = 1 := by
    refine le_antisymm (totalDegree_reedMullerMultiplier_le σ₁) (Nat.one_le_iff_ne_zero.mpr ?_)
    intro h0
    set a := (reedMullerMultiplier σ₁).coeff 0
    have hLa : reedMullerMultiplier σ₁ = C a := totalDegree_eq_zero_iff_eq_C.mp h0
    have ha : a ≠ 0 := fun ha ↦ hL₁ (by rw [hLa, ha, map_zero])
    refine hpoly ⟨C a⁻¹ * H₁, ?_⟩
    rw [map_mul, ← h₁, hLa, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ ha, map_one,
      map_one, one_mul]
  have hirr : Irreducible (reedMullerMultiplier σ₁) := by
    refine irreducible_of_totalDegree_eq_one hdeg₁ fun x hx ↦ ?_
    obtain ⟨m, hm⟩ := ne_zero_iff.mp hL₁
    exact isUnit_iff_ne_zero.mpr fun h0 ↦ hm (zero_dvd_iff.mp (h0 ▸ hx m))
  have hprime := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  refine ⟨σ₁, fun τ H₂ _ h₂ ↦ ?_⟩
  have hrel : reedMullerMultiplier τ * H₁ = reedMullerMultiplier σ₁ * H₂ :=
    hι (by rw [map_mul, map_mul, ← h₁, ← h₂]; ring)
  rcases hprime.dvd_or_dvd ⟨H₂, hrel⟩ with ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · by_cases hτ : reedMullerMultiplier τ = 0
    · exact ⟨0, by simp [hL0 τ hτ]⟩
    have hQ0 : Q ≠ 0 := by
      rintro rfl
      exact hτ (by rw [hQ, mul_zero])
    have hdeg := totalDegree_mul_of_isDomain hL₁ hQ0
    rw [← hQ, hdeg₁] at hdeg
    have hQdeg : Q.totalDegree = 0 := by
      have := totalDegree_reedMullerMultiplier_le τ
      omega
    refine ⟨Q.coeff 0, reedMullerMultiplier_injective ?_⟩
    rw [reedMullerMultiplier_smul, hQ, totalDegree_eq_zero_iff_eq_C.mp hQdeg, mul_comm]
    simp
  · refine absurd ⟨Q, ?_⟩ hpoly
    have hne : ι (reedMullerMultiplier σ₁) ≠ 0 := (map_ne_zero_iff ι hι).mpr hL₁
    refine mul_left_cancel₀ hne ?_
    rw [← map_mul, ← hQ, h₁]

omit [DecidableEq F] in
open Classical in
/-- Let `F` be a finite field of size `q`, and let `1 ≤ d`.
Let `(F₀, G₀)` be rational functions over `F` in `k` variables.
Suppose they are not polynomials with `deg F₀ ≤ d` and `deg G₀ < d` in total degree.
Then at most `q` coefficient vectors `α ∈ F^{k+1}` make `F₀ + L_α G₀` a polynomial of total
degree at most `d`. -/
theorem card_reedMuller_fractionRing_combination_le [Fintype F] {d : ℕ} (hd : 1 ≤ d)
    (F₀ G₀ : FractionRing (MvPolynomial (Fin k) F))
    (h : ¬ ∃ F₁ G₁ : MvPolynomial (Fin k) F,
      algebraMap _ (FractionRing (MvPolynomial (Fin k) F)) F₁ = F₀ ∧
      algebraMap _ (FractionRing (MvPolynomial (Fin k) F)) G₁ = G₀ ∧
      F₁.totalDegree ≤ d ∧ G₁.totalDegree < d) :
    #{α : Fin (k + 1) → F | ∃ P : MvPolynomial (Fin k) F, P.totalDegree ≤ d ∧
      algebraMap _ (FractionRing (MvPolynomial (Fin k) F)) P =
        F₀ + algebraMap _ _ (reedMullerMultiplier α) * G₀} ≤ Fintype.card F := by
  set ι := algebraMap (MvPolynomial (Fin k) F) (FractionRing (MvPolynomial (Fin k) F))
  set S : Finset (Fin (k + 1) → F) := {α : Fin (k + 1) → F | ∃ P : MvPolynomial (Fin k) F,
    P.totalDegree ≤ d ∧ ι P = F₀ + ι (reedMullerMultiplier α) * G₀}
  obtain hS | ⟨α₀, hα₀⟩ := S.eq_empty_or_nonempty
  · simp [hS]
  obtain ⟨P₀, hP₀, hP₀eq⟩ := (mem_filter.mp hα₀).2
  have hG : ¬ ∃ G₁ : MvPolynomial (Fin k) F, ι G₁ = G₀ ∧ G₁.totalDegree < d := by
    rintro ⟨G₁, rfl, hG₁⟩
    refine h ⟨P₀ - reedMullerMultiplier α₀ * G₁, G₁, ?_, rfl, ?_, hG₁⟩
    · rw [map_sub, map_mul, hP₀eq]
      ring
    · refine (totalDegree_sub _ _).trans (max_le hP₀ ((totalDegree_mul _ _).trans ?_))
      have := totalDegree_reedMullerMultiplier_le α₀
      omega
  obtain ⟨v, hv⟩ := exists_forall_eq_smul_of_reedMullerMultiplier_mul_eq hd G₀ hG
  have hsub : S ⊆ univ.image fun c : F ↦ α₀ + c • v := by
    intro α hα
    obtain ⟨P, hP, hPeq⟩ := (mem_filter.mp hα).2
    obtain ⟨c, hc⟩ := hv (α - α₀) (P - P₀)
      ((totalDegree_sub _ _).trans (max_le hP hP₀))
      (by rw [reedMullerMultiplier_sub, map_sub, map_sub, hPeq, hP₀eq]; ring)
    exact mem_image.mpr ⟨c, mem_univ _, by rw [← hc]; abel⟩
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

open Classical in
/-- Let `K₀ ⊆ F` be finite fields of sizes `q₀` and `q`, let `n = q₀ᵏ`, and let `1 ≤ d`.
For any rational pair `(F₀, G₀)` over `F` in `k` variables, at most `max q (n choose (k + 1))`
coefficient vectors `α ∈ F^{k+1}` make `F₀ + L_α G₀` a polynomial that is exceptional with
agreement loss `q₀ᵏ⁻¹`. -/
theorem card_isReedMullerExceptional_fractionRing_le [Fintype F] (f g : (Fin k → K₀) → F)
    {d A : ℕ} (hd : 1 ≤ d) (F₀ G₀ : FractionRing (MvPolynomial (Fin k) F)) :
    #{α : Fin (k + 1) → F | ∃ P : MvPolynomial (Fin k) F,
        algebraMap _ (FractionRing (MvPolynomial (Fin k) F)) P =
          F₀ + algebraMap _ _ (reedMullerMultiplier α) * G₀ ∧
        IsReedMullerExceptional f g d A (Fintype.card K₀ ^ (k - 1)) α P} ≤
      max (Fintype.card F) ((Fintype.card K₀ ^ k).choose (k + 1)) := by
  set ι := algebraMap (MvPolynomial (Fin k) F) (FractionRing (MvPolynomial (Fin k) F))
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  by_cases h : ∃ F₁ G₁ : MvPolynomial (Fin k) F, ι F₁ = F₀ ∧ ι G₁ = G₀ ∧
      F₁.totalDegree ≤ d ∧ G₁.totalDegree < d
  · obtain ⟨F₁, G₁, rfl, rfl, hF, hG⟩ := h
    refine le_max_of_le_right ((card_le_card fun α hα ↦ ?_).trans
      (card_isReedMullerExceptional_add_mul_le f g (A := A) F₁ G₁ hF hG))
    obtain ⟨P, hP, hex⟩ := (mem_filter.mp hα).2
    rw [← map_mul, ← map_add, hι.eq_iff] at hP
    exact mem_filter.mpr ⟨mem_univ _, hP ▸ hex⟩
  · refine le_max_of_le_left ((card_le_card fun α hα ↦ ?_).trans
      (card_reedMuller_fractionRing_combination_le hd F₀ G₀ h))
    obtain ⟨P, hP, hex⟩ := (mem_filter.mp hα).2
    exact mem_filter.mpr ⟨mem_univ _, P, hex.1, hP⟩

end ReedSolomon
