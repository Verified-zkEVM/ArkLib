/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.Persistent
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.KernelDescent

/-!
# Persistence witnesses on a grid over the base field

Take `H` and `σ ≠ 0` over an extension field.
Suppose `H(x) = L_σ(x) v` at finitely many base-field points `x` of `Fᵏ`.
These identities are linear in the coefficients of `H` and in `σ`.
A kernel argument gives `H₀` and `σ₀ ≠ 0` over the base field with the same identities.
The total degree of `H₀` is at most that of `H`.

The multiplier `L_σ` may vanish at an agreement point.
If `σ` has a nonzero linear part, its zeros on the grid `K₀ᵏ` lie on a hyperplane.
That hyperplane holds at most `q₀ᵏ⁻¹` grid points, where `q₀ = |K₀|`.
Starting with `B + q₀ᵏ⁻¹` common agreements leaves at least `B` where the ratio is defined.
This proves persistence.

This is the case `c > B + n/q₀ - 1` of Claim 4.8 in Appendix A of [CWYZ26], with `n = q₀ᵏ`.
The paper picks a second triple over the base field.
As in the Reed–Solomon case, the descent replaces that choice.
Exponents `k - 1` use subtraction in `ℕ`.
The [paper page](../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main statements

* `ReedMuller.exists_affineRatioWitness_of_map`: the descent of a ratio along a field embedding.
* `ReedMuller.isAffinePersistent_of_commonAgreement`: persistence from a common agreement set.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedMuller

open MvPolynomial Finset Matrix

section AffineRatio

variable {K κ : Type*} [Field K] {k : ℕ}

/-- The coefficient matrix of `H(x_j) - L_σ(x_j) v_j`.

The unknowns are the coefficients of `H` on the monomials of `S`, and the vector `σ`. -/
private noncomputable def affineRatioMatrix (S : Finset (Fin k →₀ ℕ)) (pts : κ → Fin k → K)
    (vals : κ → K) : Matrix κ (S ⊕ Fin (k + 1)) K :=
  Matrix.of fun j ↦ Sum.elim (fun m ↦ eval (pts j) (monomial (m : Fin k →₀ ℕ) 1))
    fun i ↦ -((Fin.cons 1 (pts j) : Fin (k + 1) → K) i * vals j)

/-- The numerator `H` read off a coefficient vector. -/
private noncomputable def affineRatioNumerator {S : Finset (Fin k →₀ ℕ)}
    (c : S ⊕ Fin (k + 1) → K) : MvPolynomial (Fin k) K :=
  ∑ m : S, monomial (m : Fin k →₀ ℕ) (c (.inl m))

private theorem eval_affineMultiplier_eq_sum (σ : Fin (k + 1) → K) (x : Fin k → K) :
    eval x (affineMultiplier σ) = ∑ i, σ i * (Fin.cons 1 x : Fin (k + 1) → K) i := by
  simp [Fin.sum_univ_succ]

private theorem mulVec_affineRatioMatrix (S : Finset (Fin k →₀ ℕ)) (pts : κ → Fin k → K)
    (vals : κ → K) (c : S ⊕ Fin (k + 1) → K) (j : κ) :
    (affineRatioMatrix S pts vals *ᵥ c) j = eval (pts j) (affineRatioNumerator c) -
      eval (pts j) (affineMultiplier fun i ↦ c (.inr i)) * vals j := by
  simp only [affineRatioMatrix, affineRatioNumerator, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, of_apply, Sum.elim_inl, Sum.elim_inr, map_sum,
    eval_affineMultiplier_eq_sum, sum_mul]
  simp only [eval_monomial, one_mul, neg_mul, sum_neg_distrib, sub_eq_add_neg]
  congr 1
  · exact sum_congr rfl fun m _ ↦ mul_comm _ _
  · congr 1
    exact sum_congr rfl fun i _ ↦ by ring

private theorem map_affineRatioMatrix {E : Type*} [Field E] (φ : K →+* E)
    (S : Finset (Fin k →₀ ℕ)) (pts : κ → Fin k → K) (vals : κ → K) :
    (affineRatioMatrix S pts vals).map φ =
      affineRatioMatrix S (fun j ↦ φ ∘ pts j) (φ ∘ vals) := by
  ext j (m | i)
  · simp [affineRatioMatrix, eval_monomial]
  · refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp [affineRatioMatrix]

private theorem totalDegree_affineRatioNumerator_le {S : Finset (Fin k →₀ ℕ)} {d : ℕ}
    (hS : ∀ m ∈ S, m.degree ≤ d) (c : S ⊕ Fin (k + 1) → K) :
    (affineRatioNumerator c).totalDegree ≤ d :=
  (totalDegree_finsetSum_le fun m _ ↦ (totalDegree_monomial_le _ _).trans (hS m m.2))

private theorem affineRatioNumerator_coeff (H : MvPolynomial (Fin k) K) (v : Fin (k + 1) → K) :
    affineRatioNumerator (S := H.support) (Sum.elim (fun m ↦ H.coeff m) v) = H := by
  conv_rhs => rw [← support_sum_monomial_coeff H]
  rw [← sum_attach]
  simp [affineRatioNumerator]

end AffineRatio

variable {F : Type*} [Field F] {k : ℕ}

/-- Identities `H(x) = L_σ(x) v` at finitely many base-field points descend along `φ : F → E`.

Here `L_σ = σ₀ + σ₁ X₁ + ⋯ + σₖ Xₖ` with `σ ≠ 0`.

Each identity holds at the image under `φ` of a point of `Fᵏ` and a value in `F`.

The descended `H₀` over `F` has total degree at most that of `H`, and `σ₀ ∈ F^{k+1}` is nonzero.

The identities do not assert that `L_σ(x) ≠ 0` at every point. -/
theorem exists_affineRatioWitness_of_map {E : Type*} [Field E] (φ : F →+* E) {κ : Type*}
    [Finite κ] (pts : κ → Fin k → F) (vals : κ → F) {H : MvPolynomial (Fin k) E}
    {σ : Fin (k + 1) → E} (hσ : σ ≠ 0)
    (h : ∀ j, eval (φ ∘ pts j) H = eval (φ ∘ pts j) (affineMultiplier σ) * φ (vals j)) :
    ∃ H₀ : MvPolynomial (Fin k) F, ∃ σ₀ : Fin (k + 1) → F, σ₀ ≠ 0 ∧
      H₀.totalDegree ≤ H.totalDegree ∧
      ∀ j, eval (pts j) H₀ = eval (pts j) (affineMultiplier σ₀) * vals j := by
  -- The coefficients of `H` and the vector `σ` form a kernel vector of the mapped matrix.
  set c : H.support ⊕ Fin (k + 1) → E := Sum.elim (fun m ↦ H.coeff m) σ
  have hc : (affineRatioMatrix H.support pts vals).map φ *ᵥ c = 0 := by
    ext j
    rw [map_affineRatioMatrix, mulVec_affineRatioMatrix, affineRatioNumerator_coeff]
    simp [c, h j]
  -- A nonzero coordinate of `σ` descends.
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hσ
  obtain ⟨c', hc', hi'⟩ := exists_mulVec_eq_zero_apply_ne_zero_of_map φ _ hc (j := .inr i) hi
  refine ⟨affineRatioNumerator c', fun i ↦ c' (.inr i), Function.ne_iff.mpr ⟨i, hi'⟩,
    totalDegree_affineRatioNumerator_le (fun m hm ↦ ?_) c', fun j ↦ ?_⟩
  · exact le_totalDegree hm
  · have := congrFun hc' j
    rw [mulVec_affineRatioMatrix] at this
    exact sub_eq_zero.mp this

variable {K₀ : Type*} [Field K₀] [Fintype K₀] [DecidableEq F] [Algebra K₀ F]

/-- Let `K₀ ⊆ F` be finite fields, with `q₀ = |K₀|`.

Suppose `H = L_σ g` on a set `T` of at least `B + q₀ᵏ⁻¹` agreement points of `P` with `f + L_α g`.

Here `H` has total degree at most `d` and `L_σ = σ₀ + σ₁ X₁ + ⋯ + σₖ Xₖ` with `σ ≠ 0`.

Then `P` is persistent at threshold `B`.

At most `q₀ᵏ⁻¹` points of the grid `K₀ᵏ` are zeros of `L_σ`.

That leaves `B` points where the ratio is defined.

The exponent `k - 1` uses subtraction in `ℕ`. -/
theorem isAffinePersistent_of_commonAgreement (f g : (Fin k → K₀) → F) {d B : ℕ}
    {α σ : Fin (k + 1) → F} {P H : MvPolynomial (Fin k) F} (T : Finset (Fin k → K₀))
    (hT : B + Fintype.card K₀ ^ (k - 1) ≤ #T)
    (hagree : T ⊆ agreementSet (combinedWord f g (affineMultiplier α)) P) (hσ : σ ≠ 0)
    (hH : H.totalDegree ≤ d)
    (h : ∀ z ∈ T, eval (gridPoint F z) H = eval (gridPoint F z) (affineMultiplier σ) * g z) :
    IsAffinePersistent f g d B α P := by
  classical
  refine ⟨H, σ, hσ, hH, ?_⟩
  -- `L_σ` vanishes at most `q₀ᵏ⁻¹` times on the grid.
  have hroot : #{z ∈ T | eval (gridPoint F z) (affineMultiplier σ) = 0} ≤
      Fintype.card K₀ ^ (k - 1) := by
    by_cases htail : Fin.tail σ = 0
    · -- A nonzero constant multiplier has no zeros.
      have h0 : σ 0 ≠ 0 := fun h0 ↦ hσ (funext fun i ↦ Fin.cases h0 (congrFun htail) i)
      rw [filter_false_of_mem fun z _ ↦ ?_, card_empty]
      · exact Nat.zero_le _
      have := congrFun htail
      simp only [Fin.tail, Pi.zero_apply] at this
      simp [this, h0]
    · refine (card_le_card fun z hz ↦ ?_).trans
        (card_grid_inter_hyperplane_le (F := F) (Fin.tail σ) htail (-σ 0))
      simp only [mem_filter, eval_affineMultiplier, gridPoint_apply] at hz ⊢
      refine ⟨mem_univ _, ?_⟩
      simp only [dotProduct, Fin.tail, gridPoint_apply]
      linear_combination hz.2
  have hsub : {z ∈ T | ¬ eval (gridPoint F z) (affineMultiplier σ) = 0} ⊆
      affinePersistenceSet f g α P H σ := fun z hz ↦ by
    obtain ⟨hzT, hz0⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hagree hzT, hz0, h z hzT⟩
  have := card_filter_add_card_filter_not (s := T) fun z ↦
    eval (gridPoint F z) (affineMultiplier σ) = 0
  have := card_le_card hsub
  omega

end ReedMuller
