/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Persistent
public import ArkLib.ToMathlib.LinearAlgebra.Matrix.KernelDescent

/-!
# Persistence witnesses over the base field

Suppose polynomials over an extension field satisfy `H(x) = L(x) v` at finitely many
base-field points, with `deg H ≤ d`, `deg L ≤ 1`, and `L ≠ 0`.
These identities are linear in the coefficients, so a kernel argument gives polynomials over
the base field with the same bounds and identities.
The denominator may vanish at an agreement point.
Starting with `B + 1` common agreements leaves at least `B` where the ratio is defined,
which proves persistence.

The paper's Claim 4.8 chooses a second base-field triple in an affine space defined over
that field.
The chart proof instead constructs a second regular point over the algebraic closure and
uses coefficient descent to obtain base-field identities.
This lemma supports that difference in proof method.

## Main statements

* `ReedSolomon.exists_lineRatioWitness_of_map`: the descent of a ratio along a field embedding.
* `ReedSolomon.isAffinePersistent_of_commonAgreement`: persistence from a common agreement set.

## References

The persistence argument corresponds to Claim 4.8 of [CWYZ26], case `c > B`.

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset Matrix

section LineRatio

variable {K κ : Type*} [Field K]

/-- The coefficient matrix of `H(x_k) - L(x_k) v_k` in the coefficients of `H` and `L`. -/
private def lineRatioMatrix (pts vals : κ → K) (d : ℕ) : Matrix κ (Fin (d + 1) ⊕ Fin 2) K :=
  Matrix.of fun k ↦ Sum.elim (fun j ↦ pts k ^ (j : ℕ)) ![-vals k, -(pts k * vals k)]

/-- The numerator `H` read off a coefficient vector. -/
private noncomputable def lineRatioNumerator {d : ℕ} (c : Fin (d + 1) ⊕ Fin 2 → K) : K[X] :=
  ∑ j : Fin (d + 1), C (c (.inl j)) * X ^ (j : ℕ)

/-- The denominator `L` read off a coefficient vector. -/
private noncomputable def lineRatioDenominator {d : ℕ} (c : Fin (d + 1) ⊕ Fin 2 → K) : K[X] :=
  C (c (.inr 0)) + C (c (.inr 1)) * X

private theorem mulVec_lineRatioMatrix (pts vals : κ → K) {d : ℕ} (c : Fin (d + 1) ⊕ Fin 2 → K)
    (k : κ) : (lineRatioMatrix pts vals d *ᵥ c) k =
      (lineRatioNumerator c).eval (pts k) - (lineRatioDenominator c).eval (pts k) * vals k := by
  simp only [lineRatioMatrix, lineRatioNumerator, lineRatioDenominator, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, eval_finsetSum, Fin.sum_univ_two, of_apply, Sum.elim_inl, Sum.elim_inr,
    eval_add, eval_mul, eval_C, eval_X, eval_pow, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_comm (pts k ^ _)]
  ring

private theorem map_lineRatioMatrix {E : Type*} [Field E] (φ : K →+* E) (pts vals : κ → K)
    (d : ℕ) : (lineRatioMatrix pts vals d).map φ = lineRatioMatrix (φ ∘ pts) (φ ∘ vals) d := by
  ext k (j | j)
  · simp [lineRatioMatrix]
  · fin_cases j <;> simp [lineRatioMatrix]

private theorem degree_lineRatioNumerator_le {d : ℕ} (c : Fin (d + 1) ⊕ Fin 2 → K) :
    (lineRatioNumerator c).degree ≤ d :=
  Order.le_of_lt_succ (by exact_mod_cast degree_sum_fin_lt (fun j : Fin (d + 1) ↦ c (.inl j)))

private theorem degree_lineRatioDenominator_le {d : ℕ} (c : Fin (d + 1) ⊕ Fin 2 → K) :
    (lineRatioDenominator c).degree ≤ 1 := by
  rw [lineRatioDenominator, add_comm]
  exact degree_linear_le

private theorem lineRatioDenominator_ne_zero {d : ℕ} {c : Fin (d + 1) ⊕ Fin 2 → K}
    (hc : c (.inr 0) ≠ 0 ∨ c (.inr 1) ≠ 0) : lineRatioDenominator c ≠ 0 := by
  intro h
  have h0 := congrArg (coeff · 0) h
  have h1 := congrArg (coeff · 1) h
  simp [lineRatioDenominator] at h0 h1
  tauto

private theorem lineRatioNumerator_coeff {d : ℕ} {H : K[X]} (hH : H.degree ≤ d) (v : Fin 2 → K) :
    lineRatioNumerator (d := d) (Sum.elim (fun j ↦ H.coeff j) v) = H := by
  conv_rhs => rw [H.as_sum_range' (d + 1) (Nat.lt_succ_of_le (natDegree_le_of_degree_le hH))]
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ monomial j (H.coeff j))]
  simp [lineRatioNumerator, C_mul_X_pow_eq_monomial]

private theorem lineRatioDenominator_coeff {d : ℕ} {L : K[X]} (hL : L.degree ≤ 1)
    (u : Fin (d + 1) → K) : lineRatioDenominator (Sum.elim u ![L.coeff 0, L.coeff 1]) = L := by
  rw [eq_X_add_C_of_degree_le_one hL]
  simp [lineRatioDenominator, add_comm]

end LineRatio

variable {F : Type*} [Field F]

/-- Identities `H(x) = L(x) v` at finitely many base-field points descend along a field embedding.

The descended polynomials satisfy `deg H ≤ d`, `L ≠ 0`, and `deg L ≤ 1`.
The identities do not assert that `L(x) ≠ 0` at every point. -/
theorem exists_lineRatioWitness_of_map {E : Type*} [Field E] (φ : F →+* E) {κ : Type*}
    [Finite κ] (pts vals : κ → F) (d : ℕ) {H L : E[X]} (hL : L ≠ 0) (hL1 : L.degree ≤ 1)
    (hH : H.degree ≤ d) (h : ∀ k, H.eval (φ (pts k)) = L.eval (φ (pts k)) * φ (vals k)) :
    ∃ H₀ L₀ : F[X], L₀ ≠ 0 ∧ L₀.degree ≤ 1 ∧ H₀.degree ≤ d ∧
      ∀ k, H₀.eval (pts k) = L₀.eval (pts k) * vals k := by
  -- The coefficients of `H` and `L` form a kernel vector of the mapped matrix.
  set c : Fin (d + 1) ⊕ Fin 2 → E := Sum.elim (fun j ↦ H.coeff j) ![L.coeff 0, L.coeff 1]
  have hc : (lineRatioMatrix pts vals d).map φ *ᵥ c = 0 := by
    ext k
    rw [map_lineRatioMatrix, mulVec_lineRatioMatrix, lineRatioNumerator_coeff hH,
      lineRatioDenominator_coeff hL1]
    simp [h k]
  -- One of the two coefficients of `L` is nonzero, and that coordinate descends.
  have hne : ∃ j : Fin 2, c (.inr j) ≠ 0 := by
    by_contra! hz
    have h0 := hz 0
    have h1 := hz 1
    simp only [c, Sum.elim_inr] at h0 h1
    apply hL
    rw [← lineRatioDenominator_coeff hL1 (d := d) fun j ↦ H.coeff j]
    simp [lineRatioDenominator, h0, h1]
  obtain ⟨j, hj⟩ := hne
  obtain ⟨c', hc', hj'⟩ := exists_mulVec_eq_zero_apply_ne_zero_of_map φ _ hc hj
  refine ⟨lineRatioNumerator c', lineRatioDenominator c',
    lineRatioDenominator_ne_zero ?_, degree_lineRatioDenominator_le c',
    degree_lineRatioNumerator_le c', fun k ↦ ?_⟩
  · fin_cases j
    exacts [Or.inl hj', Or.inr hj']
  · have := congrFun hc' k
    rw [mulVec_lineRatioMatrix] at this
    exact sub_eq_zero.mp this

variable [DecidableEq F] {ι : Type*} [Fintype ι]

/-- If `H = L g` on at least `B + 1` candidate agreement points, then `P` is persistent at `B`.

The bounds are `deg H ≤ d`, `deg L ≤ 1`, and `L ≠ 0`.
At most one of these points is a root of `L`, leaving at least `B` where the ratio is defined. -/
theorem isAffinePersistent_of_commonAgreement (domain : ι ↪ F) (f g : ι → F) {d B : ℕ}
    {α β : F} {P H L : F[X]} (T : Finset ι)
    (hT : B + 1 ≤ T.card) (hagree : T ⊆ polynomialAgreementSet domain
      (combinedWord domain f g (affineMultiplier α β)) P)
    (hL : L ≠ 0) (hL1 : L.degree ≤ 1) (hH : H.degree ≤ d)
    (h : ∀ i ∈ T, H.eval (domain i) = L.eval (domain i) * g i) :
    IsAffinePersistent domain f g d B α β P := by
  refine ⟨H, L, hL, hL1, hH, ?_⟩
  -- `L` vanishes at most once on `T`.
  have hroot : #{i ∈ T | L.eval (domain i) = 0} ≤ 1 :=
    (card_le_natDegree_of_injOn_of_eval_eq_zero hL domain.injective.injOn
      fun i hi ↦ (mem_filter.mp hi).2).trans (natDegree_le_of_degree_le hL1)
  have hsub : {i ∈ T | ¬ L.eval (domain i) = 0} ⊆
      affinePersistenceSet domain f g α β P H L := fun i hi ↦ by
    obtain ⟨hiT, hi0⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hagree hiT, hi0, h i hiT⟩
  have := card_filter_add_card_filter_not (s := T) fun i ↦ L.eval (domain i) = 0
  have := card_le_card hsub
  omega

end ReedSolomon
