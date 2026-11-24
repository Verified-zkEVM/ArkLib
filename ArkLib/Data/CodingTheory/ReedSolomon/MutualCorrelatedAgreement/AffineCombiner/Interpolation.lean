/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LineEvaluation
public import ArkLib.Data.MvPolynomial.WeightedDegree
public import ArkLib.Data.Polynomial.SymbolicInterpolationSupport
public import ArkLib.ToMathlib.Polynomial.RootMultiplicity
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Trivariate interpolation along multiplier curves

A nonzero `Q(X, Y, Z)` of `(1, e, d)`-weighted degree below `m A` is built to vanish
to order `m` along each line `(z, Y, f(z) + Y g(z))` indexed by a domain point `z`.
Let `L` be a multiplier of degree at most `e`.
Then `Q(X, L(X), P(X)) = 0` for every candidate `P` of degree at most `d` that agrees with
`f + L g` on at least `A` domain points.
Such an interpolant exists when its coefficient space has greater dimension than the
space of linear constraints.

Reed–Solomon codes use `e = 1`, where the multipliers are the lines `α + β X`.
On the grid `𝔽_{q₀}^k` of `n = q₀^k` points, Reed–Muller codes use `e = n / q₀ = q₀^(k-1)`.

## Main definitions

* `ReedSolomon.IsMultiplierInterpolant`: the interpolation conditions.

## Main statements

* `ReedSolomon.exists_isMultiplierInterpolant`: an interpolant exists under the surplus
  condition.
* `ReedSolomon.exists_isAffineInterpolant`: the case `e = 1`.
* `ReedSolomon.IsMultiplierInterpolant.vanish_affineMultiplier`: at `e = 1` the interpolant
  vanishes along every agreeing line `α + β X`.
* `ReedSolomon.multiplierEval_eq_aeval_affineShift`: the evaluation factors through a shift.

* `ReedSolomon.exists_isMultiplierInterpolant_degreeOf_none_pos`: positive `Z`-degree when
  `A ≤ n`.

## References

The interpolation is Lemma 4.2 of [CWYZ26].
Appendix A of [CWYZ26] uses it with the weight `(1, n / q₀, ρ n)`.

The positive `Z`-degree conclusion uses `A ≤ n`.
The factor count treats content free of `Z` separately.

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Polynomial.SymbolicInterpolation

section Exponent

/-- The exponent `Z^j X^i Y^t` of an index `⟨j, (i, t)⟩`. -/
noncomputable def affineExponent (k : Σ _ : ℕ, ℕ × ℕ) : AffineVar →₀ ℕ :=
  Finsupp.single none k.1 + Finsupp.single (some 0) k.2.1 + Finsupp.single (some 1) k.2.2

/-- The `Z`-exponent. -/
@[simp] theorem affineExponent_none (k : Σ _ : ℕ, ℕ × ℕ) : affineExponent k none = k.1 := by
  simp [affineExponent]

/-- The `X`-exponent. -/
@[simp] theorem affineExponent_x (k : Σ _ : ℕ, ℕ × ℕ) : affineExponent k (some 0) = k.2.1 := by
  simp [affineExponent]

/-- The `Y`-exponent. -/
@[simp] theorem affineExponent_y (k : Σ _ : ℕ, ℕ × ℕ) : affineExponent k (some 1) = k.2.2 := by
  simp [affineExponent]

/-- Every exponent is the exponent of its three coordinates. -/
theorem affineExponent_coords (e : AffineVar →₀ ℕ) :
    affineExponent ⟨e none, (e (some 0), e (some 1))⟩ = e := by
  ext v
  rcases v with _ | ⟨i⟩
  · simp
  · fin_cases i <;> simp

/-- Distinct indices give distinct exponents. -/
theorem affineExponent_injective : Function.Injective affineExponent := by
  rintro ⟨j, i, t⟩ ⟨j', i', t'⟩ h
  have h1 := congrArg (· none) h
  have h2 := congrArg (· (some 0)) h
  have h3 := congrArg (· (some 1)) h
  simp only [affineExponent_none, affineExponent_x, affineExponent_y] at h1 h2 h3
  subst h1 h2 h3
  rfl

end Exponent

section Shift

variable {K : Type*} [Field K]

/-- The shift `Z ↦ u + Y v + Z`, `X ↦ x + X`, `Y ↦ Y`, moving the point `(x, u + Y v)` to `0`. -/
noncomputable def affineShift (x u v : K) :
    MvPolynomial AffineVar K →ₐ[K] MvPolynomial AffineVar K :=
  MvPolynomial.aeval fun w ↦ w.elim
    (MvPolynomial.C u + MvPolynomial.X (some 1) * MvPolynomial.C v + MvPolynomial.X none)
    ![MvPolynomial.C x + MvPolynomial.X (some 0), MvPolynomial.X (some 1)]

/-- The shift does not raise the `(Y, Z)`-degree. -/
theorem weightedTotalDegree_affineShift_le (x u v : K) (Q : MvPolynomial AffineVar K) :
    (affineShift x u v Q).weightedTotalDegree affineYZWeight ≤
      Q.weightedTotalDegree affineYZWeight := by
  refine MvPolynomial.weightedTotalDegree_aeval_le_of_le _ _ _ _ fun w ↦ ?_
  rw [← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
  rcases w with _ | ⟨i⟩
  · refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact MvPolynomial.C_mem_restrictWeightedDegree _ _ _
    · simpa using MvPolynomial.mul_mem_restrictWeightedDegree
        (MvPolynomial.X_mem_restrictWeightedDegree affineYZWeight 1 (some 1) le_rfl)
        (MvPolynomial.C_mem_restrictWeightedDegree affineYZWeight 0 v)
    · exact MvPolynomial.X_mem_restrictWeightedDegree _ _ _ le_rfl
  · fin_cases i
    · refine Submodule.add_mem _ ?_ ?_
      · exact MvPolynomial.C_mem_restrictWeightedDegree _ _ _
      · exact MvPolynomial.X_mem_restrictWeightedDegree _ _ _ le_rfl
    · exact MvPolynomial.X_mem_restrictWeightedDegree _ _ _ le_rfl

/-- The evaluation along a multiplier factors through the shift. -/
theorem multiplierEval_eq_aeval_affineShift (L P : K[X]) (x u v : K)
    (Q : MvPolynomial AffineVar K) :
    multiplierEval L P Q = MvPolynomial.aeval (fun w ↦ w.elim
      (P - C u - L * C v) ![X - C x, L]) (affineShift x u v Q) := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun w ↦ ?_
  rcases w with _ | ⟨i⟩
  · simp [affineShift, multiplierEval]
  · fin_cases i <;> simp [affineShift, multiplierEval]

/-- Let `R` have coefficients in `A`, and let `ψ` send the variables into an `A`-algebra `B`.

Let `p` divide the images of `Z` and `X`.

If every monomial of `R` has degree at least `m` in `Z, X`, then `p ^ m` divides the image. -/
theorem pow_dvd_aeval_of_affineWeight_le {A B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] {ψ : AffineVar → B} {p : B} {m : ℕ}
    (hz : p ∣ ψ none) (hx : p ∣ ψ (some 0)) {R : MvPolynomial AffineVar A}
    (hR : ∀ e ∈ R.support, m ≤ e none + e (some 0)) :
    p ^ m ∣ MvPolynomial.aeval ψ R := by
  classical
  conv_rhs => rw [R.as_sum, map_sum]
  refine Finset.dvd_sum fun e he ↦ ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fintype.prod_option, Fin.prod_univ_two]
  refine Dvd.dvd.mul_left ?_ _
  refine (pow_dvd_pow p (hR e he)).trans ?_
  rw [pow_add, ← mul_assoc]
  exact Dvd.dvd.mul_right (mul_dvd_mul (pow_dvd_pow_of_dvd hz _) (pow_dvd_pow_of_dvd hx _)) _

end Shift

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- A nonzero `Q` of bounded degrees that vanishes along multipliers with agreeing candidates.

The multipliers have degree at most `e`.

No positive lower bound on the `Z`-degree is required.
The candidate has degree `≤ d` and agrees with the combined word on at least `A` points. -/
structure IsMultiplierInterpolant (domain : ι ↪ F) (f g : ι → F) (e d A m D M : ℕ)
    (Q : MvPolynomial AffineVar F) : Prop where
  /-- The interpolant is nonzero. -/
  ne_zero : Q ≠ 0
  /-- The `(1, e, d)`-weighted degree is below `m A`. -/
  multiplierWeight_lt : Q.weightedTotalDegree (multiplierWeight e d) < m * A
  /-- The joint degree in `Y` and `Z` is at most `D`. -/
  yzDegree_le : Q.weightedTotalDegree affineYZWeight ≤ D
  /-- The degree in `Z` is at most `M`. -/
  rootDegree_le : Q.degreeOf none ≤ M
  /-- The interpolant vanishes along each multiplier `L` of degree `≤ e` with agreeing `P`. -/
  vanish : ∀ L P : F[X], L.natDegree ≤ e → P.degree ≤ d →
    A ≤ (polynomialAgreementSet domain (combinedWord domain f g L) P).card →
    multiplierEval L P Q = 0

/-- With `e = 1`, the interpolant vanishes along every line `α + β X` with an agreeing candidate.

The candidate has degree `≤ d` and agrees with the combined word on at least `A` points. -/
theorem IsMultiplierInterpolant.vanish_affineMultiplier {domain : ι ↪ F} {f g : ι → F}
    {d A m D M : ℕ} {Q : MvPolynomial AffineVar F}
    (hQ : IsMultiplierInterpolant domain f g 1 d A m D M Q) (α β : F) (P : F[X])
    (hP : P.degree ≤ d)
    (hA : A ≤ (polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β))
      P).card) :
    multiplierEval (affineMultiplier α β) P Q = 0 :=
  hQ.vanish _ P (natDegree_affineMultiplier_le α β) hP hA

open Polynomial.SymbolicInterpolation in
omit [DecidableEq F] in
/-- A nonzero kernel element has the required degrees and multiplicities. -/
private theorem exists_affineShift_support_le (domain : ι ↪ F) (f g : ι → F) {e d A m D M : ℕ}
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * A - e * D) (M + 1) (D + 1)).card) :
    ∃ Q : MvPolynomial AffineVar F, Q ≠ 0 ∧
      Q.weightedTotalDegree (multiplierWeight e d) < m * A ∧
      Q.weightedTotalDegree affineYZWeight ≤ D ∧ Q.degreeOf none ≤ M ∧
      ∀ i, ∀ w ∈ (affineShift (domain i) (f i) (g i) Q).support, m ≤ w none + w (some 0) := by
  classical
  -- The unknowns are the coefficients on the monomial support.
  let S := monomialSupport d (m * A - e * D) (M + 1) (D + 1)
  let T := constraintSupport m (D + 1)
  let embed : (S → F) →ₗ[F] MvPolynomial AffineVar F :=
    Fintype.linearCombination F fun k : S ↦ MvPolynomial.monomial (affineExponent k.1) 1
  -- One constraint per point and per low coefficient of the shifted polynomial.
  let cons : (S → F) →ₗ[F] (ι × T → F) := LinearMap.pi fun p : ι × T ↦
    MvPolynomial.lcoeff F (affineExponent p.2.1) ∘ₗ
      (affineShift (domain p.1) (f p.1) (g p.1)).toLinearMap ∘ₗ embed
  have hker : LinearMap.ker cons ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    simpa [Module.finrank_fintype_fun_eq_card, S, T] using hsurplus
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set Q := embed c with hQ
  have hcoeff : ∀ e, Q.coeff e = ∑ k : S, c k * if affineExponent k.1 = e then 1 else 0 := by
    intro e
    simp [Q, embed, Fintype.linearCombination_apply, MvPolynomial.coeff_monomial]
  -- Every monomial of `Q` comes from the support.
  have hsupp : ∀ e ∈ Q.support, ∃ k ∈ S, affineExponent k = e := by
    intro e he
    rw [MvPolynomial.mem_support_iff, hcoeff] at he
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    by_cases hke : affineExponent k.1 = e
    · exact ⟨k.1, k.2, hke⟩
    · simp [hke] at hk
  have hQ0 : Q ≠ 0 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hc0
    intro h0
    have := hcoeff (affineExponent k.1)
    simp only [h0, affineExponent_injective.eq_iff, ← Subtype.ext_iff, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    exact hk (by simpa using this.symm)
  have hyz : Q.weightedTotalDegree affineYZWeight ≤ D := by
    rw [← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le,
      MvPolynomial.mem_restrictWeightedDegree]
    intro e he
    obtain ⟨⟨j, i, t⟩, hk, rfl⟩ := hsupp e he
    simp only [S, mem_monomialSupport] at hk
    simp only [weight_affineVar, affineExponent_none, affineExponent_x, affineExponent_y,
      affineYZWeight_none, affineYZWeight_X, affineYZWeight_Y]
    omega
  have hline : ∀ w ∈ Q.support, Finsupp.weight (multiplierWeight e d) w < m * A := by
    intro w hw
    obtain ⟨⟨j, i, t⟩, hk, rfl⟩ := hsupp w hw
    simp only [S, mem_monomialSupport] at hk
    simp only [weight_affineVar, affineExponent_none, affineExponent_x, affineExponent_y,
      multiplierWeight_none, multiplierWeight_X, multiplierWeight_Y]
    have het : t * e ≤ e * D := by rw [mul_comm]; exact Nat.mul_le_mul_left e (by omega)
    rw [mul_comm j d]
    omega
  have hlt : Q.weightedTotalDegree (multiplierWeight e d) < m * A := by
    obtain ⟨e, he⟩ : Q.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (by rwa [Ne, MvPolynomial.support_eq_empty])
    rw [MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff (by
      exact (Nat.zero_le _).trans_lt (hline e he))]
    exact hline
  refine ⟨Q, hQ0, hlt, hyz, ?_, fun i w hw ↦ ?_⟩
  · refine MvPolynomial.degreeOf_le_iff.mpr fun e he ↦ ?_
    obtain ⟨⟨j, i, t⟩, hk, rfl⟩ := hsupp e he
    simp only [S, mem_monomialSupport] at hk
    rw [affineExponent_none]
    exact Nat.lt_succ_iff.mp hk.1
  by_contra hlow
  push Not at hlow
  have hwt := (MvPolynomial.le_weightedTotalDegree affineYZWeight hw).trans
    ((weightedTotalDegree_affineShift_le _ _ _ Q).trans hyz)
  simp only [weight_affineVar, affineYZWeight_none, affineYZWeight_X,
    affineYZWeight_Y] at hwt
  have hT : (⟨w none, (w (some 0), w (some 1))⟩ : Σ _ : ℕ, ℕ × ℕ) ∈ T := by
    simp only [T, mem_constraintSupport]
    omega
  have h0 := congrFun (LinearMap.mem_ker.mp hc) (i, ⟨_, hT⟩)
  simp only [cons, LinearMap.pi_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.lcoeff_apply, affineExponent_coords, Pi.zero_apply] at h0
  exact (MvPolynomial.mem_support_iff.mp hw) h0


/-- Multiplicity along the received lines gives vanishing on an agreeing candidate. -/
private theorem multiplierEval_eq_zero_of_affineShift_support_le (domain : ι ↪ F)
    (f g : ι → F) {e d A m : ℕ} {Q : MvPolynomial AffineVar F}
    (hlt : Q.weightedTotalDegree (multiplierWeight e d) < m * A)
    (hmult : ∀ i, ∀ w ∈ (affineShift (domain i) (f i) (g i) Q).support,
      m ≤ w none + w (some 0))
    (L P : F[X]) (hL : L.natDegree ≤ e) (hP : P.degree ≤ d)
    (hA : A ≤ (polynomialAgreementSet domain (combinedWord domain f g L) P).card) :
    multiplierEval L P Q = 0 := by
  refine eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn (fun i ↦ domain i) _ m A
    domain.injective.injOn hA (fun i hi ↦ ?_)
    ((natDegree_multiplierEval_le hL (natDegree_le_of_degree_le hP) Q).trans_lt hlt)
  rw [multiplierEval_eq_aeval_affineShift L P (domain i) (f i) (g i)]
  refine pow_dvd_aeval_of_affineWeight_le (p := X - C (domain i)) ?_ (by simp) (hmult i)
  rw [mem_polynomialAgreementSet, combinedWord] at hi
  rw [Option.elim_none, dvd_iff_isRoot]
  simp [hi]

omit [DecidableEq F] in
/-- Let `Q` be nonzero with line weight below `m A`, where `A ≤ n` and `n` is the domain size.

If `Q` vanishes to order `m` along every line `(z, Y, f(z) + Y g(z))`, then `Q` involves `Z`.

Otherwise `Q` is a polynomial in `X` over `F[Y]` with `n` roots of multiplicity `m`. -/
private theorem degreeOf_none_pos_of_affineShift_support_le (domain : ι ↪ F) (f g : ι → F)
    {e d A m : ℕ} (hAn : A ≤ Fintype.card ι) {Q : MvPolynomial AffineVar F} (hQ : Q ≠ 0)
    (hlt : Q.weightedTotalDegree (multiplierWeight e d) < m * A)
    (hmult : ∀ i, ∀ e ∈ (affineShift (domain i) (f i) (g i) Q).support,
      m ≤ e none + e (some 0)) :
    0 < Q.degreeOf none := by
  by_contra h0
  -- `Q` is free of `Z`, so it is a polynomial `Q₀` in `X` and `Y`.
  obtain ⟨Q₀, rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q some
    (Option.some_injective _) fun w hw ↦ by
      rcases w with _ | w
      · exact absurd (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hw) (by omega)
      · exact ⟨w, rfl⟩
  -- View `Q₀` as a polynomial in `X` over the domain `F[X, Y]`.
  let χ : Fin 2 → (MvPolynomial (Fin 2) F)[X] := ![X, C (MvPolynomial.X 1)]
  set W := MvPolynomial.aeval χ Q₀ with hW
  have hW0 : W = 0 := by
    refine eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn
      (fun i ↦ MvPolynomial.C (domain i)) Finset.univ m A ?_ (by simpa using hAn) ?_ ?_
    · exact fun i _ j _ h ↦ domain.injective (MvPolynomial.C_injective _ _ h)
    · -- The shift to `(z, f(z) + Y g(z))` turns the order-`m` vanishing into `(X - z)^m ∣ W`.
      intro i _
      have hshift : MvPolynomial.aeval (fun w : AffineVar ↦ w.elim 0
          ![X - C (MvPolynomial.C (domain i)), C (MvPolynomial.X 1)])
          (affineShift (domain i) (f i) (g i) (MvPolynomial.rename some Q₀)) = W := by
        rw [affineShift, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, MvPolynomial.aeval_rename,
          hW]
        congr 2
        funext j
        fin_cases j <;> simp [χ]
      rw [← hshift]
      exact pow_dvd_aeval_of_affineWeight_le (by simp) (by simp) (hmult i)
    · have hψ : W = MvPolynomial.aeval (fun w : AffineVar ↦ w.elim 0 χ)
          (MvPolynomial.rename some Q₀) := by
        rw [MvPolynomial.aeval_rename]
        rfl
      rw [hψ, ← MvPolynomial.aeval_map_algebraMap (MvPolynomial (Fin 2) F)]
      refine lt_of_le_of_lt ?_ hlt
      refine (MvPolynomial.natDegree_aeval_le_weightedTotalDegree_of_le (multiplierWeight e d) _ _
        fun w ↦ ?_).trans (Finset.sup_mono (MvPolynomial.support_map_subset _ _))
      rcases w with _ | ⟨j⟩
      · simp
      · fin_cases j <;> simp [χ]
  -- Evaluating `X` at the variable `X` of the coefficient ring recovers `Q₀`.
  have hQ₀ : Q₀ = 0 := by
    have := congrArg
      ((Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) F)).restrictScalars F) hW0
    rw [hW, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, map_zero,
      show (fun j ↦ _) = (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) F) from
        funext fun j ↦ by fin_cases j <;> simp [χ], MvPolynomial.aeval_X_left_apply] at this
    exact this
  exact hQ (by rw [hQ₀, map_zero])

open Polynomial.SymbolicInterpolation in
/-- An interpolant exists when its allowed monomials outnumber the linear constraints.

The monomials are `Z^j X^i Y^t` with `j ≤ M`, `j + t ≤ D`, and `i + d j < m A - e D`.
The bound `m A - e D` uses natural-number subtraction, so the support is empty when `e D ≥ m A`.
At each domain point, constraints have indices `(s, r, t)` with `s + r < m` and `s + t ≤ D`.
Their number is `∑_{s < m} (m - s)(D + 1 - s)`, with natural-number subtraction.
No positive lower bound on the resulting `Z`-degree is asserted. -/
theorem exists_isMultiplierInterpolant (domain : ι ↪ F) (f g : ι → F) {e d A m D M : ℕ}
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * A - e * D) (M + 1) (D + 1)).card) :
    ∃ Q, IsMultiplierInterpolant domain f g e d A m D M Q := by
  obtain ⟨Q, hQ0, hlt, hyz, hM, hmult⟩ := exists_affineShift_support_le domain f g hsurplus
  exact ⟨Q, hQ0, hlt, hyz, hM,
    multiplierEval_eq_zero_of_affineShift_support_le domain f g hlt hmult⟩

open Polynomial.SymbolicInterpolation in
/-- If the threshold is at most the domain size, the constructed interpolant involves `Z`. -/
theorem exists_isMultiplierInterpolant_degreeOf_none_pos (domain : ι ↪ F) (f g : ι → F)
    {e d A m D M : ℕ} (hAn : A ≤ Fintype.card ι)
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * A - e * D) (M + 1) (D + 1)).card) :
    ∃ Q, IsMultiplierInterpolant domain f g e d A m D M Q ∧ 0 < Q.degreeOf none := by
  obtain ⟨Q, hQ0, hlt, hyz, hM, hmult⟩ := exists_affineShift_support_le domain f g hsurplus
  exact ⟨Q, ⟨hQ0, hlt, hyz, hM, multiplierEval_eq_zero_of_affineShift_support_le domain f g hlt
    hmult⟩, degreeOf_none_pos_of_affineShift_support_le domain f g hAn hQ0 hlt hmult⟩

open Polynomial.SymbolicInterpolation in
/-- An interpolant for the lines `α + β X` exists when its monomials outnumber the constraints.

The monomials are `Z^j X^i Y^t` with `j ≤ M`, `j + t ≤ D`, and `i + d j < m A - D`.
At each domain point, constraints have indices `(s, r, t)` with `s + r < m` and `s + t ≤ D`.
Their number is `∑_{s < m} (m - s)(D + 1 - s)`, with natural-number subtraction. -/
theorem exists_isAffineInterpolant (domain : ι ↪ F) (f g : ι → F) {d A m D M : ℕ}
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * A - D) (M + 1) (D + 1)).card) :
    ∃ Q, IsMultiplierInterpolant domain f g 1 d A m D M Q :=
  exists_isMultiplierInterpolant domain f g (by rwa [one_mul])

end ReedSolomon
