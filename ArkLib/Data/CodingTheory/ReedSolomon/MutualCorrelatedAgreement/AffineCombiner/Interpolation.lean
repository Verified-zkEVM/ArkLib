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
# Trivariate interpolation along affine lines

A nonzero `Q(X, Y, Z)` of `(1, 1, d)`-weighted degree below `m A` is built to vanish
to order `m` along each line `(z, Y, f(z) + Y g(z))` indexed by a domain point `z`.
Consequently, `Q(X, α + β X, P(X)) = 0` for every candidate of degree at most `d` that
agrees with `f + (α + β X) g` on at least `A` domain points.
Such an interpolant exists when its coefficient space has greater dimension than the
space of linear constraints.

## Main definitions

* `ReedSolomon.IsAffineInterpolant`: the interpolation conditions.

## Main statements

* `ReedSolomon.exists_isAffineInterpolant`: an interpolant exists under the surplus condition.

## References

The interpolation is Lemma 4.2 of [CWYZ26].

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

/-- The weight of an exponent in the three variables. -/
theorem weight_affineVar (w : AffineVar → ℕ) (e : AffineVar →₀ ℕ) :
    Finsupp.weight w e = e none * w none + e (some 0) * w (some 0) + e (some 1) * w (some 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_option, Fin.sum_univ_two, add_assoc]

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

/-- The line evaluation factors through the shift. -/
theorem affineLineEval_eq_aeval_affineShift (α β : K) (P : K[X]) (x u v : K)
    (Q : MvPolynomial AffineVar K) :
    affineLineEval α β P Q = MvPolynomial.aeval (fun w ↦ w.elim
      (P - C u - affineMultiplier α β * C v) ![X - C x, affineMultiplier α β])
      (affineShift x u v Q) := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun w ↦ ?_
  rcases w with _ | ⟨i⟩
  · simp [affineShift]
  · fin_cases i <;> simp [affineShift]

/-- Let `p` divide the images of `Z` and `X`.

If every monomial has degree at least `m` in `Z, X`, then `p ^ m` divides the image. -/
theorem pow_dvd_aeval_of_le {ψ : AffineVar → K[X]} {p : K[X]} {m : ℕ}
    (hz : p ∣ ψ none) (hx : p ∣ ψ (some 0)) {R : MvPolynomial AffineVar K}
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

/-- A nonzero `Q` of bounded degrees that vanishes along every line with an agreeing candidate.

The candidate has degree `≤ d` and agrees with the combined word on at least `A` points. -/
structure IsAffineInterpolant (domain : ι ↪ F) (f g : ι → F) (d A m D M : ℕ)
    (Q : MvPolynomial AffineVar F) : Prop where
  /-- The interpolant is nonzero. -/
  ne_zero : Q ≠ 0
  /-- The `(1, 1, d)`-weighted degree is below `m A`. -/
  lineWeight_lt : Q.weightedTotalDegree (affineLineWeight d) < m * A
  /-- The joint degree in `Y` and `Z` is at most `D`. -/
  yzDegree_le : Q.weightedTotalDegree affineYZWeight ≤ D
  /-- The degree in `Z` is at most `M`. -/
  rootDegree_le : Q.degreeOf none ≤ M
  /-- The interpolant vanishes along every line with an agreeing candidate. -/
  vanish : ∀ (α β : F) (P : F[X]), P.degree ≤ d →
    A ≤ (polynomialAgreementSet domain (combinedWord domain f g (affineMultiplier α β)) P).card →
    affineLineEval α β P Q = 0

open Polynomial.SymbolicInterpolation in
/-- An interpolant exists when the unknowns outnumber the constraints. -/
theorem exists_isAffineInterpolant (domain : ι ↪ F) (f g : ι → F) {d A m D M : ℕ}
    (hsurplus : Fintype.card ι * (constraintSupport m (D + 1)).card <
      (monomialSupport d (m * A - D) (M + 1) (D + 1)).card) :
    ∃ Q, IsAffineInterpolant domain f g d A m D M Q := by
  classical
  -- The unknowns are the coefficients on the monomial support.
  let S := monomialSupport d (m * A - D) (M + 1) (D + 1)
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
      affineYZWeight_none, affineYZWeight_x, affineYZWeight_y]
    omega
  have hline : ∀ e ∈ Q.support, Finsupp.weight (affineLineWeight d) e < m * A := by
    intro e he
    obtain ⟨⟨j, i, t⟩, hk, rfl⟩ := hsupp e he
    simp only [S, mem_monomialSupport] at hk
    simp only [weight_affineVar, affineExponent_none, affineExponent_x, affineExponent_y,
      affineLineWeight_none, affineLineWeight_x, affineLineWeight_y]
    rw [mul_comm j d]
    omega
  have hlt : Q.weightedTotalDegree (affineLineWeight d) < m * A := by
    obtain ⟨e, he⟩ : Q.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (by rwa [Ne, MvPolynomial.support_eq_empty])
    rw [MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff (by
      exact (Nat.zero_le _).trans_lt (hline e he))]
    exact hline
  refine ⟨Q, hQ0, hlt, hyz, ?_, ?_⟩
  · refine MvPolynomial.degreeOf_le_iff.mpr fun e he ↦ ?_
    obtain ⟨⟨j, i, t⟩, hk, rfl⟩ := hsupp e he
    simp only [S, mem_monomialSupport] at hk
    rw [affineExponent_none]
    exact Nat.lt_succ_iff.mp hk.1
  · intro α β P hP hA
    refine eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn (fun i ↦ domain i) _ m A
      (domain.injective.injOn) hA (fun i hi ↦ ?_)
      ((natDegree_affineLineEval_le α β (natDegree_le_of_degree_le hP) Q).trans_lt hlt)
    rw [affineLineEval_eq_aeval_affineShift α β P (domain i) (f i) (g i)]
    refine pow_dvd_aeval_of_le (p := X - C (domain i)) ?_ (by simp) fun e he ↦ ?_
    · rw [mem_polynomialAgreementSet, combinedWord_affineMultiplier] at hi
      rw [Option.elim_none, dvd_iff_isRoot]
      simp [hi]
    · by_contra hlow
      push Not at hlow
      have hwt := (MvPolynomial.le_weightedTotalDegree affineYZWeight he).trans
        ((weightedTotalDegree_affineShift_le _ _ _ Q).trans hyz)
      simp only [weight_affineVar, affineYZWeight_none, affineYZWeight_x,
        affineYZWeight_y] at hwt
      have hT : (⟨e none, (e (some 0), e (some 1))⟩ : Σ _ : ℕ, ℕ × ℕ) ∈ T := by
        simp only [T, mem_constraintSupport]
        omega
      have h0 := congrFun (LinearMap.mem_ker.mp hc) (i, ⟨_, hT⟩)
      simp only [cons, LinearMap.pi_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        MvPolynomial.lcoeff_apply, affineExponent_coords, Pi.zero_apply] at h0
      exact (MvPolynomial.mem_support_iff.mp he) h0

end ReedSolomon
