/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LineEvaluation
public import ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.ToMathlib.MvPolynomial.CurriedDegree
public import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
public import ArkLib.ToMathlib.Polynomial.FrobeniusTaylor

/-!
# The Taylor chart of a root along a linear multiplier family

Fix polynomials `θⱼ`, indexed by a finite type `κ`, and the multipliers `L = ∑ⱼ aⱼ θⱼ`.
At a center `c` where the derivative in `Z` is nonzero, a root `P` of `R(X, L(X), Z)` is
determined by its initial value `y₀` and the coefficient vector `a`.
For each positive order `l`, its Taylor coefficient is a rational function `N_l / S ^ (2l - 1)`
of the chart point `(y₀, a)`, where `S` is the separant at the center.
The numerator has joint degree at most `1 + (2l - 1)(h - 1)`, where `h` bounds the
`(Y, Z)`-degree of `R`.

A linear functional `Λ` on polynomials gives a cut, a polynomial in the chart point.
Its value is `S ^ τ` times `Λ` of the reconstructed root.
An agreement cut subtracts a cleared target polynomial `T` from it.
Reed–Solomon codes use the family `(1, X)`, whose multipliers are the lines `a + b X`.
Their agreement cut at `x` is the agreement cut of evaluation at `x`.

The chart maps and reconstructions are noncomputable mathematical views of polynomial
rings and rational Taylor coefficients.

The coefficient formulas and the polynomial-root reconstruction give Lemma 3.11 for these
multipliers.
Appendix A uses the multipliers `y + ∑ⱼ vⱼ θⱼ(W)` with `θⱼ(0) = 0`.
This is the family `(1, θ₁, …, θ_k)` at the coefficient vector `(y, v)`.
The existence and uniqueness of its formal power series are not stated here.
The reconstruction map, the cuts and their degree budget implement the map and hyperplanes
used in Claim 4.9.
The bound of `ReedSolomon.totalDegree_chartNumerator_le_of_pos` also covers `h = 0`.
Natural-number subtraction prevents deriving that case from the coarser bound.

The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

## Main definitions

* `ReedSolomon.ChartVar`: the chart variables, the initial value and the coefficients.
* `ReedSolomon.familyEquation` and `ReedSolomon.specializedFamilyEquation`: the equation
  `R(X, L(X), Y₀)` over the coefficient ring, and its specialization.
* `ReedSolomon.chartFlatten` and `ReedSolomon.chartSubstitution`: the two views of the chart.
* `ReedSolomon.chartEquation` and `ReedSolomon.chartSeparant`: the hypersurface polynomial and
  its derivative in the initial value.
* `ReedSolomon.chartNumerator` and `ReedSolomon.chartCoefficient`: Taylor coefficients.
* `ReedSolomon.chartPolynomial` and `ReedSolomon.chartPoint`: the polynomial reconstruction and
  the chart point of a root.
* `ReedSolomon.chartFunctionalCut`: the cleared cut of a linear functional.
* `ReedSolomon.chartAgreementCut`: the functional cut minus a cleared target.
* `ReedSolomon.affineChartCut`: the Reed–Solomon agreement cut.

## Main statements

* `ReedSolomon.chartFlatten_C`, `ReedSolomon.chartFlatten_X` and
  `ReedSolomon.aeval_chartFlatten`: the flattening map.
* `ReedSolomon.pderiv_familyEquation`, `ReedSolomon.chartEquation_eq`,
  `ReedSolomon.chartSeparant_eq` and `ReedSolomon.pderiv_chartEquation`: the chart equation is
  `R(c, L(c), y₀)`, and its derivative in `y₀` is the separant.
* `ReedSolomon.aeval_chartEquation`, `ReedSolomon.aeval_chartSeparant`,
  `ReedSolomon.aeval_chartEquation_point` and `ReedSolomon.aeval_chartSeparant_point`: their
  values, in particular at the point of a root.
* `ReedSolomon.differentialSpecialization_specializedFamilyEquation`,
  `ReedSolomon.aeval_chartSeparant_eq` and `ReedSolomon.aeval_chartNumerator`: specialization
  commutes with the chart, and a numerator is `S ^ τ` times its coefficient.
* `ReedSolomon.chartCoefficient_zero`, `ReedSolomon.degree_chartPolynomial_le`,
  `ReedSolomon.eval_chartPolynomial_center` and `ReedSolomon.map_chartPolynomial`: the
  reconstruction starts at `y₀`, has degree at most `d`, and has an explicit functional value.
* `ReedSolomon.aeval_chartFunctionalCut` and `ReedSolomon.chartFunctionalCut_eq_zero_iff`: the
  cut of `Λ` is `S ^ τ` times `Λ` of the reconstruction.
* `ReedSolomon.aeval_chartAgreementCut` and `ReedSolomon.chartAgreementCut_eq_zero_iff`: the
  agreement cut says `Λ` of the reconstruction is the target value.
* `ReedSolomon.aeval_affineChartCut` and `ReedSolomon.affineChartCut_eq_zero_iff`: the
  Reed–Solomon cut says the reconstruction takes a value.
* `ReedSolomon.chartPolynomial_point`: recover `P` when `expand (p^e) P` is a regular root.
* `ReedSolomon.totalDegree_aeval_chartSubstitution_le`,
  `ReedSolomon.totalDegree_chartEquation_le`, `ReedSolomon.totalDegree_chartSeparant_le` and
  `ReedSolomon.chartSeparant_eq_zero`: the chart does not raise the `(Y, Z)`-degree.
* `ReedSolomon.totalDegree_chartNumerator_le`,
  `ReedSolomon.totalDegree_chartNumerator_le_of_pos`,
  `ReedSolomon.totalDegree_chartFunctionalCut_le`,
  `ReedSolomon.totalDegree_chartAgreementCut_le` and
  `ReedSolomon.totalDegree_affineChartCut_le`: the joint degree bounds.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26], Lemma 3.11, Claim 4.9 and
    Appendix A.
-/

@[expose] public section

namespace ReedSolomon

open MvPolynomial PolynomialDifferential

variable {E : Type*} [Field E] {κ : Type*}

/-- The chart variables: `inl 0` is the initial value `y₀` and `inr j` is the coefficient `aⱼ`. -/
abbrev ChartVar (κ : Type*) : Type _ := Fin 1 ⊕ κ

/-- Polynomials in `y₀` over `E[(aⱼ)ⱼ]` read as polynomials in the chart variables. -/
noncomputable def chartFlatten :
    MvPolynomial (Fin 1) (MvPolynomial κ E) ≃ₐ[E] MvPolynomial (ChartVar κ) E :=
  (sumAlgEquiv E (Fin 1) κ).symm

/-- The chart point `(P(c ^ s), a)` of a root `expand s P` along the coefficients `a`. -/
noncomputable def chartPoint (c : E) (s : ℕ) (a : κ → E) (P : Polynomial E) : ChartVar κ → E :=
  Sum.elim (fun _ ↦ (Polynomial.expand E s P).eval c) a

variable [Fintype κ]

/-- The order-zero differential equation `R(X, ∑ⱼ aⱼ θⱼ(X), Y₀)` over `E[(aⱼ)ⱼ]`. -/
noncomputable def familyEquation (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E) :
    DifferentialPolynomial (MvPolynomial κ E) 0 :=
  aeval (fun v ↦ v.elim (X (some 0))
    ![X none, ∑ j, C (X j) * Polynomial.aeval (X none) (θ j)]) R

/-- The chart substitution `Z ↦ y₀`, `X ↦ c`, `Y ↦ ∑ⱼ θⱼ(c) aⱼ`. -/
noncomputable def chartSubstitution (c : E) (θ : κ → Polynomial E) :
    AffineVar → MvPolynomial (ChartVar κ) E :=
  fun v ↦ v.elim (X (.inl 0)) ![C c, ∑ j, C ((θ j).eval c) * X (.inr j)]

/-- The polynomial defining the chart hypersurface `R(c, ∑ⱼ aⱼ θⱼ(c), y₀) = 0`. -/
noncomputable def chartEquation (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E) :
    MvPolynomial (ChartVar κ) E :=
  chartFlatten (initialJetEquation (C c) (familyEquation θ R))

/-- The chart separant `R_Z(c, ∑ⱼ aⱼ θⱼ(c), y₀)`. -/
noncomputable def chartSeparant (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E) :
    MvPolynomial (ChartVar κ) E :=
  chartFlatten (initialJetSeparant (C c) (familyEquation θ R))

/-- The Taylor numerator at order `l` and center `c`, padded to separant exponent `τ`.

It represents the coefficient over `S ^ τ` when `2l - 1 ≤ τ` and the separant `S` is nonzero. -/
noncomputable def chartNumerator (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (τ l : ℕ) : MvPolynomial (ChartVar κ) E :=
  chartFlatten (commonTaylorNumeratorOver E (C c) (familyEquation θ R) τ l)

/-- The cut of a linear functional `Λ`: the numerators weighted by `Λ((X - c ^ s) ^ j)`.

Let `S` be the chart separant at the point.
When `S ≠ 0` and `2 s d - 1 ≤ τ`, the cut is `S ^ τ` times `Λ` of the reconstruction.
The subtraction `2 s d - 1` is natural-number subtraction. -/
noncomputable def chartFunctionalCut (c : E) (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) (s d τ : ℕ) (Λ : Polynomial E →ₗ[E] E) :
    MvPolynomial (ChartVar κ) E :=
  ∑ j ∈ Finset.range (d + 1),
    C (Λ ((Polynomial.X - Polynomial.C (c ^ s)) ^ j)) * chartNumerator c θ R τ (s * j)

/-- The family equation with the coefficients specialized to `a`. -/
noncomputable def specializedFamilyEquation (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) (a : κ → E) : DifferentialPolynomial E 0 :=
  map (aeval a).toRingHom (familyEquation θ R)

/-- The rational Taylor coefficient `c_l` at center `c` of the chart point `pt`. -/
noncomputable def chartCoefficient (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (pt : ChartVar κ → E) (l : ℕ) : E :=
  rationalTaylorCoefficient c (specializedFamilyEquation θ R (pt ∘ Sum.inr)) (pt ∘ Sum.inl) l

/-- The reconstruction `∑_{j ≤ d} c_{s j}(pt) (X - c ^ s) ^ j`. -/
noncomputable def chartPolynomial (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (s d : ℕ) (pt : ChartVar κ → E) : Polynomial E :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.C (chartCoefficient c θ R pt (s * j)) *
    (Polynomial.X - Polynomial.C (c ^ s)) ^ j

/-- The agreement cut of `Λ` with target `T`: the cut of `Λ` minus `T S ^ τ`.

Here `S` is the chart separant. -/
noncomputable def chartAgreementCut (c : E) (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) (s d τ : ℕ) (Λ : Polynomial E →ₗ[E] E)
    (T : MvPolynomial (ChartVar κ) E) : MvPolynomial (ChartVar κ) E :=
  chartFunctionalCut c θ R s d τ Λ - T * chartSeparant c θ R ^ τ

/-- The Reed–Solomon agreement cut at `x`, with target `u + (a ^ s + x b ^ s) v`.

Here `(y₀, a, b)` is the chart point and `S` its chart separant.
When `S ≠ 0` and `2 s d - 1 ≤ τ`, the cut vanishes iff the reconstruction hits the target at `x`.
The subtraction `2 s d - 1` is natural-number subtraction. -/
noncomputable def affineChartCut (c : E) (R : MvPolynomial AffineVar E) (s d τ : ℕ) (x u v : E) :
    MvPolynomial (ChartVar (Fin 2)) E :=
  chartAgreementCut c affineFamily R s d τ (Polynomial.leval x)
    (C u + (X (.inr 0) ^ s + C x * X (.inr 1) ^ s) * C v)

/-! ### Flattening and evaluation -/

omit [Fintype κ] in
/-- A coefficient flattens to the same polynomial in the coefficient variables. -/
theorem chartFlatten_C (a : MvPolynomial κ E) :
    chartFlatten (C a : MvPolynomial (Fin 1) (MvPolynomial κ E)) = rename Sum.inr a := by
  induction a using MvPolynomial.induction_on with
  | C e => simp [chartFlatten]
  | add p q hp hq => rw [C_add, map_add, hp, hq, map_add]
  | mul_X p i hp => rw [C_mul, map_mul, hp, map_mul, rename_X]; simp [chartFlatten]

omit [Fintype κ] in
/-- The initial-value variable flattens to `y₀`. -/
@[simp] theorem chartFlatten_X (i : Fin 1) :
    chartFlatten (X i : MvPolynomial (Fin 1) (MvPolynomial κ E)) = X (.inl i) := by
  simp [chartFlatten]

omit [Fintype κ] in
/-- Evaluating a flattened polynomial specializes the coefficients, then the initial value. -/
theorem aeval_chartFlatten (pt : ChartVar κ → E) (P : MvPolynomial (Fin 1) (MvPolynomial κ E)) :
    aeval pt (chartFlatten P) = aeval (pt ∘ Sum.inl) (map (aeval (pt ∘ Sum.inr)).toRingHom P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [chartFlatten_C, aeval_rename]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, chartFlatten_X, map_X, aeval_X,
      Function.comp_apply]

omit [Fintype κ] in
/-- Setting the independent variable to `c` turns a polynomial in it into its value at `c`. -/
private theorem chartFlatten_aeval_aeval_X_none (c : E) (θ : Polynomial E) :
    chartFlatten (aeval (fun i : Option (Fin (0 + 1)) ↦
      i.elim (C (C c) : MvPolynomial (Fin (0 + 1)) (MvPolynomial κ E)) X)
      (Polynomial.aeval (X none : DifferentialPolynomial (MvPolynomial κ E) 0) θ)) =
        C (θ.eval c) := by
  induction θ using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | monomial n a => simp [Polynomial.aeval_monomial, chartFlatten, MvPolynomial.algebraMap_eq]

/-- The partial derivative in `Y₀` of the family equation is the family equation of `R_Z`. -/
theorem pderiv_familyEquation (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E) :
    pderiv (some 0) (familyEquation θ R) = familyEquation θ (pderiv none R) := by
  unfold familyEquation
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, aeval_X]
    rcases v with _ | ⟨i⟩
    · simp [pderiv_X]
    · fin_cases i
      · simp [pderiv_X]
      · simp [pderiv_X, pderiv_polynomial_aeval_X_of_ne]

/-- The chart equation is `R(c, ∑ⱼ aⱼ θⱼ(c), y₀)`. -/
theorem chartEquation_eq (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E) :
    chartEquation c θ R = aeval (chartSubstitution c θ) R := by
  induction R using MvPolynomial.induction_on with
  | C a => simp [chartEquation, familyEquation, initialJetEquation, chartFlatten]
  | add p q hp hq =>
    simp only [chartEquation, familyEquation, initialJetEquation, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [chartEquation, familyEquation, initialJetEquation, map_mul] at hp ⊢
    rw [hp]
    congr 1
    rcases v with _ | ⟨i⟩
    · simp [chartFlatten, chartSubstitution]
    · fin_cases i
      · simp [chartFlatten, chartSubstitution]
      · simp only [Fin.mk_one, aeval_X, Option.elim_some, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, map_sum, map_mul, chartFlatten_aeval_aeval_X_none,
          chartSubstitution]
        simp [chartFlatten_C, mul_comm]

/-- The chart separant is `R_Z(c, ∑ⱼ aⱼ θⱼ(c), y₀)`. -/
theorem chartSeparant_eq (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E) :
    chartSeparant c θ R = aeval (chartSubstitution c θ) (pderiv none R) := by
  rw [← chartEquation_eq, chartSeparant, chartEquation, initialJetSeparant, separant,
    Fin.last_zero, pderiv_familyEquation]
  rfl

/-- The derivative of the chart equation in `y₀` is the chart separant. -/
theorem pderiv_chartEquation (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E) :
    pderiv (.inl 0) (chartEquation c θ R) = chartSeparant c θ R := by
  rw [chartSeparant_eq, chartEquation_eq]
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, aeval_X]
    rcases v with _ | ⟨i⟩
    · simp [chartSubstitution, pderiv_X]
    · fin_cases i <;> simp [chartSubstitution, pderiv_X]

/-- The chart equation at `pt` is `R(c, L(c), y₀)` for the multiplier `L = ∑ⱼ aⱼ θⱼ`. -/
theorem aeval_chartEquation (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (pt : ChartVar κ → E) :
    aeval pt (chartEquation c θ R) = aeval (fun v ↦ v.elim (pt (.inl 0))
      ![c, (familyMultiplier θ (pt ∘ Sum.inr)).eval c]) R := by
  rw [chartEquation_eq, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext v
  rcases v with _ | ⟨i⟩
  · simp [chartSubstitution]
  · fin_cases i <;> simp [chartSubstitution, familyMultiplier_apply, Polynomial.eval_finsetSum,
      mul_comm]

/-- The chart separant at `pt` is `R_Z(c, L(c), y₀)` for the multiplier `L = ∑ⱼ aⱼ θⱼ`. -/
theorem aeval_chartSeparant (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (pt : ChartVar κ → E) :
    aeval pt (chartSeparant c θ R) = aeval (fun v ↦ v.elim (pt (.inl 0))
      ![c, (familyMultiplier θ (pt ∘ Sum.inr)).eval c]) (pderiv none R) := by
  rw [chartSeparant_eq, ← chartEquation_eq, aeval_chartEquation]

/-- At the point of a root, the chart equation is the evaluation along the multiplier at `c`. -/
theorem aeval_chartEquation_point (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (s : ℕ) (a : κ → E) (P : Polynomial E) :
    aeval (chartPoint c s a P) (chartEquation c θ R) =
      (multiplierEval (familyMultiplier θ a) (Polynomial.expand E s P) R).eval c := by
  rw [aeval_chartEquation, eval_multiplierEval]
  rfl

/-- At the point of a root, the chart separant is `R_Z` along the multiplier at `c`. -/
theorem aeval_chartSeparant_point (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (s : ℕ) (a : κ → E) (P : Polynomial E) :
    aeval (chartPoint c s a P) (chartSeparant c θ R) =
      (multiplierEval (familyMultiplier θ a) (Polynomial.expand E s P) (pderiv none R)).eval c := by
  rw [aeval_chartSeparant, eval_multiplierEval]
  rfl

/-- The specialized family equation along `P` is `R(X, ∑ⱼ aⱼ θⱼ(X), P)`. -/
theorem differentialSpecialization_specializedFamilyEquation (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) (a : κ → E) (P : Polynomial E) :
    differentialSpecialization (specializedFamilyEquation θ R a) P =
      multiplierEval (familyMultiplier θ a) P R := by
  unfold specializedFamilyEquation familyEquation differentialSpecialization
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    rcases v with _ | ⟨i⟩
    · simp [differentialSpecializationHom]
    · fin_cases i
      · simp [differentialSpecializationHom]
      · simp only [differentialSpecializationHom, familyMultiplier_apply,
          AlgHom.toRingHom_eq_coe, coe_aeval_eq_eval, Fin.mk_one,
          aeval_X, Option.elim_some, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_sum,
          map_mul, map_C, eval_X, algHom_C, Polynomial.algebraMap_eq, multiplierEval_X_Y]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        congr 1
        induction θ j using Polynomial.induction_on' with
          | add p q hp hq => simp only [map_add, hp, hq]
          | monomial n b => simp [Polynomial.aeval_monomial, Polynomial.C_mul_X_pow_eq_monomial]

/-- Specializing the coefficients commutes with the chart separant. -/
theorem aeval_chartSeparant_eq (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (pt : ChartVar κ → E) :
    aeval pt (chartSeparant c θ R) = aeval (pt ∘ Sum.inl)
      (initialJetSeparant c (specializedFamilyEquation θ R (pt ∘ Sum.inr))) := by
  rw [chartSeparant, aeval_chartFlatten, map_initialJetSeparant]
  simp [specializedFamilyEquation]

/-- On `S ≠ 0`, the numerator at `pt` is `S ^ τ` times the coefficient `c_l`. -/
theorem aeval_chartNumerator (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (pt : ChartVar κ → E) {τ l : ℕ} (hl : 2 * l - 1 ≤ τ)
    (hS : aeval pt (chartSeparant c θ R) ≠ 0) :
    aeval pt (chartNumerator c θ R τ l) =
      aeval pt (chartSeparant c θ R) ^ τ * chartCoefficient c θ R pt l := by
  rw [aeval_chartSeparant_eq] at hS ⊢
  rw [chartNumerator, aeval_chartFlatten, map_commonTaylorNumeratorOver_eq]
  simp only [AlgHom.toRingHom_eq_coe, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
  exact aeval_commonTaylorNumerator c _ _ (by simpa using hl) hS

/-! ### The reconstruction and the cuts -/

/-- The coefficient `c_0` is the initial value `y₀`. -/
@[simp] theorem chartCoefficient_zero (c : E) (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) (pt : ChartVar κ → E) :
    chartCoefficient c θ R pt 0 = pt (.inl 0) :=
  rationalTaylorCoefficient_initial c _ (pt ∘ Sum.inl) 0

/-- The reconstruction has degree at most `d`. -/
theorem degree_chartPolynomial_le (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (s d : ℕ) (pt : ChartVar κ → E) : (chartPolynomial c θ R s d pt).degree ≤ d := by
  refine Polynomial.degree_le_of_natDegree_le
    (Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_)
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

/-- The reconstruction takes the value `y₀` at `c ^ s`. -/
theorem eval_chartPolynomial_center (c : E) (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) (s d : ℕ) (pt : ChartVar κ → E) :
    (chartPolynomial c θ R s d pt).eval (c ^ s) = pt (.inl 0) := by
  rw [chartPolynomial, Polynomial.eval_finsetSum, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- A linear functional of the reconstruction is `∑_{j ≤ d} c_{s j} Λ((X - c ^ s) ^ j)`. -/
theorem map_chartPolynomial (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    (s d : ℕ) (pt : ChartVar κ → E) (Λ : Polynomial E →ₗ[E] E) :
    Λ (chartPolynomial c θ R s d pt) = ∑ j ∈ Finset.range (d + 1),
      chartCoefficient c θ R pt (s * j) * Λ ((Polynomial.X - Polynomial.C (c ^ s)) ^ j) := by
  simp [chartPolynomial, ← Polynomial.smul_eq_C_mul]

/-- The cut of `Λ` at `pt` is `S ^ τ` times `Λ` of the reconstruction.

Here `S` is the chart separant at `pt`, assumed nonzero, and `2 s d - 1 ≤ τ`.
The subtraction `2 s d - 1` is natural-number subtraction. -/
theorem aeval_chartFunctionalCut (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    {s d τ : ℕ} (hτ : 2 * s * d - 1 ≤ τ) (Λ : Polynomial E →ₗ[E] E) (pt : ChartVar κ → E)
    (hS : aeval pt (chartSeparant c θ R) ≠ 0) :
    aeval pt (chartFunctionalCut c θ R s d τ Λ) =
      aeval pt (chartSeparant c θ R) ^ τ * Λ (chartPolynomial c θ R s d pt) := by
  rw [chartFunctionalCut, map_sum, map_chartPolynomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : 2 * (s * j) - 1 ≤ τ := by
    have := Finset.mem_range.mp hj
    have : s * j ≤ s * d := Nat.mul_le_mul_left _ (by omega)
    have : 2 * s * d = 2 * (s * d) := Nat.mul_assoc _ _ _
    omega
  rw [map_mul, aeval_chartNumerator c θ R pt hj' hS, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply]
  ring

/-- The cut of `Λ` at `pt` vanishes iff `Λ` kills the reconstruction.

Here the chart separant at `pt` is nonzero and `2 s d - 1 ≤ τ`.
The subtraction `2 s d - 1` is natural-number subtraction. -/
theorem chartFunctionalCut_eq_zero_iff (c : E) (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) {s d τ : ℕ} (hτ : 2 * s * d - 1 ≤ τ)
    (Λ : Polynomial E →ₗ[E] E) (pt : ChartVar κ → E) (hS : aeval pt (chartSeparant c θ R) ≠ 0) :
    aeval pt (chartFunctionalCut c θ R s d τ Λ) = 0 ↔ Λ (chartPolynomial c θ R s d pt) = 0 := by
  rw [aeval_chartFunctionalCut c θ R hτ Λ pt hS, mul_eq_zero, or_iff_right (pow_ne_zero _ hS)]

/-- The agreement cut of `Λ` with target `T` at `pt` is `S ^ τ (Λ(P_pt) - T(pt))`.

Here `S` is the chart separant at `pt`, assumed nonzero, and `P_pt` is the reconstruction.
The exponent satisfies `2 s d - 1 ≤ τ`, with natural-number subtraction. -/
theorem aeval_chartAgreementCut (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    {s d τ : ℕ} (hτ : 2 * s * d - 1 ≤ τ) (Λ : Polynomial E →ₗ[E] E)
    (T : MvPolynomial (ChartVar κ) E) (pt : ChartVar κ → E)
    (hS : aeval pt (chartSeparant c θ R) ≠ 0) :
    aeval pt (chartAgreementCut c θ R s d τ Λ T) = aeval pt (chartSeparant c θ R) ^ τ *
      (Λ (chartPolynomial c θ R s d pt) - aeval pt T) := by
  rw [chartAgreementCut, map_sub, aeval_chartFunctionalCut c θ R hτ Λ pt hS, map_mul, map_pow]
  ring

/-- The agreement cut of `Λ` with target `T` vanishes at `pt` iff `Λ(P_pt) = T(pt)`.

Here the chart separant at `pt` is nonzero and `P_pt` is the reconstruction.
The exponent satisfies `2 s d - 1 ≤ τ`, with natural-number subtraction. -/
theorem chartAgreementCut_eq_zero_iff (c : E) (θ : κ → Polynomial E)
    (R : MvPolynomial AffineVar E) {s d τ : ℕ} (hτ : 2 * s * d - 1 ≤ τ)
    (Λ : Polynomial E →ₗ[E] E) (T : MvPolynomial (ChartVar κ) E) (pt : ChartVar κ → E)
    (hS : aeval pt (chartSeparant c θ R) ≠ 0) :
    aeval pt (chartAgreementCut c θ R s d τ Λ T) = 0 ↔
      Λ (chartPolynomial c θ R s d pt) = aeval pt T := by
  rw [aeval_chartAgreementCut c θ R hτ Λ T pt hS, mul_eq_zero,
    or_iff_right (pow_ne_zero _ hS), sub_eq_zero]

/-- The Reed–Solomon cut at `pt` is `S ^ τ` times the discrepancy of the reconstruction.

Here `pt = (y₀, a, b)` and `S` is its chart separant, assumed nonzero.
The exponent satisfies `2 s d - 1 ≤ τ`, with natural-number subtraction. -/
theorem aeval_affineChartCut (c : E) (R : MvPolynomial AffineVar E) {s d τ : ℕ}
    (hτ : 2 * s * d - 1 ≤ τ) (x u v : E) (pt : ChartVar (Fin 2) → E)
    (hS : aeval pt (chartSeparant c affineFamily R) ≠ 0) :
    aeval pt (affineChartCut c R s d τ x u v) = aeval pt (chartSeparant c affineFamily R) ^ τ *
      ((chartPolynomial c affineFamily R s d pt).eval x -
        (u + (pt (.inr 0) ^ s + x * pt (.inr 1) ^ s) * v)) := by
  rw [affineChartCut, aeval_chartAgreementCut c affineFamily R hτ _ _ pt hS]
  simp

/-- The Reed–Solomon cut vanishes iff the reconstruction is `u + (a ^ s + x b ^ s) v` at `x`.

Here the chart separant at `pt = (y₀, a, b)` is nonzero.
The exponent satisfies `2 s d - 1 ≤ τ`, with natural-number subtraction. -/
theorem affineChartCut_eq_zero_iff (c : E) (R : MvPolynomial AffineVar E) {s d τ : ℕ}
    (hτ : 2 * s * d - 1 ≤ τ) (x u v : E) (pt : ChartVar (Fin 2) → E)
    (hS : aeval pt (chartSeparant c affineFamily R) ≠ 0) :
    aeval pt (affineChartCut c R s d τ x u v) = 0 ↔
      (chartPolynomial c affineFamily R s d pt).eval x =
        u + (pt (.inr 0) ^ s + x * pt (.inr 1) ^ s) * v := by
  rw [affineChartCut, chartAgreementCut_eq_zero_iff c affineFamily R hτ _ _ pt hS]
  simp

/-- Let `s = p ^ e`, where `p` is the exponential characteristic, and `L = ∑ⱼ aⱼ θⱼ`.
Let `expand s P` be a root of `R(X, L(X), Z)` with `R_Z ≠ 0` at `c`.

If `deg P ≤ d`, the reconstruction at the point of the root is `P`. -/
theorem chartPolynomial_point (c : E) (θ : κ → Polynomial E) (R : MvPolynomial AffineVar E)
    {p e s d : ℕ} [ExpChar E p] (hs : s = p ^ e) {a : κ → E} {P : Polynomial E}
    (hP : P.degree ≤ d)
    (hroot : multiplierEval (familyMultiplier θ a) (Polynomial.expand E s P) R = 0)
    (hsep : (multiplierEval (familyMultiplier θ a) (Polynomial.expand E s P)
      (pderiv none R)).eval c ≠ 0) :
    chartPolynomial c θ R s d (chartPoint c s a P) = P := by
  set pt := chartPoint c s a P
  have ha : pt ∘ Sum.inr = a := rfl
  have hsol : differentialSpecialization (specializedFamilyEquation θ R a)
      (Polynomial.expand E s P) = 0 := by
    rwa [differentialSpecialization_specializedFamilyEquation]
  have hsepJ : jetEvaluation (separant (specializedFamilyEquation θ R a) (Fin.last 0)) c
      (polynomialJet c (Polynomial.expand E s P)) ≠ 0 := by
    rw [← eval_differentialSpecialization, separant, Fin.last_zero, specializedFamilyEquation,
      pderiv_map, pderiv_familyEquation, ← specializedFamilyEquation,
      differentialSpecialization_specializedFamilyEquation]
    exact hsep
  have hjet : pt ∘ Sum.inl = polynomialJet c (Polynomial.expand E s P) := by
    funext i
    rw [Fin.fin_one_eq_zero i, polynomialJet, Polynomial.hasseJet_eq_taylor_coeff,
      Fin.val_zero, Polynomial.taylor_coeff_zero]
    rfl
  have hcoef : ∀ j,
      chartCoefficient c θ R pt (s * j) = (Polynomial.taylor (c ^ s) P).coeff j := by
    intro j
    rw [chartCoefficient, ha, hjet,
      rationalTaylorCoefficient_eq_solution c _ _ hsol hsepJ _ (fun i _ _ ↦ by simp), hs,
      Polynomial.coeff_taylor_expand_expChar_pow_mul, Polynomial.taylor_coeff]
  have hdeg : (Polynomial.taylor (c ^ s) P).natDegree < d + 1 := by
    rw [Polynomial.natDegree_taylor]
    exact Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le hP)
  conv_rhs => rw [← Polynomial.sum_taylor_eq P (c ^ s)]
  rw [Polynomial.sum_over_range' _ (fun _ ↦ by simp) _ hdeg, chartPolynomial]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hcoef]

/-! ### Joint degree bounds -/

/-- The chart substitution does not raise the `(Y, Z)`-degree. -/
theorem totalDegree_aeval_chartSubstitution_le (c : E) (θ : κ → Polynomial E)
    (P : MvPolynomial AffineVar E) :
    (aeval (chartSubstitution c θ) P).totalDegree ≤ P.weightedTotalDegree affineYZWeight := by
  rw [← weightedTotalDegree_one]
  apply weightedTotalDegree_aeval_le_of_le
  intro v
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  rcases v with _ | ⟨i⟩
  · exact X_mem_restrictWeightedDegree _ _ _ le_rfl
  · fin_cases i
    · exact C_mem_restrictWeightedDegree _ _ _
    · refine Submodule.sum_mem _ fun j _ ↦ ?_
      simpa using mul_mem_restrictWeightedDegree (C_mem_restrictWeightedDegree _ 0 _)
        (X_mem_restrictWeightedDegree (1 : ChartVar κ → ℕ) 1 (.inr j) le_rfl)

/-- The chart equation has degree at most the `(Y, Z)`-degree of `R`. -/
theorem totalDegree_chartEquation_le (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {h : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    (chartEquation c θ R).totalDegree ≤ h := by
  rw [chartEquation_eq]
  exact (totalDegree_aeval_chartSubstitution_le c θ R).trans hR

/-- If `R` has `(Y, Z)`-degree at most `h`, the chart separant has degree at most `h - 1`.

The subtraction is natural-number subtraction. -/
theorem totalDegree_chartSeparant_le (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {h : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    (chartSeparant c θ R).totalDegree ≤ h - 1 := by
  rw [chartSeparant_eq]
  refine (totalDegree_aeval_chartSubstitution_le c θ _).trans ?_
  refine (weightedTotalDegree_pderiv_le_sub affineYZWeight none R).trans ?_
  simp only [affineYZWeight_none]
  omega

/-- With `(Y, Z)`-degree `0`, the chart separant vanishes. -/
theorem chartSeparant_eq_zero (c : E) (θ : κ → Polynomial E) {R : MvPolynomial AffineVar E}
    (hR : R.weightedTotalDegree affineYZWeight ≤ 0) : chartSeparant c θ R = 0 := by
  rw [chartSeparant_eq,
    pderiv_eq_zero_of_weightedTotalDegree_lt affineYZWeight none R (by simp; omega), map_zero]

/-- Each residual monomial, with its coefficient degree added, has degree at most `h`. -/
private theorem totalDegree_residual_coeff_add_degree_le (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {h : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (l t : ℕ) (m : Fin l →₀ ℕ) (hm : m ∈ ((optionEquivLeft (MvPolynomial κ E) (Fin l)
      (universalTaylorResidual l (C c) (familyEquation θ R))).coeff t).support) :
    (((optionEquivLeft (MvPolynomial κ E) (Fin l)
      (universalTaylorResidual l (C c) (familyEquation θ R))).coeff t).coeff m).totalDegree +
        m.degree ≤ h := by
  set w : Option (Fin l) → ℕ := fun i ↦ i.elim 0 fun _ ↦ 1
  set Res := universalTaylorResidual l (C c) (familyEquation θ R)
  rw [mem_support_iff, optionEquivLeft_coeff_coeff] at hm
  rw [optionEquivLeft_coeff_coeff, ← MvPolynomial.weight_optionElim_zero_one m t]
  refine (totalDegree_coeff_add_weight_le_weightedTotalDegree_sumAlgEquiv_symm
    w Res (mem_support_iff.mpr hm)).trans ?_
  set flat := (sumAlgEquiv E (Option (Fin l)) κ).symm
  set jet := (aeval (R := MvPolynomial κ E) (fun i : Option (Fin (0 + 1)) ↦
    i.elim (C (C c) + X none) fun j ↦
      universalTaylorJet (F := MvPolynomial κ E) l j.val)).restrictScalars E
  set sub : AffineVar → DifferentialPolynomial (MvPolynomial κ E) 0 := fun v ↦
    v.elim (X (some 0)) ![X none, ∑ j, C (X j) * Polynomial.aeval (X none) (θ j)]
  have hflat : flat Res = aeval (fun v ↦ flat (jet (sub v))) R := by
    have := DFunLike.congr_fun (comp_aeval (R := E) (f := sub) (flat.toAlgHom.comp jet)) R
    simpa [Res, universalTaylorResidual, familyEquation, jet, sub] using this
  rw [hflat]
  refine (weightedTotalDegree_aeval_le_of_le affineYZWeight _ _ R fun v ↦ ?_).trans hR
  apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mp
  -- The independent variable becomes `c + X`, which has weight `0`.
  have hX : flat (jet (X none)) ∈ restrictWeightedDegree (Sum.elim w 1) 0 := by
    simp only [jet, AlgHom.restrictScalars_apply, aeval_X, Option.elim_none, map_add, flat,
      sumAlgEquiv_symm_C_C, sumAlgEquiv_symm_X]
    exact Submodule.add_mem _ (C_mem_restrictWeightedDegree (R := E) (Sum.elim w 1) 0 c)
      (X_mem_restrictWeightedDegree (R := E) (Sum.elim w 1) 0 (.inl none) (by simp [w]))
  rcases v with _ | ⟨i⟩
  · apply mem_restrictWeightedDegree_iff_weightedTotalDegree_le.mpr
    simp only [sub, jet, AlgHom.restrictScalars_apply, Option.elim_none, aeval_X,
      Option.elim_some, Fin.val_zero]
    rw [← map_universalTaylorJet (algebraMap E (MvPolynomial κ E)),
      sumAlgEquiv_symm_map_algebraMap,
      weightedTotalDegree_rename_of_injective Sum.inl_injective]
    exact weightedTotalDegree_universalTaylorJet_le l 0
  · fin_cases i
    · simpa [sub] using hX
    · simp only [sub, Fin.mk_one, Option.elim_some, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        map_sum, map_mul, affineYZWeight_Y]
      refine Submodule.sum_mem _ fun j _ ↦ ?_
      have hC : flat (jet (C (X j))) = X (.inr j) := by
        simp [jet, flat, sumAlgEquiv_symm_C_X]
      have hθ : flat (jet (Polynomial.aeval (X none) (θ j))) =
          Polynomial.aeval (flat (jet (X none))) (θ j) :=
        (Polynomial.aeval_algHom_apply (flat.toAlgHom.comp jet) _ _).symm
      rw [hC, hθ]
      exact mul_mem_restrictWeightedDegree (d := 1) (e := 0)
        (X_mem_restrictWeightedDegree (R := E) (Sum.elim w 1) 1 (.inr j) (by simp))
        (polynomial_aeval_mem_restrictWeightedDegree_zero hX _)

/-- The flattening map satisfies the hypotheses of the joint numerator bound. -/
private theorem chartFlatten_numerator_hypotheses (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {h : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h) :
    (∀ i, (chartFlatten.toAlgHom (X i : MvPolynomial (Fin 1) (MvPolynomial κ E))).totalDegree ≤
      1) ∧
    (chartFlatten.toAlgHom (initialJetSeparant (C c) (familyEquation θ R))).totalDegree ≤
      h - 1 ∧
    ∀ l, 0 < l → ∀ m ∈ ((optionEquivLeft (MvPolynomial κ E) (Fin l)
      (universalTaylorResidual l (C c) (familyEquation θ R))).coeff (l - 0)).support,
      (chartFlatten.toAlgHom (C (((optionEquivLeft (MvPolynomial κ E) (Fin l)
        (universalTaylorResidual l (C c) (familyEquation θ R))).coeff (l - 0)).coeff m))
          ).totalDegree + m.degree ≤ h := by
  refine ⟨fun i ↦ ?_, totalDegree_chartSeparant_le c θ hR, fun l _ m hm ↦ ?_⟩
  · simp [totalDegree_X]
  · have hle := totalDegree_residual_coeff_add_degree_le c θ hR l (l - 0) m hm
    change (chartFlatten (C _)).totalDegree + _ ≤ _
    rw [chartFlatten_C]
    exact (Nat.add_le_add_right (totalDegree_rename_le _ _) _).trans hle

/-- If `2l - 1 ≤ τ`, the numerator of `c_l` has degree at most `1 + τ (h - 1)`.

Here `h` bounds the `(Y, Z)`-degree of `R`, and the subtractions are in `ℕ`. -/
theorem totalDegree_chartNumerator_le (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {h τ l : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (hl : 2 * l - 1 ≤ τ) :
    (chartNumerator c θ R τ l).totalDegree ≤ 1 + τ * (h - 1) := by
  obtain ⟨hX, hS, hres⟩ := chartFlatten_numerator_hypotheses c θ hR
  exact totalDegree_algHom_commonTaylorNumeratorOver_le chartFlatten.toAlgHom (C c)
    (familyEquation θ R) (h - 1) h (by omega) hX hS hres (by simpa using hl)

/-- For `l > 0` and `2l - 1 ≤ τ`, the numerator has degree at most `(τ - 1)(h - 1) + h`.

Here `h` bounds the `(Y, Z)`-degree of `R`, and the subtractions are in `ℕ`. -/
theorem totalDegree_chartNumerator_le_of_pos (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {h τ l : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (hl0 : 0 < l) (hl : 2 * l - 1 ≤ τ) :
    (chartNumerator c θ R τ l).totalDegree ≤ (τ - 1) * (h - 1) + h := by
  obtain ⟨hX, hS, hres⟩ := chartFlatten_numerator_hypotheses c θ hR
  exact totalDegree_algHom_commonTaylorNumeratorOver_le_of_lt chartFlatten.toAlgHom
    (C c) (familyEquation θ R) (h - 1) h (by omega) hX hS hres hl0 (by simpa using hl)

/-- For `1 ≤ h` and `a ≤ 2 s d`, the bound `(2 s d - 1)(h - 1) + a ≤ 2 s d h`. -/
private theorem two_mul_sub_one_mul_sub_one_add_le {s d h a : ℕ} (hh : 1 ≤ h)
    (ha : a ≤ 2 * s * d) : (2 * s * d - 1) * (h - 1) + a ≤ 2 * s * d * h := by
  have : (2 * s * d - 1) * (h - 1) ≤ 2 * s * d * (h - 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have : 2 * s * d * (h - 1) + 2 * s * d = 2 * s * d * h := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  omega

/-- With `τ = 2 s d - 1`, every numerator of the reconstruction has degree at most `2 s d h`. -/
private theorem totalDegree_chartNumerator_le_two_mul (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {s d h j : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (hj : j ≤ d) :
    (chartNumerator c θ R (2 * s * d - 1) (s * j)).totalDegree ≤ 2 * s * d * h := by
  have hsj : s * j ≤ s * d := Nat.mul_le_mul_left s hj
  have hsd : 1 ≤ s * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : 2 * s * d = 2 * (s * d) := Nat.mul_assoc _ _ _
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · -- The order-zero numerator is `y₀ S ^ τ`, and `S = 0`.
      rw [Nat.mul_zero, chartNumerator, commonTaylorNumeratorOver, map_mul, map_pow]
      change (chartFlatten _ * chartSeparant c θ R ^ _).totalDegree ≤ _
      rw [chartSeparant_eq_zero c θ hR, zero_pow (by omega), mul_zero, totalDegree_zero]
      exact Nat.zero_le _
    · have := totalDegree_chartNumerator_le_of_pos c θ hR (τ := 2 * s * d - 1) (l := s * j)
        (Nat.mul_pos (by omega) hj0) (by omega)
      simpa using this
  · have := totalDegree_chartNumerator_le c θ hR (τ := 2 * s * d - 1) (l := s * j) (by omega)
    have := two_mul_sub_one_mul_sub_one_add_le (s := s) (d := d) (a := 1) hh (by omega)
    omega

/-- For positive `s` and `d`, the cut of `Λ` with `τ = 2 s d - 1` has degree at most `2 s d h`.

Here `h` bounds the `(Y, Z)`-degree of `R`. -/
theorem totalDegree_chartFunctionalCut_le (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {s d h : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (Λ : Polynomial E →ₗ[E] E) :
    (chartFunctionalCut c θ R s d (2 * s * d - 1) Λ).totalDegree ≤ 2 * s * d * h := by
  refine totalDegree_finsetSum_le fun j hj ↦ (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact totalDegree_chartNumerator_le_two_mul c θ hR hd hs
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))

/-- The agreement cut with `τ = 2 s d - 1` has degree at most `2 s d h`.

Here `s, d ≥ 1`, the target `T` has degree at most `s`, and `h` bounds the `(Y, Z)`-degree. -/
theorem totalDegree_chartAgreementCut_le (c : E) (θ : κ → Polynomial E)
    {R : MvPolynomial AffineVar E} {s d h : ℕ} (hR : R.weightedTotalDegree affineYZWeight ≤ h)
    (hd : 1 ≤ d) (hs : 1 ≤ s) (Λ : Polynomial E →ₗ[E] E) {T : MvPolynomial (ChartVar κ) E}
    (hT : T.totalDegree ≤ s) :
    (chartAgreementCut c θ R s d (2 * s * d - 1) Λ T).totalDegree ≤ 2 * s * d * h := by
  refine (totalDegree_sub _ _).trans
    (max_le (totalDegree_chartFunctionalCut_le c θ hR hd hs Λ) ?_)
  have hsd : 1 ≤ s * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : 2 * s * d = 2 * (s * d) := Nat.mul_assoc _ _ _
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rw [chartSeparant_eq_zero c θ hR, zero_pow (by omega), mul_zero, totalDegree_zero]
    exact Nat.zero_le _
  refine (totalDegree_mul _ _).trans ?_
  have hpow := (totalDegree_pow (chartSeparant c θ R) (2 * s * d - 1)).trans
    (Nat.mul_le_mul_left _ (totalDegree_chartSeparant_le c θ hR))
  have := two_mul_sub_one_mul_sub_one_add_le (s := s) (d := d) (a := s) hh (by nlinarith)
  omega

/-- For positive `s` and `d`, the Reed–Solomon cut with `τ = 2 s d - 1` has degree `≤ 2 s d h`.

Here `h` bounds the `(Y, Z)`-degree of `R`. -/
theorem totalDegree_affineChartCut_le (c : E) {R : MvPolynomial AffineVar E} {s d h : ℕ}
    (hR : R.weightedTotalDegree affineYZWeight ≤ h) (hd : 1 ≤ d) (hs : 1 ≤ s) (x u v : E) :
    (affineChartCut c R s d (2 * s * d - 1) x u v).totalDegree ≤ 2 * s * d * h := by
  refine totalDegree_chartAgreementCut_le c affineFamily hR hd hs _ ?_
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, Nat.add_zero]
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])

end ReedSolomon
