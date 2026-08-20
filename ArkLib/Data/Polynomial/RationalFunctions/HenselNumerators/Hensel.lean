/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Setup
/-!
# The Hensel Lift

Appendix A.4 of [BCIKS20]: the formal Hensel/Newton iteration producing coefficients `αₜ` with
`α₀ = T/W` and `R(x₀ + S, γ, Z) = 0` for `γ = ∑ₜ αₜ Sᵗ`, its uniqueness, and the regularity half of
that the cleared residual `βₜ₊₁ = -(residual · W^{t+2} ξ^{eₜ₊₁-1} W^{d-2})` is regular.

Everything is expressed in the local coordinate `S = X - x₀`: the shift lives on `R`
(`liftCoeffToPowerSeries` sends `X ↦ x₀ + S`), not on `γ`, matching `γ ∈ L[[X - x₀]]`.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions
noncomputable section HenselLift

namespace HenselNumerators

variable {F : Type} [Field F] {R : F[X][X][Y]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
/-- The exponent of `ξ` in the denominator of the `t`-th Hensel coefficient.

The paper separates `t = 0`, where no `ξ` factor appears, from `t ≥ 1`, where the exponent is
`2*t - 1`. -/
def henselDenominatorExponent (t : ℕ) : ℕ :=
  if t = 0 then 0 else 2 * t - 1

/-- `e₀ = 0`. -/
@[simp]
lemma henselDenominatorExponent_zero : henselDenominatorExponent 0 = 0 := by
  simp [henselDenominatorExponent]

/-- `eₜ₊₁ = 2(t+1) - 1`, i.e. the exponent is `2t-1` from `t = 1` on. -/
@[simp]
lemma henselDenominatorExponent_succ (t : ℕ) :
    henselDenominatorExponent (t + 1) = 2 * (t + 1) - 1 := by
  simp [henselDenominatorExponent]

/-- A total degree for the trivariate polynomial `R`, represented as a polynomial in `Y` with
bivariate coefficients in the `Z` and `X` variables. -/
def trivariateTotalDegree (R : F[X][X][Y]) : ℕ :=
  R.support.sup (fun i => Bivariate.totalDegree (R.coeff i) + i)

/-- Each coefficient of `R` is bounded by `trivariateTotalDegree R`. -/
lemma coeff_totalDegree_add_index_le_trivariateTotalDegree (R : F[X][X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ trivariateTotalDegree R := by
  classical
  unfold trivariateTotalDegree
  exact Finset.le_sup (f := fun i => Bivariate.totalDegree (R.coeff i) + i) hi

/-- A canonical degree bound large enough for both `H` and all coefficients of `R`. -/
def defaultDegreeBound (R : F[X][X][Y]) (H : F[X][Y]) : ℕ :=
  max (Bivariate.totalDegree H) (trivariateTotalDegree R)

/-- `defaultDegreeBound` dominates the total degree of `H`, as A.4 requires of `D`. -/
lemma defaultDegreeBound_ge_H (R : F[X][X][Y]) (H : F[X][Y]) :
    Bivariate.totalDegree H ≤ defaultDegreeBound R H :=
  le_max_left _ _

/-- `defaultDegreeBound` dominates `R` trivariately, as A.4 requires of `D`. -/
lemma defaultDegreeBound_ge_R_coeff (R : F[X][X][Y]) (H : F[X][Y]) {i : ℕ}
    (hi : i ∈ R.support) :
    Bivariate.totalDegree (R.coeff i) + i ≤ defaultDegreeBound R H :=
  (coeff_totalDegree_add_index_le_trivariateTotalDegree R hi).trans (le_max_right _ _)

/-- Coefficients in `F[Z][X]` evaluated as power series over the function field: `Z` is sent to
the function-field coefficient embedding, and the `X` variable is sent to `x₀ + S`, where `S` is
the power-series variable. This realizes the local coordinate `S = X - x₀`, so
that a root condition becomes an identity in `𝕃 H⟦S⟧ = L[[X - x₀]]`. -/
noncomputable def liftCoeffToPowerSeries (x₀ : F) (H : F[X][Y]) :
    F[X][X] →+* PowerSeries (𝕃 H) :=
  Polynomial.eval₂RingHom (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
    (PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X)

/-- Evaluation of the trivariate polynomial `R(X,Y,Z)` at a power series `Γ` for the `Y`
variable, with the `X` variable interpreted as `x₀ + S` (`S` the power-series variable, i.e. the
local coordinate `X - x₀`) and `Z` interpreted in the function field of `H`. -/
noncomputable def evalRAtPowerSeries (x₀ : F) (H : F[X][Y]) (R : F[X][X][Y])
    (Γ : PowerSeries (𝕃 H)) : PowerSeries (𝕃 H) :=
  Polynomial.eval₂ (liftCoeffToPowerSeries x₀ H) Γ R

/-- The coefficient sequence obtained from a candidate sequence of regular numerators. -/
noncomputable def alphaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (βseq t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (xi x₀ R H hHyp)) ^
      henselDenominatorExponent t)

/-- The local power series `γ = ∑ αₜ Sᵗ` induced by a candidate sequence of regular numerators,
where `S = X - x₀` is the local coordinate. The `x₀`-shift is carried by
`evalRAtPowerSeries` (`X ↦ x₀ + S`), not by `γ`, matching the paper's `γ ∈ L[[X - x₀]]`. -/
noncomputable def gammaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) :
    PowerSeries (𝕃 H) :=
  PowerSeries.mk (alphaOfNumerators x₀ R H hHyp βseq)

/-- A numerator sequence has the semantic content required of a Hensel lift: it gives the Hensel
lift starting at `T / W`, and the induced power series is a root of `R(x₀ + S, ·, Z)`. -/
def IsHenselNumeratorSequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) : Prop :=
  alphaOfNumerators x₀ R H hHyp βseq 0 =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
    evalRAtPowerSeries x₀ H R (gammaOfNumerators x₀ R H hHyp βseq) = 0

/-- Specializing `X = x₀` cannot raise the total degree: a trivariate bound on `R` gives the same
bound on `R(x₀,·,Z)`. -/
theorem evalX_totalDegree_le_of_coeff_bound (x₀ : F) (R : F[X][X][Y]) {D : ℕ}
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D) :
    Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D := by
  classical
  unfold Bivariate.totalDegree
  refine Finset.sup_le ?_
  intro i hi
  have hcoeff_eval_ne : (Bivariate.evalX (Polynomial.C x₀) R).coeff i ≠ 0 :=
    Polynomial.mem_support_iff.mp hi
  have hcoeff_eq : (Bivariate.evalX (Polynomial.C x₀) R).coeff i =
      (R.coeff i).eval (Polynomial.C x₀) := by
    simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
  have hRcoeff_ne : R.coeff i ≠ 0 := by
    intro h0
    apply hcoeff_eval_ne
    rw [hcoeff_eq, h0]
    simp
  have hiR : i ∈ R.support := Polynomial.mem_support_iff.mpr hRcoeff_ne
  have heval_deg : ((Bivariate.evalX (Polynomial.C x₀) R).coeff i).natDegree ≤
      Bivariate.totalDegree (R.coeff i) := by
    rw [hcoeff_eq]
    have hP : (Polynomial.C x₀ : F[X]).natDegree ≤ 1 - 1 := by
      simp [Polynomial.natDegree_C]
    have hle := Bivariate.degree_eval_le_weightedDegree (Q := R.coeff i)
      (P := Polynomial.C x₀) (k := 1) hP
    have hw_le_total : Bivariate.natWeightedDegree (R.coeff i) 1 (1 - 1) ≤
        Bivariate.totalDegree (R.coeff i) := by
      unfold Bivariate.natWeightedDegree Bivariate.totalDegree
      simp only [Nat.sub_self, one_mul, zero_mul, add_zero]
      refine Finset.sup_le ?_
      intro j hj
      have hsup : ((R.coeff i).coeff j).natDegree + j ≤
          (R.coeff i).support.sup (fun m => ((R.coeff i).coeff m).natDegree + m) :=
        Finset.le_sup (s := (R.coeff i).support)
          (f := fun m => ((R.coeff i).coeff m).natDegree + m) hj
      exact le_trans (Nat.le_add_right ((R.coeff i).coeff j).natDegree j) hsup
    exact hle.trans hw_le_total
  have hD := hD_R i hiR
  omega

/-- The local power series `γ = ∑ αₜ Sᵗ ∈ 𝕃 H⟦S⟧`, where `S = X - x₀` is the local coordinate
in the local coordinate. The `x₀`-shift lives in `evalRAtPowerSeries` (`X ↦ x₀ + S`), not in
`γ` itself, matching the paper's `γ ∈ L[[X - x₀]]`. -/
noncomputable def gammaFromAlpha (H : F[X][Y]) (αseq : ℕ → 𝕃 H) :
    PowerSeries (𝕃 H) :=
  PowerSeries.mk αseq

/-- `βseq` presents `αseq`: every `αₜ` is `βₜ / (W^{t+1} ξ^{eₜ})`.  This is the *shape* of the
coefficients, separated from the semantic content in `IsHenselNumeratorSequence`. -/
def HasNumeratorShape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H) : Prop :=
  ∀ t : ℕ, alphaOfNumerators x₀ R H hHyp βseq t = αseq t

/-- The base case: `β₀ = T`.  From `α₀ = T/W` and the shape `α₀ = β₀/W`, the
numerator is forced to be the image of the polynomial variable. -/
theorem beta_zero_eq_X_of_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (_hD_H : Bivariate.totalDegree H ≤ D)
    (_hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (_hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    βseq 0 =
      (Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.X : F[X][Y]) : 𝒪 H) := by
  classical
  apply embeddingOf𝒪Into𝕃_injective hH
  have h0 := hshape 0
  unfold alphaOfNumerators at h0
  simp only [henselDenominatorExponent_zero, pow_zero, mul_one, zero_add, pow_one] at h0
  rw [hα0] at h0
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  field_simp [hW] at h0
  rw [embeddingOf𝒪Into𝕃_mk, liftBivariate_X]
  exact h0

/-- A product of power series vanishes in degrees below the sum of the two orders. -/
theorem coeff_mul_eq_zero_of_orders {A : Type} [CommRing A] {m : ℕ}
    (u v : PowerSeries A) (a b : ℕ)
    (hab : m < a + b) (hu : ∀ i < a, PowerSeries.coeff i u = 0)
    (hv : ∀ i < b, PowerSeries.coeff i v = 0) :
    PowerSeries.coeff m (u * v) = 0 := by
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hsum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
  rcases lt_or_ge p.1 a with h1 | h1
  · rw [hu p.1 h1, zero_mul]
  · have : p.2 < b := by omega
    rw [hv p.2 this, mul_zero]

/-- If `δ` has order at least `n`, then the `n`-th coefficient of `P · δ` sees only the constant
term of `P`. -/
theorem coeff_mul_of_low_order {A : Type} [CommRing A] (n : ℕ) (P δ : PowerSeries A)
    (hδ : ∀ i < n, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff n (P * δ) = PowerSeries.constantCoeff P * PowerSeries.coeff n δ := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (0, n)]
  · simp [PowerSeries.coeff_zero_eq_constantCoeff]
  · intro b hb hbne
    have hmem : b.1 + b.2 = n := Finset.mem_antidiagonal.mp hb
    have hb2 : b.2 < n := by
      rcases Nat.eq_zero_or_pos b.1 with h | h
      · exfalso; apply hbne; ext
        · simp [h]
        · simp; omega
      · omega
    rw [hδ b.2 hb2, mul_zero]
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by simp)) h

/-- Taylor's theorem to first order for `eval₂` at a power-series argument: perturbing `Γ` by a `δ`
of order `≥ n` changes `p(Γ)` by `p'(Γ)·δ` up to terms of order `≥ 2n`.  This is what makes the
Hensel step linear in the new coefficient. -/
theorem remainder_low_order {A B : Type} [CommRing A] [CommRing B] (n : ℕ)
    (φ : A →+* PowerSeries B)
    (Γ δ : PowerSeries B) (hδ : ∀ i < n, PowerSeries.coeff i δ = 0) (p : A[X]) :
    ∀ i < 2 * n, PowerSeries.coeff i
      (Polynomial.eval₂ φ (Γ + δ) p - Polynomial.eval₂ φ Γ p
        - Polynomial.eval₂ φ Γ (Polynomial.derivative p) * δ) = 0 := by
  induction p using Polynomial.induction_on with
  | C a =>
      intro i hi
      simp [Polynomial.derivative_C]
  | add p q hp hq =>
      intro i hi
      have e1 := hp i hi
      have e2 := hq i hi
      simp only [Polynomial.eval₂_add, add_mul, map_sub, map_add] at *
      linear_combination e1 + e2
  | monomial m a hp =>
      intro i hi
      set q : A[X] := Polynomial.C a * Polynomial.X ^ m with hq_def
      have hmulX : Polynomial.C a * Polynomial.X ^ (m+1) = q * Polynomial.X := by
        rw [hq_def]; ring
      rw [hmulX]
      have hderiv : Polynomial.derivative (q * Polynomial.X)
          = Polynomial.derivative q * Polynomial.X + q := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_X, mul_one]
      rw [hderiv]
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_add]
      set u := Polynomial.eval₂ φ Γ q with hu_def
      set up := Polynomial.eval₂ φ (Γ + δ) q with hup_def
      set d := Polynomial.eval₂ φ Γ (Polynomial.derivative q) with hd_def
      have hrewrite : up * (Γ + δ) - u * Γ - (d * Γ + u) * δ
          = d * (δ * δ) + (up - u - d * δ) * (Γ + δ) := by ring
      rw [hrewrite, map_add]
      have h1 : PowerSeries.coeff i (d * (δ * δ)) = 0 := by
        apply coeff_mul_eq_zero_of_orders d (δ * δ) 0 (2*n) (by omega)
        · intro j hj; omega
        · intro j hj
          exact coeff_mul_eq_zero_of_orders δ δ n n (by omega) hδ hδ
      have h2 : PowerSeries.coeff i ((up - u - d * δ) * (Γ + δ)) = 0 := by
        apply coeff_mul_eq_zero_of_orders (up - u - d * δ) (Γ + δ) (2*n) 0 (by omega)
        · intro j hj; exact hp j hj
        · intro j hj; omega
      rw [h1, h2, add_zero]



omit H_irreducible H_natDegree_pos in
/-- The constant term of a lifted coefficient is its specialization at `X = x₀`. -/
theorem constantCoeff_liftCoeffToPowerSeries (x₀ : F) (p : F[X][X]) :
    PowerSeries.constantCoeff (liftCoeffToPowerSeries x₀ H p) =
      liftToFunctionField (H := H) (p.eval (Polynomial.C x₀)) := by
  unfold liftCoeffToPowerSeries
  rw [coe_eval₂RingHom, Polynomial.hom_eval₂]
  have hconst : RingHom.comp (PowerSeries.constantCoeff (R := 𝕃 H))
      (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
      = liftToFunctionField (H := H) := by
    refine RingHom.ext fun z => ?_
    simp
  rw [hconst]
  have hs : PowerSeries.constantCoeff (R := 𝕃 H)
      (PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X) = fieldTo𝕃 (H := H) x₀ := by
    simp
  rw [hs]
  have : fieldTo𝕃 (H := H) x₀ = liftToFunctionField (H := H) (Polynomial.C x₀) := rfl
  rw [this, Polynomial.eval₂_hom]

omit H_irreducible H_natDegree_pos in
/-- Constant terms commute with `eval₂`: evaluating `R` at a power series and taking the constant
term is evaluating `R(x₀,·,Z)` at the constant term. -/
theorem constantCoeff_eval₂_liftCoeff (x₀ : F) (q : F[X][X][Y]) (Γ : PowerSeries (𝕃 H)) :
    PowerSeries.constantCoeff (Polynomial.eval₂ (liftCoeffToPowerSeries x₀ H) Γ q) =
      Polynomial.eval₂ (liftToFunctionField (H := H))
        (PowerSeries.constantCoeff Γ) (Bivariate.evalX (Polynomial.C x₀) q) := by
  rw [Polynomial.hom_eval₂]
  rw [Bivariate.evalX_eq_map, Polynomial.eval₂_map]
  congr 1
  refine RingHom.ext fun p => ?_
  change PowerSeries.constantCoeff (liftCoeffToPowerSeries x₀ H p) = _
  rw [constantCoeff_liftCoeffToPowerSeries]
  rfl

-- constantCoeff of derivative eval = ζ when constantCoeff Γ = T/W
/-- The constant term of `∂R/∂Y` evaluated at any `Γ` starting from `T/W` is exactly `ζ`.  This is
why `ζ` is the coefficient of the new unknown at every Hensel step. -/
theorem constantCoeff_eval₂_derivative_eq_zeta (x₀ : F) (R : F[X][X][Y])
    (Γ : PowerSeries (𝕃 H))
    (hΓ0 : PowerSeries.constantCoeff Γ =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) :
    PowerSeries.constantCoeff
        (Polynomial.eval₂ (liftCoeffToPowerSeries x₀ H) Γ R.derivative)
      = zeta R x₀ H := by
  rw [constantCoeff_eval₂_liftCoeff, hΓ0]
  rfl



/-- **The linearity at the heart of the Hensel step.**  For `δ` of order at least `n ≥ 1`,
`coeff n (R(x₀+S, Γ+δ, Z)) = coeff n (R(x₀+S, Γ, Z)) + ζ · coeff n δ`.
Since `ζ` is invertible, the `n`-th coefficient of the lift is uniquely determined by the earlier
ones — this gives both existence (`formalHenselAlphaSequence`) and uniqueness
(`hensel_alpha_sequence_unique`). -/
theorem coeff_evalR_split (x₀ : F) (R : F[X][X][Y]) (n : ℕ) (hn : 1 ≤ n)
    (Γ δ : PowerSeries (𝕃 H)) (hδ : ∀ i < n, PowerSeries.coeff i δ = 0)
    (hΓ0 : PowerSeries.constantCoeff Γ =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) :
    PowerSeries.coeff n (evalRAtPowerSeries x₀ H R (Γ + δ)) =
      PowerSeries.coeff n (evalRAtPowerSeries x₀ H R Γ)
        + zeta R x₀ H * PowerSeries.coeff n δ := by
  unfold evalRAtPowerSeries
  have hrem := remainder_low_order n (liftCoeffToPowerSeries x₀ H) Γ δ hδ R n (by omega)
  rw [map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at hrem
  rw [hrem, coeff_mul_of_low_order n _ δ hδ,
    constantCoeff_eval₂_derivative_eq_zeta x₀ R Γ hΓ0, add_comm]

-- base case n=0
omit H_irreducible H_natDegree_pos in
/-- The constant term of `R(x₀+S, Γ, Z)` is `R(x₀,·,Z)` evaluated at the constant term of `Γ`. -/
theorem coeff_zero_evalR (x₀ : F) (R : F[X][X][Y]) (Γ : PowerSeries (𝕃 H)) :
    PowerSeries.coeff 0 (evalRAtPowerSeries x₀ H R Γ) =
      Polynomial.eval₂ (liftToFunctionField (H := H)) (PowerSeries.constantCoeff Γ)
        (Bivariate.evalX (Polynomial.C x₀) R) := by
  unfold evalRAtPowerSeries
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_eval₂_liftCoeff]



omit H_irreducible H_natDegree_pos in
/-- Coefficients below the order of the perturbation are unchanged, so the Hensel iteration never
disturbs the coefficients it has already fixed. -/
theorem coeff_evalR_stable (x₀ : F) (R : F[X][X][Y]) (n m : ℕ) (hm : m < n)
    (Γ δ : PowerSeries (𝕃 H)) (hδ : ∀ i < n, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff m (evalRAtPowerSeries x₀ H R (Γ + δ)) =
      PowerSeries.coeff m (evalRAtPowerSeries x₀ H R Γ) := by
  unfold evalRAtPowerSeries
  have hrem := remainder_low_order n (liftCoeffToPowerSeries x₀ H) Γ δ hδ R m (by omega)
  rw [map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at hrem
  rw [hrem]
  have hz : PowerSeries.coeff m
      (Polynomial.eval₂ (liftCoeffToPowerSeries x₀ H) Γ (derivative R) * δ) = 0 := by
    apply coeff_mul_eq_zero_of_orders _ δ 0 n (by omega)
    · intro j hj; omega
    · exact hδ
  rw [hz, zero_add]


-- The recursive construction.
/-- The Hensel iteration as a sequence of finite approximations: `bSeq N` agrees with the lift up
to index `N` and is zero beyond.  Each step solves `ζ · α_{N+1} + (earlier terms) = 0`. -/
noncomputable def bSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : ℕ → (ℕ → 𝕃 H)
  | 0 => fun i => if i = 0 then
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff else 0
  | (N+1) => Function.update (bSeq x₀ R H N) (N+1)
      (- PowerSeries.coeff (N+1)
          (evalRAtPowerSeries x₀ H R (PowerSeries.mk (bSeq x₀ R H N))) / zeta R x₀ H)

/-- The diagonal of `bSeq`: the coefficient sequence of the Hensel lift. -/
noncomputable def alphaSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : ℕ → 𝕃 H :=
  fun n => bSeq x₀ R H n n

-- bSeq N agrees with bSeq (N+1) below N+1
/-- Unfolding of one iteration step. -/
theorem bSeq_succ_def (x₀ : F) (R : F[X][X][Y]) (N : ℕ) :
    bSeq x₀ R H (N+1) = Function.update (bSeq x₀ R H N) (N+1)
      (- PowerSeries.coeff (N+1)
          (evalRAtPowerSeries x₀ H R (PowerSeries.mk (bSeq x₀ R H N))) / zeta R x₀ H) := by
  rfl

/-- A step does not disturb the coefficients already computed. -/
theorem bSeq_succ_eq_below (x₀ : F) (R : F[X][X][Y]) (N i : ℕ) (hi : i < N + 1) :
    bSeq x₀ R H (N+1) i = bSeq x₀ R H N i := by
  rw [bSeq_succ_def, Function.update_apply, if_neg (by omega)]

-- value 0 is T/W for all N
/-- Every approximation starts at `α₀ = T/W`. -/
theorem bSeq_zero (x₀ : F) (R : F[X][X][Y]) (N : ℕ) :
    bSeq x₀ R H N 0 =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
  induction N with
  | zero => simp [bSeq]
  | succ N ih => rw [bSeq_succ_eq_below x₀ R N 0 (by omega), ih]



/-- Below its index, `bSeq N` agrees with the limit sequence `alphaSeq`. -/
theorem bSeq_stable (x₀ : F) (R : F[X][X][Y]) (N i : ℕ) (hi : i ≤ N) :
    bSeq x₀ R H N i = alphaSeq x₀ R H i := by
  induction N with
  | zero =>
      interval_cases i
      rfl
  | succ N ih =>
      rcases Nat.lt_or_ge i (N+1) with h | h
      · rw [bSeq_succ_eq_below x₀ R N i h]
        exact ih (by omega)
      · have : i = N + 1 := by omega
        subst this
        rfl

-- mk (bSeq N) agrees with mk (alphaSeq) at indices ≤ N
/-- Power-series form of `bSeq_stable`: the approximations agree with the limit in low degrees. -/
theorem mk_bSeq_coeff_eq (x₀ : F) (R : F[X][X][Y]) (N i : ℕ) (hi : i ≤ N) :
    PowerSeries.coeff i (PowerSeries.mk (bSeq x₀ R H N)) =
      PowerSeries.coeff i (PowerSeries.mk (alphaSeq x₀ R H)) := by
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, bSeq_stable x₀ R N i hi]



/-- Approximations vanish beyond their index. -/
theorem bSeq_eq_zero_of_gt (x₀ : F) (R : F[X][X][Y]) (N j : ℕ) (hj : N < j) :
    bSeq x₀ R H N j = 0 := by
  induction N generalizing j with
  | zero =>
      have : j ≠ 0 := by omega
      simp [bSeq, this]
  | succ N ih =>
      rw [bSeq_succ_def, Function.update_apply, if_neg (by omega)]
      exact ih j (by omega)

-- δ helper: mk (bSeq (N+1)) = mk (bSeq N) + δ with δ low order N+1
/-- Consecutive approximations differ only from degree `N+1` on, so their difference is a legal
perturbation for `coeff_evalR_split`. -/
theorem coeff_delta_below (x₀ : F) (R : F[X][X][Y]) (N i : ℕ) (hi : i < N + 1) :
    PowerSeries.coeff i
      (PowerSeries.mk (bSeq x₀ R H (N+1)) - PowerSeries.mk (bSeq x₀ R H N)) = 0 := by
  rw [map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, bSeq_succ_eq_below x₀ R N i hi,
    sub_self]

/-- The invariant of the iteration: `R(x₀+S, bSeq N, Z)` vanishes in all degrees up to `N`. -/
theorem root_bSeq (x₀ : F) (R : F[X][X][Y])
    (hinit : Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    (hzeta : zeta R x₀ H ≠ 0) :
    ∀ N, ∀ m ≤ N, PowerSeries.coeff m
      (evalRAtPowerSeries x₀ H R (PowerSeries.mk (bSeq x₀ R H N))) = 0 := by
  intro N
  induction N with
  | zero =>
      intro m hm
      interval_cases m
      rw [coeff_zero_evalR]
      have hcc : PowerSeries.constantCoeff (PowerSeries.mk (bSeq x₀ R H 0)) =
          functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, bSeq_zero]
      rw [hcc, hinit]
  | succ N ih =>
      intro m hm
      set Γ := PowerSeries.mk (bSeq x₀ R H N) with hΓ
      set δ := PowerSeries.mk (bSeq x₀ R H (N+1)) - PowerSeries.mk (bSeq x₀ R H N) with hδ_def
      have hsum : PowerSeries.mk (bSeq x₀ R H (N+1)) = Γ + δ := by rw [hδ_def]; ring
      have hδlow : ∀ i < N + 1, PowerSeries.coeff i δ = 0 := by
        intro i hi; rw [hδ_def]; exact coeff_delta_below x₀ R N i hi
      have hΓ0 : PowerSeries.constantCoeff Γ =
          functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
        rw [hΓ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, bSeq_zero]
      rw [hsum]
      rcases Nat.lt_or_ge m (N+1) with hlt | hge
      · rw [coeff_evalR_stable x₀ R (N+1) m hlt Γ δ hδlow]
        exact ih m (by omega)
      · have hmeq : m = N + 1 := by omega
        subst hmeq
        rw [coeff_evalR_split x₀ R (N+1) (by omega) Γ δ hδlow hΓ0]
        -- coeff (N+1) δ = bSeq (N+1)(N+1) - bSeq N (N+1)
        have hδval : PowerSeries.coeff (N+1) δ =
            bSeq x₀ R H (N+1) (N+1) - bSeq x₀ R H N (N+1) := by
          rw [hδ_def, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
        have hbN1 : bSeq x₀ R H N (N+1) = 0 := bSeq_eq_zero_of_gt x₀ R N (N+1) (by omega)
        have hval : bSeq x₀ R H (N+1) (N+1) =
            - PowerSeries.coeff (N+1) (evalRAtPowerSeries x₀ H R Γ) / zeta R x₀ H := by
          rw [bSeq_succ_def, Function.update_self, hΓ]
        rw [hδval, hbN1, sub_zero, hval]
        field_simp
        ring

/-- **Existence of the Hensel lift**: a coefficient sequence with `α₀ = T/W` whose
generating series is a root of `R(x₀ + S, ·, Z)`.  Built by the Newton iteration `bSeq`, whose
limit is a root in every degree.  Uniqueness is `hensel_alpha_sequence_unique`. -/
theorem formalHenselAlphaSequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hinit : Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0)
    (hzeta : zeta R x₀ H ≠ 0) :
    ∃ αseq : ℕ → 𝕃 H,
      αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0 := by
  -- Formal-Hensel / Newton iteration over the field `𝕃 H`, in the local coordinate
  -- `S = X - x₀` (so `evalRAtPowerSeries` evaluates `R` at `X ↦ x₀ + S`).
  -- Construct `αseq` coefficient-by-coefficient with `α₀ = T/W` (`hinit` is the base).
  -- Key linearity lemma: `coeff (n) (evalRAtPowerSeries x₀ H R (mk α)) = ζ * α n + c n`
  -- where `c n` depends only on `α i, i < n` (the partition expansion of A.4, in which
  -- `αₙ` first appears at degree `n` with coefficient `A₀,λ⁽ⁿ⁾ = ζ`). Since `hzeta` makes
  -- `ζ` a unit, solve `α n = -c n / ζ`, so every coefficient of `evalR` vanishes; conclude
  -- with `PowerSeries.ext`. (`𝕃 H⟦S⟧` is also Henselian, but `R` need not be monic in `Y`.)
  refine ⟨alphaSeq x₀ R H, ?_, ?_⟩
  · change bSeq x₀ R H 0 0 = _
    simp [bSeq]
  · unfold gammaFromAlpha
    ext m
    rw [map_zero]
    set α := PowerSeries.mk (alphaSeq x₀ R H) with hα
    set Γ := PowerSeries.mk (bSeq x₀ R H m) with hΓ
    set δ := α - Γ with hδ_def
    have hsum : α = Γ + δ := by rw [hδ_def]; ring
    have hδlow : ∀ i < m + 1, PowerSeries.coeff i δ = 0 := by
      intro i hi
      rw [hδ_def, map_sub, hα, hΓ, mk_bSeq_coeff_eq x₀ R m i (by omega), sub_self]
    have hstable := coeff_evalR_stable x₀ R (m+1) m (by omega) Γ δ hδlow
    rw [hsum, hstable]
    exact root_bSeq x₀ R hinit hzeta m m (le_refl m)

/-- **Uniqueness of the Hensel lift.**  Two coefficient sequences that agree at `t = 0` and both
make `γ = ∑ₜ αₜ Sᵗ` a root of `R(x₀ + S, ·, Z)` are equal.

At each step the new coefficient is determined: by `coeff_evalR_split` the `n`-th coefficient of
`R(x₀ + S, γ, Z)` is `ζ · αₙ` plus a term depending only on `αᵢ` with `i < n`, and `ζ` is
invertible, so `αₙ` is forced.

Uniqueness is what lets a lift be identified with any other solution of the same equation, which is
how one recognizes a lift as coming from a known function. -/
theorem hensel_alpha_sequence_unique (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hzeta : zeta R x₀ H ≠ 0) {αseq αseq' : ℕ → 𝕃 H}
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hα0' : αseq' 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hroot' : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq') = 0) :
    αseq = αseq' := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hα0, hα0']
    · -- `n ≥ 1`: write `γ' = γ + δ` with `δ` of order `≥ n`, then compare `n`-th coefficients.
      set Γ : PowerSeries (𝕃 H) := gammaFromAlpha H αseq with hΓdef
      set δ : PowerSeries (𝕃 H) := gammaFromAlpha H αseq' - Γ with hδdef
      have hδlow : ∀ i < n, PowerSeries.coeff i δ = 0 := by
        intro i hi
        rw [hδdef, map_sub, hΓdef, gammaFromAlpha, gammaFromAlpha, PowerSeries.coeff_mk,
          PowerSeries.coeff_mk, ih i hi, sub_self]
      have hΓ0 : PowerSeries.constantCoeff Γ =
          functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
        rw [hΓdef, gammaFromAlpha, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_mk]
        exact hα0
      have hsum : gammaFromAlpha H αseq' = Γ + δ := by rw [hδdef]; ring
      have hkey := coeff_evalR_split x₀ R n hn Γ δ hδlow hΓ0
      rw [← hsum] at hkey
      have hzero' :
          PowerSeries.coeff n (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq')) = 0 := by
        rw [hroot']; simp
      have hzero : PowerSeries.coeff n (evalRAtPowerSeries x₀ H R Γ) = 0 := by
        rw [hΓdef, hroot]; simp
      rw [hzero', hzero, zero_add] at hkey
      have hδn : PowerSeries.coeff n δ = 0 :=
        (mul_eq_zero.mp hkey.symm).resolve_left hzeta
      rw [hδdef, map_sub, hΓdef, gammaFromAlpha, gammaFromAlpha, PowerSeries.coeff_mk,
        PowerSeries.coeff_mk, sub_eq_zero] at hδn
      exact hδn.symm

/-- The two ways of forming `γ` — from numerators or from coefficients — agree once the numerators
present the coefficients. -/
theorem gammaOfNumerators_eq_gammaFromAlpha (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    gammaOfNumerators x₀ R H hHyp βseq = gammaFromAlpha H αseq := by
  unfold HasNumeratorShape at hshape
  unfold gammaOfNumerators gammaFromAlpha
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  exact hshape n

/-- The residual at step `t`: the `(t+1)`-st coefficient of `R(x₀+S, γ, Z)` with the `ζ·α_{t+1}`
term removed.  It vanishes exactly when `α_{t+1}` solves the Hensel equation, and after clearing
denominators it becomes the next numerator. -/
noncomputable def henselCoeffResidual (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (αseq : ℕ → 𝕃 H) (t : ℕ) : 𝕃 H :=
  PowerSeries.coeff (t + 1) (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) -
    zeta R x₀ H * αseq (t + 1)

/-- Packaging: numerators presenting a genuine Hensel coefficient sequence form a
`IsHenselNumeratorSequence`. -/
theorem hensel_numerator_sequence_of_alpha_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    IsHenselNumeratorSequence x₀ R H hHyp βseq := by
  unfold IsHenselNumeratorSequence
  constructor
  · rw [hshape 0]
    exact hα0
  · rw [gammaOfNumerators_eq_gammaFromAlpha x₀ R H hHyp αseq βseq hshape]
    exact hroot

/-- The defining relation of `𝕃`, in evaluated form: the class of `H̃` equals
`W^{dH-1} · H(T/W)`. -/
theorem mk_monicizeRatFunc_eq_leadingCoeff_pow_mul_eval₂ (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)] :
    (Ideal.Quotient.mk (Ideal.span ({monicizeRatFunc H} : Set (Polynomial (RatFunc F))))
        (monicizeRatFunc H) : 𝕃 H)
        =
      liftToFunctionField (H := H) H.leadingCoeff ^ (H.natDegree - 1) *
        Polynomial.eval₂ (liftToFunctionField (H := H))
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H := by
  unfold liftToFunctionField functionFieldT coeffAsRatFunc
  unfold monicizeRatFunc
  simp only [Polynomial.coeff_natDegree, ToRatFunc.bivPolyHom, Polynomial.coe_mapRingHom,
    Polynomial.map_C, RingHom.comp_apply]
  let Wp : Polynomial (RatFunc F) := Polynomial.C (univPolyHom (F := F) H.leadingCoeff)
  let I : Ideal (Polynomial (RatFunc F)) := Ideal.span
      ({Wp ^ (H.natDegree - 1) * Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F)))
          (Polynomial.X / Wp) H} : Set (Polynomial (RatFunc F)))
  let q : Polynomial (RatFunc F) →+* 𝕃 H := Ideal.Quotient.mk I
  have hW_ne : univPolyHom (F := F) H.leadingCoeff ≠ 0 := by
    intro h
    exact
        (Polynomial.leadingCoeff_ne_zero.mpr
            (Polynomial.ne_zero_of_natDegree_gt _H_natDegree_pos.out))
      (univPolyHom_injective (F := F) (by simpa using h))
  have hdiv : q (Polynomial.X / Wp) = q Polynomial.X / q Wp := by
    dsimp [Wp]
    rw [Polynomial.div_C]
    rw [map_mul]
    rw [div_eq_mul_inv]
    congr 1
    have hmul : q (Polynomial.C (univPolyHom (F := F) H.leadingCoeff)) *
        q (Polynomial.C ((univPolyHom (F := F) H.leadingCoeff)⁻¹)) = 1 := by
      rw [← map_mul, ← Polynomial.C_mul]
      rw [mul_inv_cancel₀ hW_ne]
      exact map_one q
    exact (inv_eq_of_mul_eq_one_right hmul).symm
  change q
      (Wp ^ (H.natDegree - 1) * Polynomial.eval₂ (RingHom.comp Polynomial.C (univPolyHom (F := F)))
          (Polynomial.X / Wp) H) = q Wp ^ (H.natDegree - 1) * Polynomial.eval₂
          (q.comp ((Polynomial.mapRingHom (univPolyHom (F := F))).comp Polynomial.C))
          (q Polynomial.X / q Wp) H
  rw [map_mul, map_pow]
  rw [← hdiv]
  rw [Polynomial.hom_eval₂]
  have hhom : q.comp
      (RingHom.comp Polynomial.C (univPolyHom (F := F)) : F[X] →+* Polynomial (RatFunc F)) =
      q.comp ((Polynomial.mapRingHom (univPolyHom (F := F))).comp Polynomial.C) := by
    ext p <;> simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
  rw [hhom]

/-- `Y = T/W` is a root of `H` in `𝕃`. -/
theorem H_eval2_T_div_W_eq_zero (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)] :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) H = 0 := by
  have hzero :
      (Ideal.Quotient.mk (Ideal.span ({monicizeRatFunc H} : Set (Polynomial (RatFunc F))))
          (monicizeRatFunc H) : 𝕃
          H) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  rw [mk_monicizeRatFunc_eq_leadingCoeff_pow_mul_eval₂] at hzero
  have hW : liftToFunctionField (H := H) H.leadingCoeff ^ (H.natDegree - 1) ≠ 0 := by
    exact pow_ne_zero _ (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  exact (mul_eq_zero.mp hzero).resolve_left hW

/-- `α₀ = T/W` is a root of `R(x₀,·,Z)`, since `H` divides it.  This is the base of the lift. -/
theorem initial_root_at_x0 (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    Polynomial.eval₂ (liftToFunctionField (H := H))
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
      (Bivariate.evalX (Polynomial.C x₀) R) = 0 := by
  classical
  rcases hHyp.dvd_evalX with ⟨Q, hQ⟩
  rw [hQ, Polynomial.eval₂_mul]
  rw [H_eval2_T_div_W_eq_zero H, zero_mul]

/-- `ζ ≠ 0`, i.e. `α₀` is a *simple* root — this is exactly where separability of `R(x₀,·,Z)` is
used, and it is what makes the Hensel step solvable. -/
theorem zeta_ne_zero_of_hypotheses (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    zeta R x₀ H ≠ 0 := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  let t : 𝕃 H := functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff
  have hroot : Polynomial.eval₂ (liftToFunctionField (H := H)) t P = 0 := by
    simpa [P, t] using initial_root_at_x0 x₀ R H hHyp
  have hderiv_evalX : Bivariate.evalX (Polynomial.C x₀) R.derivative = P.derivative := by
    ext i
    simp [P, derivative_evalX_coeff, Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
  -- `liftToFunctionField` factors through `F(Z)`, so fraction-field separability is enough here.
  set ψ : RatFunc F →+* 𝕃 H :=
    (Ideal.Quotient.mk (Ideal.span {monicizeRatFunc H})).comp
      (Polynomial.C : RatFunc F →+* Polynomial (RatFunc F)) with hψ
  have hfactor : (liftToFunctionField (H := H)) = ψ.comp (univPolyHom (F := F)) :=
    RingHom.ext fun c => by
      simp only [hψ, RingHom.comp_apply, liftToFunctionField, coeffAsRatFunc,
        ToRatFunc.bivPolyHom, Polynomial.coe_mapRingHom, Polynomial.map_C]
  have hroot' : Polynomial.eval₂ ψ t (P.map (univPolyHom (F := F))) = 0 := by
    rw [Polynomial.eval₂_map, ← hfactor]; exact hroot
  have hne : Polynomial.eval₂ (liftToFunctionField (H := H)) t P.derivative ≠ 0 := by
    have hsep := hHyp.separable_evalX.eval₂_derivative_ne_zero ψ hroot'
    rw [Polynomial.derivative_map, Polynomial.eval₂_map, ← hfactor] at hsep
    exact hsep
  simpa [zeta, P, t, hderiv_evalX] using hne

/-- `formalHenselAlphaSequence` with its two hypotheses discharged from `Hypotheses`. -/
theorem exists_hensel_alpha_sequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    ∃ αseq : ℕ → 𝕃 H,
      αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff ∧
      evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0 := by
  exact formalHenselAlphaSequence x₀ R H (initial_root_at_x0 x₀ R H hHyp)
      (zeta_ne_zero_of_hypotheses x₀ R H hHyp)

/-- Predicate: all coefficients of a power series over `𝕃 H` are regular (lie in the image of
`𝒪 H`). This abstracts the "regular power series" used throughout the Hensel clearing argument. -/
def AllCoeffRegular (H : F[X][Y]) (φ : PowerSeries (𝕃 H)) : Prop :=
  ∀ n, PowerSeries.coeff n φ ∈ regularElementsSet H

/-- Coefficientwise regularity is closed under addition. -/
theorem AllCoeffRegular.add {H : F[X][Y]} {φ ψ : PowerSeries (𝕃 H)}
    (hφ : AllCoeffRegular H φ) (hψ : AllCoeffRegular H ψ) :
    AllCoeffRegular H (φ + ψ) := by
  intro n; rw [map_add]; exact regularElementsSet_add (hφ n) (hψ n)

/-- Coefficientwise regularity is closed under multiplication (Cauchy product). -/
theorem AllCoeffRegular.mul {H : F[X][Y]} {φ ψ : PowerSeries (𝕃 H)}
    (hφ : AllCoeffRegular H φ) (hψ : AllCoeffRegular H ψ) :
    AllCoeffRegular H (φ * ψ) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply regularElementsSet_sum
  intro p _
  exact regularElementsSet_mul (hφ p.1) (hψ p.2)

/-- Coefficientwise regularity is closed under powers. -/
theorem AllCoeffRegular.pow {H : F[X][Y]} {φ : PowerSeries (𝕃 H)}
    (hφ : AllCoeffRegular H φ) (m : ℕ) :
    AllCoeffRegular H (φ ^ m) := by
  induction m with
  | zero =>
      intro n; rw [pow_zero, PowerSeries.coeff_one]; split
      · exact regularElementsSet_one H
      · exact regularElementsSet_zero H
  | succ m ih => rw [pow_succ]; exact ih.mul hφ

/-- A constant series with regular value has regular coefficients. -/
theorem AllCoeffRegular.const {H : F[X][Y]} {c : 𝕃 H} (hc : c ∈ regularElementsSet H) :
    AllCoeffRegular H (PowerSeries.C c) := by
  intro n; rw [PowerSeries.coeff_C]; split
  · exact hc
  · exact regularElementsSet_zero H

/-- The power-series variable has regular coefficients (`0` and `1`). -/
theorem AllCoeffRegular.X {H : F[X][Y]} : AllCoeffRegular H (PowerSeries.X) := by
  intro n; rw [PowerSeries.coeff_X]; split
  · exact regularElementsSet_one H
  · exact regularElementsSet_zero H

/-- The zero series has regular coefficients. -/
theorem AllCoeffRegular.zero {H : F[X][Y]} :
    AllCoeffRegular H (0 : PowerSeries (𝕃 H)) := by
  intro n; rw [map_zero]; exact regularElementsSet_zero H

/-- The image of a field constant `x₀ : F` in `𝕃 H` is a regular element. -/
theorem fieldTo𝕃_regular (x₀ : F) (H : F[X][Y]) :
    fieldTo𝕃 (H := H) x₀ ∈ regularElementsSet H := by
  change RingHom.comp liftToFunctionField Polynomial.C x₀ ∈ regularElementsSet H
  rw [RingHom.comp_apply]
  exact regularElementsSet_liftToFunctionField H _

/-- Every coefficient of `liftCoeffToPowerSeries x₀ H p` is regular: the construction only uses
`liftToFunctionField`-images of `F[X]`-coefficients, the regular constant `x₀`, and the
power-series variable, all of which preserve regularity. -/
theorem coeff_liftCoeff_regular (x₀ : F) (H : F[X][Y]) (p : F[X][X]) :
    AllCoeffRegular H (liftCoeffToPowerSeries x₀ H p) := by
  classical
  have heq : liftCoeffToPowerSeries x₀ H p =
      Polynomial.eval₂ (RingHom.comp PowerSeries.C (liftToFunctionField (H := H)))
        (PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X) p := rfl
  rw [heq, Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_induction _ (AllCoeffRegular H) (fun _ _ => AllCoeffRegular.add)
    AllCoeffRegular.zero
  intro m _
  apply AllCoeffRegular.mul
  · rw [RingHom.comp_apply]
    exact AllCoeffRegular.const (regularElementsSet_liftToFunctionField H _)
  · exact AllCoeffRegular.pow
      ((AllCoeffRegular.const (fieldTo𝕃_regular x₀ H)).add AllCoeffRegular.X) m

/-- **Residual simplification** (paper A.4): replacing `αseq` by its truncation `αtrunc i =
if i ≤ t then αseq i else 0` cancels the linear term `ζ · αseq (t+1)` exactly. Hence the Hensel
residual at step `t` equals the `(t+1)`-st coefficient of `R` evaluated at the *truncated*
power series. This uses only the splitting lemma `coeff_evalR_split`; `hroot` is not needed. -/
theorem henselCoeffResidual_eq_trunc (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (t : ℕ) :
    henselCoeffResidual x₀ R H αseq t =
      PowerSeries.coeff (t + 1)
        (evalRAtPowerSeries x₀ H R
          (PowerSeries.mk (fun i => if i ≤ t then αseq i else 0))) := by
  classical
  unfold henselCoeffResidual gammaFromAlpha
  set αtrunc : ℕ → 𝕃 H := fun i => if i ≤ t then αseq i else 0 with hαtrunc
  set δ : PowerSeries (𝕃 H) := PowerSeries.mk αseq - PowerSeries.mk αtrunc with hδ_def
  have hsum : PowerSeries.mk αseq = PowerSeries.mk αtrunc + δ := by rw [hδ_def]; ring
  have hδlow : ∀ i < t + 1, PowerSeries.coeff i δ = 0 := by
    intro i hi
    rw [hδ_def, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, hαtrunc]
    simp only []
    rw [if_pos (by omega)]; ring
  have hδtop : PowerSeries.coeff (t + 1) δ = αseq (t + 1) := by
    rw [hδ_def, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, hαtrunc]
    simp only []
    rw [if_neg (by omega)]; ring
  have hΓ0 : PowerSeries.constantCoeff (PowerSeries.mk αtrunc) =
      functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hαtrunc]
    simp only []
    rw [if_pos (by omega), hα0]
  rw [hsum, coeff_evalR_split x₀ R (t + 1) (by omega) (PowerSeries.mk αtrunc) δ hδlow hΓ0,
    hδtop]
  ring

/-- **Per-degree clearing lemma** (paper A.4 core combinatorial bound).

For the truncated power series `g = mk αtrunc` whose nonzero coefficients (`i ≤ t`) have the
Hensel shape `αtrunc i = embeddingOf𝒪Into𝕃 (βprev ⟨i⟩) / (W^{i+1} · eta^{e_i})` with `βprev`
regular and `e_i = henselDenominatorExponent i`, each degree-`j` summand of the expansion of
`coeff (t+1) (eval₂ liftCoeff g R)`, after multiplication by the global clearing denominator
`Ddiv = W^{t+2} · eta^{E-1} · W^{d-2}`, is a regular element.

This is the combinatorial heart of the regularity argument. The denominator of a
partition term with `∑ iₗ = b ≤ t+1` over `j` parts is `W^{b+j} · eta^{∑ e_{iₗ}}`; the
exponent bounds `∑ e_{iₗ} ≤ E-1 = 2t` and (for `b ≤ t`) `b+j ≤ t+d` make the leftover `W`/`eta`
powers nonnegative. The single boundary case `a = 0, b = t+1, j = R.natDegree` has a one-`W`
deficit covered by the leading-coefficient divisibility `leadingCoeff_dvd_evalX_coeff_natDegree`
(the coefficient `coeff 0 (liftCoeff (R.coeff d))` is `liftToFunctionField` of the top
coefficient of `R(x₀,·)`, which is divisible by `W`). The leftover `eta = W^{d-2}·ζ` factors
and `embeddingOf𝒪Into𝕃_xi` close the regularity. -/
theorem henselClearedTerm_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (αtrunc : ℕ → 𝕃 H)
    (hshape : ∀ i : ℕ, αtrunc i =
      if h : i ≤ t then
        embeddingOf𝒪Into𝕃 H (βprev ⟨i, by omega⟩) /
          (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
            (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ henselDenominatorExponent i)
      else 0)
    (j : ℕ) (hj : j ∈ Finset.range (R.natDegree + 1)) :
    PowerSeries.coeff (t + 1)
        (liftCoeffToPowerSeries x₀ H (R.coeff j) * (PowerSeries.mk αtrunc) ^ j) *
      (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
        (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ (henselDenominatorExponent (t + 1) - 1) *
        liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2)) ∈
      regularElementsSet H := by
  classical
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) with hetadef
  have hWne : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have hetane : eta ≠ 0 := by
    rw [hetadef, embeddingOf𝒪Into𝕃_xi]
    exact mul_ne_zero (pow_ne_zero _ hWne) (zeta_ne_zero_of_hypotheses x₀ R H hHyp)
  have hjle : j ≤ R.natDegree := by
    rw [Finset.mem_range] at hj; omega
  -- regularity of cleared numerators (clearing the denominator of each `αtrunc i`, `i ≤ t`)
  have hnumReg : ∀ i, i ≤ t →
      αtrunc i * (W ^ (i + 1) * eta ^ henselDenominatorExponent i) ∈ regularElementsSet H := by
    intro i hi
    rw [hshape i, dif_pos hi, hWdef, hetadef,
      div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hWne) (pow_ne_zero _ hetane))]
    exact ⟨βprev ⟨i, by omega⟩, rfl⟩
  -- `αtrunc` vanishes above the truncation point
  have hαzero : ∀ i, t < i → αtrunc i = 0 := by
    intro i hi; rw [hshape i, dif_neg (by omega)]
  -- Step: distribute `coeff_mul` and `coeff_pow`, reduce to a single composition `l`.
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply regularElementsSet_sum
  intro p _hp
  rw [PowerSeries.coeff_pow]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply regularElementsSet_sum
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  have hbsum : (∑ i ∈ Finset.range j, l i) = p.2 := hl.1
  have hcoeffReg : PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j))
      ∈ regularElementsSet H := coeff_liftCoeff_regular x₀ H (R.coeff j) p.1
  have hab : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp _hp
  -- Case A: some part exceeds `t`  ⇒  the product has a zero factor.
  by_cases hbig : ∃ i ∈ Finset.range j, t < l i
  · obtain ⟨i₀, hi₀, hi₀t⟩ := hbig
    have hz : (∏ i ∈ Finset.range j, αtrunc (l i)) = 0 :=
      Finset.prod_eq_zero hi₀ (hαzero _ hi₀t)
    rw [hz]
    simp
  · -- Case B: all parts `≤ t`.
    push Not at hbig
    have hle : ∀ i ∈ Finset.range j, l i ≤ t := hbig
    -- product-clearing: `(∏ αtrunc) · W^{∑(lᵢ+1)} · eta^{∑e} ∈ regular`
    have hprodReg : (∏ i ∈ Finset.range j, αtrunc (l i)) *
        (W ^ (∑ i ∈ Finset.range j, (l i + 1)) *
          eta ^ (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)))
        ∈ regularElementsSet H := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact regularElementsSet_prod _ fun i hi => hnumReg (l i) (hle i hi)
    -- the eta exponent bound `∑ e ≤ E - 1 = 2t`
    have hPe : (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)) ≤
        henselDenominatorExponent (t + 1) - 1 := by
      set Pe := (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)) with hPedef
      set S1 := (∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)) with hS1def
      have h2b : 2 * p.2 = Pe + S1 := by
        rw [hPedef, hS1def, ← hbsum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          unfold henselDenominatorExponent; split <;> omega
      have hbS1 : p.2 ≤ t * S1 := by
        rw [← hbsum, hS1def, Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        split
        · next h => rw [h]; simp
        · next h => rw [Nat.mul_one]; exact hle i hi
      have hE1 : henselDenominatorExponent (t + 1) - 1 = 2 * t := by
        rw [henselDenominatorExponent_succ]; omega
      rw [hE1]
      rcases Nat.lt_or_ge p.2 (t + 1) with hbt | hbt
      · omega
      · have hS1ge : 2 ≤ S1 := by
          by_contra h
          push Not at h
          interval_cases S1 <;> omega
        omega
    -- `Pw = ∑(lᵢ + 1) = p.2 + j`
    have hPweq : (∑ i ∈ Finset.range j, (l i + 1)) = p.2 + j := by
      rw [Finset.sum_add_distrib, hbsum]; simp
    set Pw := (∑ i ∈ Finset.range j, (l i + 1)) with hPwdef
    set Pe := (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)) with hPedef
    set E1 := henselDenominatorExponent (t + 1) - 1 with hE1def
    -- helper: given a `W`-budget `wb ≥ Pw` and a regular `cf`, finish.
    have finish_with : ∀ (cf : 𝕃 H) (wb : ℕ),
        cf ∈ regularElementsSet H → Pw ≤ wb →
        cf * ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
          (W ^ (wb - Pw) * eta ^ (E1 - Pe)) ∈ regularElementsSet H := by
      intro cf wb hcf _hwb
      refine regularElementsSet_mul (regularElementsSet_mul hcf hprodReg) ?_
      exact regularElementsSet_mul
        (by rw [hWdef]; exact regularElementsSet_pow (regularElementsSet_liftToFunctionField H _) _)
        (by rw [hetadef]; exact regularElementsSet_pow ⟨_, rfl⟩ _)
    -- boundary detection
    by_cases hbdry : p.2 = t + 1 ∧ j = R.natDegree ∧ 2 ≤ R.natDegree
    · -- boundary: `p.1 = 0`, `j = d`, `d ≥ 2`; one extra `W` comes from the leading-coeff
      -- divisibility `W ∣ coeff 0 (liftCoeff (R.coeff d))`.
      obtain ⟨hb, hjeq, hdge⟩ := hbdry
      have ha0 : p.1 = 0 := by omega
      -- coeff 0 (liftCoeff (R.coeff d)) = W * q, q regular
      have hWdvd : ∃ q : 𝕃 H, q ∈ regularElementsSet H ∧
          PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) = W * q := by
        rw [ha0, hjeq, PowerSeries.coeff_zero_eq_constantCoeff_apply,
          constantCoeff_liftCoeffToPowerSeries]
        have hcoeff : (R.coeff R.natDegree).eval (Polynomial.C x₀) =
            (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
        rw [hcoeff]
        obtain ⟨c, hc⟩ := leadingCoeff_dvd_evalX_coeff_natDegree hHyp
        rw [hc, map_mul]
        exact ⟨liftToFunctionField (H := H) c, regularElementsSet_liftToFunctionField H c, by
          rw [hWdef]⟩
      obtain ⟨q, hqReg, hqeq⟩ := hWdvd
      -- W-budget: total available `W` power is `(t+2) + (d-2) + 1` (the `+1` from `q`'s `W`).
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) + 1 := by
        rw [hPweq]; omega
      -- rewrite Ddiv with the extra `W` from `coeffReg = W * q`
      rw [hqeq]
      have hreassoc :
          (W * q) * (∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          q * ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2) + 1) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2) + 1) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2) + 1) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show (W * q) * (∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            q * ((∏ i ∈ Finset.range j, αtrunc (l i)) *
              (W ^ ((t + 1 + 1) + (R.natDegree - 2) + 1) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      exact finish_with q _ hqReg hbudget
    · -- non-boundary: the `W`-budget `(t+2)+(d-2)` already covers `Pw = p.2 + j`.
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) := by
        rw [hPweq]
        rw [Finset.mem_range] at hj
        -- `¬(p.2 = t+1 ∧ j = d ∧ 2 ≤ d)`; with `p.2 ≤ t+1`, `j ≤ d`
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · omega
        · -- d ≥ 2:  the negated boundary forces `p.2 ≤ t` or `j ≤ d - 1`
          rcases not_and_or.mp hbdry with h1 | h2
          · -- p.2 ≠ t+1, so p.2 ≤ t
            omega
          · rcases not_and_or.mp h2 with h3 | h4
            · -- j ≠ R.natDegree, so j ≤ d - 1
              omega
            · exact absurd hd h4
      -- rewrite Ddiv directly
      have hreassoc :
          PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
            ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2)) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2)) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2)) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              ((∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ ((t + 1 + 1) + (R.natDegree - 2)) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      exact finish_with _ _ hcoeffReg hbudget

/-- **Regularity of the numerators.**  Multiplying the residual by the clearing denominator
`W^{t+2}·η^{eₜ₊₁-1}·W^{d-2}` lands in `𝒪`, so the next numerator `βₜ₊₁` is regular.  Proved
degree-by-degree through `henselClearedTerm_regular`, using `W ∣ leadingCoeff R(x₀,·,Z)` for the
top term. -/
theorem henselCoeffResidual_regular_after_clearing (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (_hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (_hzeta : zeta R x₀ H ≠ 0)
    (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (hprev : ∀ i : Fin (t + 1),
      embeddingOf𝒪Into𝕃 H (βprev i) /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (i.val + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ henselDenominatorExponent i.val) =
        αseq i.val) :
    let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
    let eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)
    let E : ℕ := henselDenominatorExponent (t + 1)
    let Ddiv : 𝕃 H := W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)
    henselCoeffResidual x₀ R H αseq t * Ddiv ∈ regularElementsSet H := by
  -- Residual-regularity (paper A.4). Step 1 (`henselCoeffResidual_eq_trunc`): the residual is
  -- the `(t+1)`-st coefficient of `R` evaluated at the truncated series `mk αtrunc` (the linear
  -- term `ζ · α(t+1)` cancels exactly). Step 2: expand `eval₂ liftCoeff (mk αtrunc) R` as a
  -- finite sum over `j`, distribute `Ddiv`, and apply the per-degree clearing lemma
  -- `henselClearedTerm_regular` to each summand.
  classical
  intro W eta E Ddiv
  set αtrunc : ℕ → 𝕃 H := fun i => if i ≤ t then αseq i else 0 with hαtrunc
  rw [henselCoeffResidual_eq_trunc x₀ R H αseq hα0 t]
  -- shape of `αtrunc` from `hprev`
  have hshape : ∀ i : ℕ, αtrunc i =
      if h : i ≤ t then
        embeddingOf𝒪Into𝕃 H (βprev ⟨i, by omega⟩) /
          (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
            (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ henselDenominatorExponent i)
      else 0 := by
    intro i
    by_cases h : i ≤ t
    · have hval : αtrunc i = αseq i := by rw [hαtrunc]; simp only [if_pos h]
      rw [hval, dif_pos h]
      have := hprev ⟨i, by omega⟩
      simpa using this.symm
    · have hval : αtrunc i = 0 := by rw [hαtrunc]; simp only [if_neg h]
      rw [hval, dif_neg h]
  change PowerSeries.coeff (t + 1)
      (evalRAtPowerSeries x₀ H R (PowerSeries.mk αtrunc)) * Ddiv ∈ regularElementsSet H
  unfold evalRAtPowerSeries
  rw [Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_mul]
  apply regularElementsSet_sum
  intro j hj
  exact henselClearedTerm_regular x₀ R H hHyp t βprev αtrunc hshape j hj


end HenselNumerators
end HenselLift
end RationalFunctions
