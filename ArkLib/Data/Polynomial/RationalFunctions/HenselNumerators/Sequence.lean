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
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Weight
/-!
# The Hensel Numerator Sequence

Appendix A.4 of [BCIKS20]: assembly of Claim A.2. Existence of a sequence of regular numerators
`βₜ` with `αₜ = βₜ / (W^{t+1} ξ^{eₜ})` (`exists_hensel_numerator_sequence`), its uniqueness
(`IsHenselNumeratorSequence.unique`), the chosen sequence `betaSeq` with the induced `alpha` and
`gamma`, the weight bounds, and the paper's bundled statement.

Existence is deliberately separate from the weight bounds, so that `betaSeq`, `alpha` and `gamma` —
and hence the list-decoding consumers — do not depend on the one open quantitative step.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions
noncomputable section HenselNumeratorSequence
namespace HenselNumerators
variable {F : Type} [Field F] {R : F[X][X][Y]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
/-- One step of the numerator recursion: given regular numerators `βprev` realizing `αseq i` for
all `i ≤ t`, the next coefficient `αseq (t+1)` also has a regular numerator.  The witness is the
cleared residual, regular by `henselCoeffResidual_regular_after_clearing`. -/
theorem regular_numerator_shape_succ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hzeta : zeta R x₀ H ≠ 0)
    (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (hprev : ∀ i : Fin (t + 1),
      embeddingOf𝒪Into𝕃 H (βprev i) /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (i.val + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ henselDenominatorExponent i.val) =
        αseq i.val) :
    ∃ βnext : 𝒪 H,
      embeddingOf𝒪Into𝕃 H βnext /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ henselDenominatorExponent (t + 1)) =
        αseq (t + 1) := by
  classical
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)
  let E : ℕ := henselDenominatorExponent (t + 1)
  let D : 𝕃 H := W ^ (t + 1 + 1) * eta ^ E
  let Ddiv : 𝕃 H := W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)
  let S : 𝕃 H :=
    PowerSeries.coeff (t + 1) (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) -
      zeta R x₀ H * αseq (t + 1)
  have hSreg : S * Ddiv ∈ regularElementsSet H := by
    exact henselCoeffResidual_regular_after_clearing x₀ R H hHyp αseq hα0 hroot hzeta t βprev hprev
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have heta : eta ≠ 0 := by
    have hξeq := embeddingOf𝒪Into𝕃_xi x₀ R H hHyp
    simpa [eta, W, hξeq] using mul_ne_zero (pow_ne_zero (R.natDegree - 2) hW) hzeta
  have hD : D ≠ 0 := by
    simp only [D]
    exact mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ heta)
  have hcoeff :
      PowerSeries.coeff (t + 1) (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) = 0 := by
    simpa using congrArg (fun p : PowerSeries (𝕃 H) => PowerSeries.coeff (t + 1) p) hroot
  have hS : S = - zeta R x₀ H * αseq (t + 1) := by
    simp only [S, hcoeff, zero_sub]
    ring
  have hEpos : 0 < E := by
    dsimp [E]
    rw [henselDenominatorExponent_succ]
    omega
  have hE : E = (E - 1) + 1 := by omega
  have hpeta : eta ^ E = eta ^ (E - 1) * eta := by
    conv_lhs => rw [hE, pow_succ]
  have hD_eq : D = zeta R x₀ H * Ddiv := by
    have heta_eq : eta = W ^ (R.natDegree - 2) * zeta R x₀ H := by
      simpa [eta, W] using embeddingOf𝒪Into𝕃_xi x₀ R H hHyp
    calc
      D = W ^ (t + 1 + 1) * eta ^ E := rfl
      _ = W ^ (t + 1 + 1) * (eta ^ (E - 1) * eta) := by
        rw [hpeta]
      _ = W ^ (t + 1 + 1) * (eta ^ (E - 1) * (W ^ (R.natDegree - 2) * zeta R x₀ H)) := by
        exact congrArg (fun x => W ^ (t + 1 + 1) * (eta ^ (E - 1) * x)) heta_eq
      _ = zeta R x₀ H * (W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)) := by
        ring
      _ = zeta R x₀ H * Ddiv := rfl
  have hprod_eq : αseq (t + 1) * D = -(S * Ddiv) := by
    rw [hD_eq, hS]
    ring
  have hregProd : αseq (t + 1) * D ∈ regularElementsSet H := by
    rw [hprod_eq]
    exact regularElementsSet_neg hSreg
  rcases hregProd with ⟨βnext, hβnext⟩
  refine ⟨βnext, ?_⟩
  have hβnext' : (embeddingOf𝒪Into𝕃 H) βnext = αseq (t + 1) * D := hβnext.symm
  rw [hβnext']
  change (αseq (t + 1) * D) / D = αseq (t + 1)
  exact mul_div_cancel_right₀ (αseq (t + 1)) hD

/-- Iterating `regular_numerator_shape_succ`: every coefficient sequence solving the Hensel
equation admits regular numerators, i.e. some `βseq` with `HasNumeratorShape`.  The sequence is
assembled from compatible finite prefixes. -/
theorem exists_regular_numerator_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0) :
    ∃ βseq : ℕ → 𝒪 H,
      HasNumeratorShape x₀ R H hHyp αseq βseq := by
  classical
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let Xi : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)
  let shapeAt : ℕ → 𝒪 H → Prop := fun t β =>
    embeddingOf𝒪Into𝕃 H β / (W ^ (t + 1) * Xi ^ henselDenominatorExponent t) = αseq t
  have hprefix :
      ∀ n : ℕ, ∃ βpref : Fin (n + 1) → 𝒪 H, ∀ i : Fin (n + 1), shapeAt i.val (βpref i) := by
    intro n
    induction n with
    | zero =>
        let β0 : 𝒪 H := (Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.X : F[X][Y]) : 𝒪 H)
        refine ⟨fun _ => β0, ?_⟩
        intro i
        have hi : i.val = 0 := by omega
        rw [hi]
        unfold shapeAt
        rw [hα0]
        simp [β0, W, Xi, div_eq_mul_inv]
    | succ n ih =>
        rcases ih with ⟨βpref, hβpref⟩
        have hnext : ∃ βnext : 𝒪 H, shapeAt (n + 1) βnext := by
          unfold shapeAt
          exact regular_numerator_shape_succ x₀ R H hHyp αseq hα0 hroot
            (zeta_ne_zero_of_hypotheses x₀ R H hHyp) n βpref (by
              intro i
              exact hβpref i)
        rcases hnext with ⟨βnext, hβnext⟩
        refine ⟨fun i => if hlt : i.val < n + 1 then βpref ⟨i.val, hlt⟩ else βnext, ?_⟩
        intro i
        by_cases hlt : i.val < n + 1
        · simp only [dif_pos hlt]
          exact hβpref ⟨i.val, hlt⟩
        · have hval : i.val = n + 1 := by
            have hi_lt : i.val < n + 1 + 1 := i.isLt
            omega
          simp only [dif_neg hlt]
          rw [hval]
          exact hβnext
  let βseq : ℕ → 𝒪 H := fun t => (Classical.choose (hprefix t)) ⟨t, Nat.lt_succ_self t⟩
  refine ⟨βseq, ?_⟩
  intro t
  unfold alphaOfNumerators
  change shapeAt t (βseq t)
  unfold βseq
  exact (Classical.choose_spec (hprefix t)) ⟨t, Nat.lt_succ_self t⟩

/-- **Existence of a regular numerator sequence.**  There are regular `βₜ ∈ 𝒪 H` with
`αₜ = βₜ / (W^{t+1} ξ^{eₜ})` such that `α₀ = T / W` and the induced `γ = ∑ₜ αₜ (X - x₀)ᵗ` is a root
of `R(X, ·, Z)`.

Deliberately stated *without* the weight bounds: the chosen sequence `betaSeq` — and hence `alpha`,
`gamma` and every downstream consumer — is defined from this existence proof alone, so those
definitions do not depend on the quantitative weight accounting.  The bounds are supplied
separately by `hensel_numerator_weight_sharp_le` / `hensel_numerator_weight_le`, and the two halves
are recombined in `exists_hensel_numerators_with_weight_bounds`. -/
lemma exists_hensel_numerator_sequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    ∃ βseq : ℕ → 𝒪 H, IsHenselNumeratorSequence x₀ R H hHyp βseq := by
  rcases exists_hensel_alpha_sequence x₀ R H hHyp with ⟨αseq, hα0, hroot⟩
  rcases exists_regular_numerator_shape x₀ R H hHyp αseq hα0 hroot with ⟨βseq, hshape⟩
  exact ⟨βseq, hensel_numerator_sequence_of_alpha_shape x₀ R H hHyp αseq βseq hα0 hroot hshape⟩

/-- The chosen regular numerator sequence supplied by `exists_hensel_numerator_sequence`. -/
noncomputable def betaSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) : ℕ → 𝒪 H :=
  (exists_hensel_numerator_sequence x₀ R H hHyp).choose

/-- The Hensel-lift specification satisfied by the chosen numerator sequence. -/
lemma betaSeq_spec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    IsHenselNumeratorSequence x₀ R H hHyp (betaSeq x₀ R H hHyp) :=
  (exists_hensel_numerator_sequence x₀ R H hHyp).choose_spec

/-- **The Hensel numerator sequence is unique** — the counterpart of `IsHenselNumeratorSequence`'s
existence, and the numerator-level form of the uniqueness of the lift.

Consequently `betaSeq` is not merely *a* choice: it is *the* numerator sequence, and any `βseq`
satisfying the specification equals it (`eq_betaSeq`). -/
theorem IsHenselNumeratorSequence.unique (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) {βseq βseq' : ℕ → 𝒪 H}
    (hβ : IsHenselNumeratorSequence x₀ R H hHyp βseq)
    (hβ' : IsHenselNumeratorSequence x₀ R H hHyp βseq') :
    βseq = βseq' := by
  have hzeta := zeta_ne_zero_of_hypotheses x₀ R H hHyp
  -- the induced coefficient sequences agree, by uniqueness of the lift
  have hroot : evalRAtPowerSeries x₀ H R
      (gammaFromAlpha H (alphaOfNumerators x₀ R H hHyp βseq)) = 0 := by
    rw [← gammaOfNumerators_eq_gammaFromAlpha x₀ R H hHyp _ βseq (fun _ => rfl)]
    exact hβ.2
  have hroot' : evalRAtPowerSeries x₀ H R
      (gammaFromAlpha H (alphaOfNumerators x₀ R H hHyp βseq')) = 0 := by
    rw [← gammaOfNumerators_eq_gammaFromAlpha x₀ R H hHyp _ βseq' (fun _ => rfl)]
    exact hβ'.2
  have hα : alphaOfNumerators x₀ R H hHyp βseq = alphaOfNumerators x₀ R H hHyp βseq' :=
    hensel_alpha_sequence_unique x₀ R H hzeta hβ.1 hβ'.1 hroot hroot'
  -- the common denominator `W^{t+1} ξ^{eₜ}` is nonzero, so the numerators agree in `𝕃`,
  -- and `embeddingOf𝒪Into𝕃` is injective
  funext t
  have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have heta : embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) ≠ 0 := by
    rw [embeddingOf𝒪Into𝕃_xi x₀ R H hHyp]
    exact mul_ne_zero (pow_ne_zero (R.natDegree - 2) hW) hzeta
  have hD : liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1) *
      embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) ^ henselDenominatorExponent t ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ heta)
  have hdiv := congrFun hα t
  simp only [alphaOfNumerators] at hdiv
  rw [div_eq_div_iff hD hD] at hdiv
  exact embeddingOf𝒪Into𝕃_injective _H_natDegree_pos.out (mul_right_cancel₀ hD hdiv)

/-- Any sequence satisfying the specification is the chosen one. -/
theorem IsHenselNumeratorSequence.eq_betaSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) {βseq : ℕ → 𝒪 H}
    (hβ : IsHenselNumeratorSequence x₀ R H hHyp βseq) :
    βseq = betaSeq x₀ R H hHyp :=
  IsHenselNumeratorSequence.unique x₀ R H hHyp hβ (betaSeq_spec x₀ R H hHyp)

/-- The sharp weight bound for the chosen numerator sequence, at an arbitrary degree bound `D`
dominating `H` and the coefficients of `R`. -/
lemma betaSeq_weight_sharp_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R) :
    ∀ t : ℕ,
      regularWeight hH ((betaSeq x₀ R H hHyp) t) D ≤
        (WithBot.some (numeratorShapeSharpContent x₀ R H D t) : WithBot ℕ) :=
  hensel_numerator_weight_sharp_le x₀ R H hHyp hH hD_H hD_R hRdeg (betaSeq_spec x₀ R H hHyp)

/-- The loose weight bound `Λ(βₜ) ≤ (2t+1)·dY·D` for the chosen numerator sequence. -/
lemma betaSeq_weight_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R) :
    ∀ t : ℕ,
      regularWeight hH ((betaSeq x₀ R H hHyp) t) D ≤
        (WithBot.some ((2 * t + 1) * (Bivariate.natDegreeY R + 1) * D) : WithBot ℕ) :=
  hensel_numerator_weight_le x₀ R H hHyp hH hD_H hD_R hRdeg (betaSeq_spec x₀ R H hHyp)

/-- The sharp weight bound at the canonical degree bound `defaultDegreeBound R H`,
for callers that have no `D` of their own (e.g. the list-decoding files, which get `R` and `H` from
their own extraction step and no degree bound).  `defaultDegreeBound` dominates both `H` and the
coefficients of `R`, as required of `D`. -/
lemma betaSeq_weight_sharp_le_defaultDegreeBound (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R) :
    ∀ t : ℕ,
      regularWeight hH ((betaSeq x₀ R H hHyp) t) (defaultDegreeBound R H) ≤
        (WithBot.some (numeratorShapeSharpContent x₀ R H (defaultDegreeBound R H) t) : WithBot ℕ) :=
  betaSeq_weight_sharp_le x₀ R H hHyp hH (defaultDegreeBound_ge_H R H)
    (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi) hRdeg

/-- The loose weight bound `Λ(βₜ) ≤ (2t+1)·dY·D` at the canonical degree bound. -/
lemma betaSeq_weight_le_defaultDegreeBound (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R) :
    ∀ t : ℕ,
      regularWeight hH ((betaSeq x₀ R H hHyp) t) (defaultDegreeBound R H) ≤
        (WithBot.some ((2 * t + 1) * (Bivariate.natDegreeY R + 1) * defaultDegreeBound R H) :
          WithBot ℕ) :=
  betaSeq_weight_le x₀ R H hHyp hH (defaultDegreeBound_ge_H R H)
    (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi) hRdeg

/-- **Existence of a regular numerator sequence with weight bounds**, as a single statement: there
are regular `βₜ ∈ 𝒪` realizing the Hensel lift `αₜ = βₜ / (W^{t+1} ξ^{eₜ})`, with
`eₜ = max(0, 2t-1)` and

* `Λ(βₜ) ≤ 1 + (t+1)Λ(W) + eₜΛ(ξ)` (the sharp bound, the one that telescopes), and
* `Λ(βₜ) ≤ (2t+1)·d·D` (the loose bound, which is what consumers usually want).

The regularity of `ξ` and the bound `Λ(ξ) ≤ (d-1)(D - dH + 1)` are `xi_regular` and `xi_weight_le`.
Use `exists_hensel_numerator_sequence` (existence only) when defining data: this bundled form
carries the weight conjuncts and hence their proof dependencies. -/
theorem exists_hensel_numerators_with_weight_bounds (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R) :
    ∃ βseq : ℕ → 𝒪 H,
      IsHenselNumeratorSequence x₀ R H hHyp βseq ∧
      (∀ t : ℕ, regularWeight hH (βseq t) D ≤
        (WithBot.some (numeratorShapeSharpContent x₀ R H D t) : WithBot ℕ)) ∧
      ∀ t : ℕ, regularWeight hH (βseq t) D ≤
        (WithBot.some ((2 * t + 1) * (Bivariate.natDegreeY R + 1) * D) : WithBot ℕ) :=
  ⟨betaSeq x₀ R H hHyp, betaSeq_spec x₀ R H hHyp,
    betaSeq_weight_sharp_le x₀ R H hHyp hH hD_H hD_R hRdeg,
    betaSeq_weight_le x₀ R H hHyp hH hD_H hD_R hRdeg⟩


/-- The chosen Hensel-lift coefficients induced by the regular numerator sequence. -/
def alpha (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  alphaOfNumerators x₀ R H hHyp (betaSeq x₀ R H hHyp) t

/-- Variant of `α` taking explicit irreducibility and positive-degree hypotheses. -/
def alpha' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  alpha x₀ R _ (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp t

/-- The chosen power series `γ = ∑ α_t (X - x₀)^t`, induced by the selected regular numerator
sequence from `exists_hensel_numerator_sequence`. -/
def gamma (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    PowerSeries (𝕃 H) :=
  gammaOfNumerators x₀ R H hHyp (betaSeq x₀ R H hHyp)

/-- Variant of `γ` taking explicit irreducibility and positive-degree hypotheses. -/
def gamma' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  gamma x₀ R H (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp


end HenselNumerators
end HenselNumeratorSequence
end RationalFunctions
