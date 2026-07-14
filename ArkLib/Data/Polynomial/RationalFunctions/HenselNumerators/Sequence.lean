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

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Weight
/-!
# Hensel Numerator Sequences

We define the notions of Appendix A of [BCIKS20].

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions
noncomputable section
namespace HenselNumerators
variable {F : Type} [Field F] {R : F[X][X][X]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
theorem regular_numerator_shape_succ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hzeta : ζ R x₀ H ≠ 0)
    (t : ℕ) (βprev : Fin (t + 1) → 𝒪 H)
    (hprev : ∀ i : Fin (t + 1),
      embeddingOf𝒪Into𝕃 H (βprev i) /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (i.val + 1) *
          (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent i.val) =
        αseq i.val) :
    ∃ βnext : 𝒪 H,
      embeddingOf𝒪Into𝕃 H βnext /
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)) ^ henselDenominatorExponent (t + 1)) =
        αseq (t + 1) := by
  classical
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)
  let E : ℕ := henselDenominatorExponent (t + 1)
  let D : 𝕃 H := W ^ (t + 1 + 1) * eta ^ E
  let Ddiv : 𝕃 H := W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)
  let S : 𝕃 H :=
    PowerSeries.coeff (t + 1) (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) -
      ζ R x₀ H * αseq (t + 1)
  have hSreg : S * Ddiv ∈ regularElementsSet H := by
    exact henselCoeffResidual_regular_after_clearing x₀ R H hHyp αseq hα0 hroot hzeta t βprev hprev
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have heta : eta ≠ 0 := by
    have hξeq := embeddingOf𝒪Into𝕃_ξ x₀ R H hHyp
    simpa [eta, W, hξeq] using mul_ne_zero (pow_ne_zero (R.natDegree - 2) hW) hzeta
  have hD : D ≠ 0 := by
    simp only [D]
    exact mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ heta)
  have hcoeff : PowerSeries.coeff (t + 1) (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) = 0 := by
    simpa using congrArg (fun p : PowerSeries (𝕃 H) => PowerSeries.coeff (t + 1) p) hroot
  have hS : S = - ζ R x₀ H * αseq (t + 1) := by
    simp only [S, hcoeff, zero_sub]
    ring
  have hEpos : 0 < E := by
    dsimp [E]
    rw [henselDenominatorExponent_succ]
    omega
  have hE : E = (E - 1) + 1 := by omega
  have hpeta : eta ^ E = eta ^ (E - 1) * eta := by
    conv_lhs => rw [hE, pow_succ]
  have hD_eq : D = ζ R x₀ H * Ddiv := by
    have heta_eq : eta = W ^ (R.natDegree - 2) * ζ R x₀ H := by
      simpa [eta, W] using embeddingOf𝒪Into𝕃_ξ x₀ R H hHyp
    calc
      D = W ^ (t + 1 + 1) * eta ^ E := rfl
      _ = W ^ (t + 1 + 1) * (eta ^ (E - 1) * eta) := by
        rw [hpeta]
      _ = W ^ (t + 1 + 1) * (eta ^ (E - 1) * (W ^ (R.natDegree - 2) * ζ R x₀ H)) := by
        exact congrArg (fun x => W ^ (t + 1 + 1) * (eta ^ (E - 1) * x)) heta_eq
      _ = ζ R x₀ H * (W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2)) := by
        ring
      _ = ζ R x₀ H * Ddiv := rfl
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

theorem exists_regular_numerator_shape (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (αseq : ℕ → 𝕃 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0) :
    ∃ βseq : ℕ → 𝒪 H,
      HasNumeratorShape x₀ R H hHyp αseq βseq := by
  classical
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let Xi : 𝕃 H := embeddingOf𝒪Into𝕃 H (ξ x₀ R H hHyp)
  let shapeAt : ℕ → 𝒪 H → Prop := fun t β =>
    embeddingOf𝒪Into𝕃 H β / (W ^ (t + 1) * Xi ^ henselDenominatorExponent t) = αseq t
  have hprefix : ∀ n : ℕ, ∃ βpref : Fin (n + 1) → 𝒪 H, ∀ i : Fin (n + 1), shapeAt i.val (βpref i) := by
    intro n
    induction n with
    | zero =>
        let β0 : 𝒪 H := (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) (Polynomial.X : F[X][Y]) : 𝒪 H)
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
            (zeta_ne_zero_of_Hypotheses x₀ R H hHyp) n βpref (by
              intro i
              exact hβpref i)
        rcases hnext with ⟨βnext, hβnext⟩
        refine ⟨fun i => if hlt : i.val < n + 1 then βpref ⟨i.val, hlt⟩ else βnext, ?_⟩
        intro i
        by_cases hlt : i.val < n + 1
        · simp [hlt]
          exact hβpref ⟨i.val, hlt⟩
        · have hval : i.val = n + 1 := by
            have hi_lt : i.val < n + 1 + 1 := i.isLt
            omega
          simp [hlt, hval]
          exact hβnext
  let βseq : ℕ → 𝒪 H := fun t => (Classical.choose (hprefix t)) ⟨t, Nat.lt_succ_self t⟩
  refine ⟨βseq, ?_⟩
  intro t
  unfold HasNumeratorShape at *
  unfold alphaOfNumerators
  change shapeAt t (βseq t)
  unfold βseq
  exact (Classical.choose_spec (hprefix t)) ⟨t, Nat.lt_succ_self t⟩

/-- There is a sequence of regular numerators `β_t` with the Hensel-lift semantics and the
weight bound stated in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
lemma exists_hensel_numerator_sequence (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D) :
    ∃ βseq : ℕ → 𝒪 H,
      IsHenselNumeratorSequence x₀ R H hHyp βseq ∧
      ∀ t : ℕ,
        weight_Λ_over_𝒪 hH (βseq t) D ≤
          (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  rcases exists_hensel_alpha_sequence x₀ R H hHyp with ⟨αseq, hα0, hroot⟩
  rcases exists_regular_numerator_shape x₀ R H hHyp αseq hα0 hroot with ⟨βseq, hshape⟩
  refine ⟨βseq, ?_, ?_⟩
  · exact hensel_numerator_sequence_of_alpha_shape x₀ R H hHyp αseq βseq hα0 hroot hshape
  · exact numerator_shape_weight_bound x₀ R H hHyp hH hD_H hD_R αseq βseq hα0 hroot hshape

/-- The chosen regular numerator sequence supplied by `exists_hensel_numerator_sequence`. -/
noncomputable def βSeq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) : ℕ → 𝒪 H :=
  if hH : 0 < H.natDegree then
    (exists_hensel_numerator_sequence x₀ R H hHyp hH
      (defaultDegreeBound_ge_H R H) (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)).choose
  else
    fun _ => 0

/-- The specification satisfied by the chosen numerator sequence. -/
lemma βSeq_spec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) :
    IsHenselNumeratorSequence x₀ R H hHyp (βSeq x₀ R H hHyp) ∧
      ∀ t : ℕ,
        weight_Λ_over_𝒪 hH ((βSeq x₀ R H hHyp) t) (defaultDegreeBound R H) ≤
          (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * defaultDegreeBound R H) :
            WithBot ℕ) := by
  unfold βSeq
  rw [dif_pos hH]
  exact (exists_hensel_numerator_sequence x₀ R H hHyp hH
    (defaultDegreeBound_ge_H R H) (fun _ hi => defaultDegreeBound_ge_R_coeff R H hi)).choose_spec

/-- The regular element `β_t` giving the numerator of the `t`-th chosen Hensel coefficient. -/
noncomputable def β (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝒪 H :=
  βSeq x₀ R H hHyp t

/-- The chosen Hensel-lift coefficients induced by the regular numerator sequence. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  alphaOfNumerators x₀ R H hHyp (βSeq x₀ R H hHyp) t

/-- Variant of `α` taking explicit irreducibility and positive-degree hypotheses. -/
def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp t

/-- The chosen power series `γ = ∑ α_t (X - x₀)^t`, induced by the selected regular numerator
sequence from `exists_hensel_numerator_sequence`. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    PowerSeries (𝕃 H) :=
  gammaOfNumerators x₀ R H hHyp (βSeq x₀ R H hHyp)

/-- Variant of `γ` taking explicit irreducibility and positive-degree hypotheses. -/
def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp


end HenselNumerators
end
end RationalFunctions
