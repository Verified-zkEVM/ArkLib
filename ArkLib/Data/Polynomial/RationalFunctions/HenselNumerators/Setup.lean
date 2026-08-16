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
import ArkLib.Data.Polynomial.RationalFunctions.Weight
import ArkLib.Data.Polynomial.RationalFunctions.Lifts
/-!
# The Derivative Value `ζ`, its Cleared Form `ξ`, and their Weights

Appendix A.4 of [BCIKS20]: the hypotheses of the Hensel lift (`Hypotheses`: `H ∣ R(x₀,·,Z)`
and `R(x₀,·,Z)` separable in `Y`), the derivative value `ζ = ∂R/∂Y(x₀, T/W, Z) ∈ 𝕃 H`, its cleared
form `ξ = W^{d-2}ζ ∈ 𝒪 H`, and the bound `Λ(ξ) ≤ (d-1)(D - dH + 1)` of Claim A.2.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions
noncomputable section HenselSetup
namespace HenselNumerators

variable {F : Type} [Field F] {R : F[X][X][Y]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]

/-! ### Hypotheses and derivative setup -/

/-- The algebraic hypotheses for the Hensel lift, after specializing
`R` at `X = x₀`. -/
structure Hypotheses (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : Prop where
  dvd_evalX : H ∣ Bivariate.evalX (Polynomial.C x₀) R
  separable_evalX : (Bivariate.evalX (Polynomial.C x₀) R).Separable

private lemma evalX_natDegree_le {K : Type} [CommSemiring K] (x : K) (P : K[X][Y]) :
    (Bivariate.evalX x P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have hcoeff : P.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
  simp [Bivariate.evalX_eq_map, Polynomial.coeff_map, hcoeff]

/-- `R(x₀,·,Z)` is nonzero, since it is separable by hypothesis. -/
lemma evalX_ne_zero_of_hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    Bivariate.evalX (Polynomial.C x₀) R ≠ 0 :=
  hHyp.separable_evalX.ne_zero

/-- `dH ≤ d`: the factor `H` cannot have larger `Y`-degree than `R`, since it divides
`R(x₀,·,Z)`. -/
lemma natDegree_H_le_natDegree_R_of_hypotheses {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.natDegree ≤ R.natDegree :=
  (Polynomial.natDegree_le_of_dvd hHyp.dvd_evalX (evalX_ne_zero_of_hypotheses hHyp)).trans
    (evalX_natDegree_le (Polynomial.C x₀) R)

/-- Coefficients of the specialized `Y`-derivative: `∂R/∂Y(x₀,·,Z)` has `i`-th coefficient
`(i+1) · R(x₀,·,Z)ᵢ₊₁`.  Differentiation in `Y` commutes with specializing `X`. -/
lemma derivative_evalX_coeff (x₀ : F) (R : F[X][X][Y]) (i : ℕ) :
    (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i =
      (Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X]) := by
  have hsucc_cast : (((i : ℕ) : F[X][X]) + 1) = ((i + 1 : ℕ) : F[X][X]) := by
    rw [← Nat.cast_one (R := F[X][X]), ← Nat.cast_add]
  calc
    (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i =
        ((R.derivative).coeff i).eval (Polynomial.C x₀) := by
      simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    _ = (R.coeff (i + 1) * ((i + 1 : ℕ) : F[X][X])).eval (Polynomial.C x₀) := by
      rw [Polynomial.coeff_derivative, hsucc_cast]
    _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X]) := by
      simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]

/-- Degree bound inherited by the derivative: its `i`-th coefficient has `Z`-degree at most
`D - (i+1)`, one better than the naive `D - i` because differentiating shifts the index. -/
lemma natDegree_derivative_evalX_coeff_le (x₀ : F) (R : F[X][X][Y]) {D i : ℕ}
    (hD : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i).natDegree ≤ D - (i + 1) := by
  rw [derivative_evalX_coeff]
  calc
    (((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1) * ((i + 1 : ℕ) : F[X])).natDegree)
        ≤ ((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1)).natDegree +
            (((i + 1 : ℕ) : F[X]).natDegree) := Polynomial.natDegree_mul_le
    _ = ((Bivariate.evalX (Polynomial.C x₀) R).coeff (i + 1)).natDegree := by
        rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C, Nat.add_zero]
    _ ≤ D - (i + 1) :=
        natDegree_coeff_le_of_totalDegree_le (Bivariate.evalX (Polynomial.C x₀) R) hD (i + 1)

/-- The leading coefficient `W` of `H` divides the leading coefficient of `R(x₀,Y,Z)`. -/
lemma leadingCoeff_dvd_evalX_leadingCoeff {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff := by
  rcases hHyp.dvd_evalX with ⟨q, hq⟩
  refine ⟨q.leadingCoeff, ?_⟩
  calc
    (Bivariate.evalX (Polynomial.C x₀) R).leadingCoeff = (H * q).leadingCoeff := by rw [hq]
    _ = H.leadingCoeff * q.leadingCoeff := Polynomial.leadingCoeff_mul H q

/-- The leading coefficient `W` of `H` divides the coefficient of `Y ^ R.natDegree` in
`R(x₀,Y,Z)`. If specialization lowers the `Y`-degree, that coefficient is zero. -/
lemma leadingCoeff_dvd_evalX_coeff_natDegree {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣ (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R
  have hdeg : P.natDegree ≤ R.natDegree := evalX_natDegree_le (Polynomial.C x₀) R
  by_cases hEq : P.natDegree = R.natDegree
  · simpa [P, hEq.symm] using leadingCoeff_dvd_evalX_leadingCoeff hHyp
  · have hlt : P.natDegree < R.natDegree := lt_of_le_of_ne hdeg hEq
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    exact dvd_zero H.leadingCoeff

/-- The leading coefficient `W` of `H` divides the top possible coefficient of
`∂R/∂Y(x₀,Y,Z)`. This is the coefficient that remains after multiplying `ζ` by `W^(d-2)`. -/
lemma leadingCoeff_dvd_evalX_derivative_coeff_pred {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hHyp : Hypotheses x₀ R H) :
    H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) := by
  by_cases hR : R.natDegree = 0
  · have hderiv : R.derivative = 0 := Polynomial.derivative_of_natDegree_zero hR
    rw [hderiv]
    exact ⟨0, by simp [Bivariate.evalX_eq_map]⟩
  · have hsucc : R.natDegree - 1 + 1 = R.natDegree :=
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hR)
    have hsucc_cast : (((R.natDegree - 1 : ℕ) : F[X][X]) + 1) =
        (R.natDegree : F[X][X]) := by
      rw [← Nat.cast_one (R := F[X][X])]
      rw [← Nat.cast_add, hsucc]
    have hcoeff :
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
          (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
      calc
        (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
            ((R.derivative).coeff (R.natDegree - 1)).eval (Polynomial.C x₀) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
        _ = (R.coeff R.natDegree * (R.natDegree : F[X][X])).eval (Polynomial.C x₀) := by
          rw [Polynomial.coeff_derivative, hsucc, hsucc_cast]
        _ = (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree *
            (R.natDegree : F[X]) := by
          simp [Bivariate.evalX_eq_map, Polynomial.coeff_map]
    rcases leadingCoeff_dvd_evalX_coeff_natDegree hHyp with ⟨q, hq⟩
    refine ⟨q * (R.natDegree : F[X]), ?_⟩
    rw [hcoeff, hq]
    ring

/-- The derivative value `ζ = ∂R/∂Y(x₀, T/W, Z) ∈ 𝕃 H`.  It is nonzero exactly when `T/W` is a
*simple* root of `R(x₀,·,Z)` (`zeta_ne_zero_of_hypotheses`), which is what makes each Hensel step
uniquely solvable. -/
def zeta (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  let T : 𝕃 H := functionFieldT (H := H)
  Polynomial.eval₂ liftToFunctionField (T / W)
    (Bivariate.evalX (Polynomial.C x₀) R.derivative)


/-- If `R` has `Y`-degree at most one, then the specialized derivative is constant. -/
lemma derivative_evalX_eq_C_of_natDegree_le_one
    (x₀ : F) (R : F[X][X][Y]) (hR : R.natDegree ≤ 1) :
    ∃ p : F[X], Bivariate.evalX (Polynomial.C x₀) R.derivative = Polynomial.C p := by
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  refine ⟨P.coeff 0, ?_⟩
  have hderiv : R.derivative.natDegree ≤ 0 := by
    calc
      R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      _ = 0 := by omega
  have hP : P.natDegree ≤ 0 :=
    (evalX_natDegree_le (Polynomial.C x₀) R.derivative).trans hderiv
  exact Polynomial.eq_C_of_natDegree_le_zero hP


/-- Explicit polynomial representative for the regular element `ξ = W^(d-2) · ζ`.
For `2 ≤ R.natDegree`, this is the polynomial obtained by clearing the single denominator that
appears in `W^(d-2) · ζ`; the divisibility `W ∣ R'(x₀, Z)_{d-1}` is captured implicitly by
Euclidean division in `F[X]`. For `R.natDegree ≤ 1`, the derivative specialization is constant
in `Y`, so we take it as the representative. -/
noncomputable def xiPre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  if 2 ≤ d then
    (∑ i ∈ Finset.range (d - 1),
        Polynomial.C (P.coeff i * W ^ (d - 2 - i)) * Polynomial.X ^ i) +
      Polynomial.C (P.coeff (d - 1) / W) * Polynomial.X ^ (d - 1)
  else
    P

/-- The image of `⟦xiPre⟧` in the function field equals `W^(d-2) · ζ`, i.e. `xiPre` really does
represent `ξ`. -/
lemma embeddingOf𝒪Into𝕃_mk_xiPre (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk _ (xiPre x₀ R H) : 𝒪 H) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * zeta R x₀ H := by
  rw [embeddingOf𝒪Into𝕃_mk]
  by_cases hRle : R.natDegree ≤ 1
  · -- d ≤ 1: xiPre = R'(x₀, Z), constant in Y; ζ is the lift of that constant.
    rcases derivative_evalX_eq_C_of_natDegree_le_one x₀ R hRle with ⟨p, hp⟩
    have hd2 : R.natDegree - 2 = 0 := by omega
    have hbranch : ¬ 2 ≤ R.natDegree := by omega
    have hxiPre : xiPre x₀ R H = Polynomial.C p := by
      simp [xiPre, hbranch, hp]
    rw [hxiPre, hd2, pow_zero, one_mul, liftBivariate_C]
    change liftToFunctionField (H := H) p =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
        (Bivariate.evalX (Polynomial.C x₀) R.derivative)
    rw [hp, Polynomial.eval₂_C]
  · have hd2 : 2 ≤ R.natDegree := by omega
    set P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative with hP_def
    set W_poly : F[X] := H.leadingCoeff with hW_poly_def
    have hkk : R.natDegree - 1 = R.natDegree - 2 + 1 := by omega
    have hP_le : P.natDegree ≤ R.natDegree - 2 + 1 := by
      have h1 : P.natDegree ≤ R.derivative.natDegree := evalX_natDegree_le _ R.derivative
      have h2 : R.derivative.natDegree ≤ R.natDegree - 1 := Polynomial.natDegree_derivative_le R
      omega
    have hdiv : W_poly ∣ P.coeff (R.natDegree - 2 + 1) := by
      have h := leadingCoeff_dvd_evalX_derivative_coeff_pred (H := H) hHyp
      rwa [hkk] at h
    have hW_poly_ne : W_poly ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out)
    have hW_ne : (liftToFunctionField (H := H) W_poly : 𝕃 H) ≠ 0 :=
      liftToFunctionField_leadingCoeff_ne_zero (H := H)
    have hxiPre_eq : xiPre x₀ R H =
        (∑ i ∈ Finset.range (R.natDegree - 2 + 1),
            Polynomial.C (P.coeff i * W_poly ^ (R.natDegree - 2 - i)) * Polynomial.X ^ i) +
          Polynomial.C (P.coeff (R.natDegree - 2 + 1) / W_poly) *
            Polynomial.X ^ (R.natDegree - 2 + 1) := by
      simp only [xiPre, hd2, ↓reduceIte, ← hP_def, ← hW_poly_def, hkk]
    rw [hxiPre_eq]
    rw [show (zeta R x₀ H : 𝕃 H) =
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) W_poly) P from rfl]
    rw [leadingCoeff_pow_mul_eval₂_div_eq_sum (H := H) (P := P) (k := R.natDegree - 2) hP_le]
    have hlift_div :
        liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1) / W_poly) =
          liftToFunctionField (H := H) (P.coeff (R.natDegree - 2 + 1)) /
            liftToFunctionField (H := H) W_poly := by
      rw [eq_div_iff hW_ne, ← map_mul, mul_comm,
          EuclideanDomain.mul_div_cancel' hW_poly_ne hdiv]
    simp only [map_add, map_sum, map_mul, map_pow, liftBivariate_C, liftBivariate_X, hlift_div]
    refine congr_arg₂ (· + ·) ?_ rfl
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring

/-- The element `ξ = W(Z)^(d-2) · ζ` is regular, i.e. has a representative in `𝒪 H`.

For `d < 2` the natural-number exponent truncates to zero, so this statement remains true but says
something weaker than intended; the weight bound is therefore stated separately, with the explicit
hypothesis `2 ≤ d`. -/
lemma xi_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * zeta R x₀ H :=
  ⟨Ideal.Quotient.mk _ (xiPre x₀ R H),
    by simpa using embeddingOf𝒪Into𝕃_mk_xiPre x₀ R H hHyp⟩

/-- The regular element `ξ = W(Z)^(d-2) · ζ`.

The `Fact` and `Hypotheses` arguments are kept for API compatibility with downstream callers
(`α`, `γ`); they are needed for the embedding equation in `embeddingOf𝒪Into𝕃_xi`. -/
noncomputable def xi (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [_φ : Fact (Irreducible H)]
    [_H_natDegree_pos : Fact (0 < H.natDegree)] (_hHyp : Hypotheses x₀ R H) : 𝒪 H :=
  Ideal.Quotient.mk _ (xiPre x₀ R H)

/-- The defining equation `embedding ξ = W^(d-2) · ζ`, the specialization of
`embeddingOf𝒪Into𝕃_mk_xiPre` to `ξ`. -/
lemma embeddingOf𝒪Into𝕃_xi (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) :
    embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) =
      liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2) * zeta R x₀ H :=
  embeddingOf𝒪Into𝕃_mk_xiPre x₀ R H hHyp

omit H_irreducible H_natDegree_pos in
/-- `deg_Z W ≤ D - dH` for `W = H.leadingCoeff`, the paper's bound on `Λ(W)` in A.4. -/
theorem leadingCoeff_natDegree_le_of_totalDegree_le {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D) :
    H.leadingCoeff.natDegree ≤ D - H.natDegree := by
  exact natDegree_coeff_le_of_totalDegree_le H hD_H H.natDegree

/-- Weight of the reduction of a top-degree cofactor term: for `H · Q` of total degree at most
`D`, the monomial `C (d · Q_a) · T^{d-1}` reduces modulo `H̃` to something of weight at most
`(d-1)·(D - dH + 1)`.  This drives the `ξ`-weight bound in the case `dH < d`. -/
theorem cofactor_top_reduction_weight_le {H : F[X][Y]} (hH : 0 < H.natDegree) {Q : F[X][Y]}
    {d D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_HQ : Bivariate.totalDegree (H * Q) ≤ D)
    (hd : H.natDegree < d)
    (hQdeg : Q.natDegree ≤ d - H.natDegree) :
    weight
      (Polynomial.C ((d : F[X]) * Q.coeff (d - H.natDegree)) *
          Polynomial.X ^ (d - 1) %ₘ monicize H) H D ≤
      (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ) := by
  classical
  by_cases hQzero : Q = 0
  · subst hQzero
    simp
  · let m : ℕ := H.natDegree
    let s : ℕ := d - m
    let W : F[X] := H.coeff m
    let c : F[X] := (d : F[X]) * Q.coeff s
    let lower : F[X][Y] := ∑ i ∈ Finset.range m,
      Polynomial.C (H.coeff i * W ^ (m - 1 - i)) * Polynomial.X ^ i
    let p : F[X][Y] := Polynomial.C c * Polynomial.X ^ (d - 1)
    have hm_pos : 0 < m := by dsimp [m]; exact hH
    have hs_pos : 0 < s := by
      dsimp [s, m]
      omega
    have hdm : d - 1 = (s - 1) + m := by
      dsimp [s, m]
      omega
    have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
    have hm_le_T : m ≤ Bivariate.totalDegree H := by
      have hHin : m ∈ H.support := by
        dsimp [m]
        exact Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
      have hcontrib : (H.coeff m).natDegree + m ≤ Bivariate.totalDegree H := by
        simpa [m] using Bivariate.coeff_totalDegree_le H hHin
      omega
    have hm_le_D : m ≤ D := le_trans hm_le_T hD_H
    have hTQ : Bivariate.totalDegree Q ≤ D - Bivariate.totalDegree H := by
      have hmul :
          Bivariate.totalDegree (H * Q) = Bivariate.totalDegree H + Bivariate.totalDegree Q := by
        simpa using Bivariate.totalDegree_mul (F := F) hH_ne hQzero
      omega
    have hQcoeff0 : (Q.coeff s).natDegree ≤ D - Bivariate.totalDegree H := by
      exact (natDegree_coeff_le_of_totalDegree_le Q hTQ s).trans (Nat.sub_le _ _)
    have hd_natDegree : ((d : F[X]).natDegree = 0) := by
      rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C]
    have hcdeg : c.natDegree ≤ D - Bivariate.totalDegree H := by
      dsimp [c]
      calc
        ((d : F[X]) * Q.coeff s).natDegree ≤ ((d : F[X]).natDegree + (Q.coeff s).natDegree) :=
            Polynomial.natDegree_mul_le
        _ ≤ 0 + (D - Bivariate.totalDegree H) := by
          rw [hd_natDegree]
          omega
        _ = D - Bivariate.totalDegree H := by omega
    have htilde : monicize H = Polynomial.X ^ m + lower := by
      dsimp [lower, W, m]
      rw [monicize, if_neg (Nat.ne_of_gt hH)]
      rw [← Polynomial.coeff_natDegree (p := H)]
    have hmod :
        p %ₘ monicize H = (-(Polynomial.C c * Polynomial.X ^ (s - 1) * lower)) %ₘ monicize H := by
      apply Polynomial.modByMonic_eq_of_dvd_sub (monicize_monic H hH)
      refine ⟨Polynomial.C c * Polynomial.X ^ (s - 1), ?_⟩
      rw [htilde]
      dsimp [p]
      rw [hdm, pow_add]
      ring
    have hsum_eq : Polynomial.C c * Polynomial.X ^ (s - 1) * lower =
        ∑ i ∈ Finset.range m,
          Polynomial.C (c * (H.coeff i * W ^ (m - 1 - i))) * Polynomial.X ^ ((s - 1) + i) := by
      dsimp [lower]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      let a : F[X] := H.coeff i * W ^ (m - 1 - i)
      change Polynomial.C c * Polynomial.X ^ (s - 1) * (Polynomial.C a * Polynomial.X ^ i) =
        Polynomial.C (c * a) * Polynomial.X ^ (s - 1 + i)
      calc
        Polynomial.C c * Polynomial.X ^ (s - 1) * (Polynomial.C a * Polynomial.X ^ i)
            = (Polynomial.C c * Polynomial.C a) * (Polynomial.X ^ (s - 1) * Polynomial.X ^ i) := by
                ring
        _ = Polynomial.C (c * a) * Polynomial.X ^ (s - 1 + i) := by
          rw [← Polynomial.C_mul, pow_add]
    have hraw : weight (-(Polynomial.C c * Polynomial.X ^ (s - 1) * lower)) H D ≤
        (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ) := by
      rw [weight_neg]
      rw [hsum_eq]
      refine (weight_sum_le (Finset.range m)
        (fun i => Polynomial.C (c * (H.coeff i * W ^ (m - 1 - i))) * Polynomial.X ^ (s - 1 + i)) H
            D).trans ?_
      refine Finset.sup_le (fun i hi => ?_)
      have hi_lt : i < m := Finset.mem_range.mp hi
      have hHi : (H.coeff i).natDegree ≤ Bivariate.totalDegree H - i := by
        exact natDegree_coeff_le_of_totalDegree_le H (le_rfl) i
      have hWdeg : W.natDegree ≤ Bivariate.totalDegree H - m := by
        dsimp [W, m]
        exact natDegree_coeff_le_of_totalDegree_le H (le_rfl) H.natDegree
      have hWpow : (W ^ (m - 1 - i)).natDegree ≤ (m - 1 - i) * (Bivariate.totalDegree H - m) := by
        exact (Polynomial.natDegree_pow_le (p := W) (n := m - 1 - i)).trans
          (Nat.mul_le_mul_left _ hWdeg)
      have hHiW : (H.coeff i * W ^ (m - 1 - i)).natDegree ≤
          (Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m) := by
        calc
          (H.coeff i * W ^ (m - 1 - i)).natDegree ≤
              (H.coeff i).natDegree + (W ^ (m - 1 - i)).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m) :=
              Nat.add_le_add hHi hWpow
      have htermdeg : (c * (H.coeff i * W ^ (m - 1 - i))).natDegree ≤
          (D - Bivariate.totalDegree H) +
            ((Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m)) := by
        calc
          (c * (H.coeff i * W ^ (m - 1 - i))).natDegree ≤
              c.natDegree + (H.coeff i * W ^ (m - 1 - i)).natDegree := Polynomial.natDegree_mul_le
          _ ≤ (D - Bivariate.totalDegree H) +
              ((Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m)) :=
              Nat.add_le_add hcdeg hHiW
      have harith :
          (s - 1 + i) * (D - m + 1) +
            ((D - Bivariate.totalDegree H) +
                ((Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m))) ≤
          (d - 1) * (D - m + 1) := by
        have hT_le_D : Bivariate.totalDegree H ≤ D := hD_H
        have hi_le : i ≤ m - 1 := by omega
        have hi_le_m : i ≤ m := le_of_lt hi_lt
        have hi_le_T : i ≤ Bivariate.totalDegree H := le_trans hi_le_m hm_le_T
        have hkey :
            (s - 1 + i) * (D - m + 1) +
                ((D - Bivariate.totalDegree H) +
                    ((Bivariate.totalDegree H - i) + (m - 1 - i) * (Bivariate.totalDegree H - m))) +
                (m - 1 - i) * (D - Bivariate.totalDegree H) =
              (d - 1) * (D - m + 1) := by
          rw [hdm]
          zify [hT_le_D, hm_le_T, hm_le_D, hi_le, hi_le_m, hi_le_T, hs_pos, hm_pos]
          ring_nf
        omega
      refine (weight_C_mul_X_pow_le H D (c * (H.coeff i * W ^ (m - 1 - i))) (s - 1 + i)).trans ?_
      rw [WithBot.coe_le_coe]
      have hM : D + 1 - Bivariate.natDegreeY H = D - m + 1 := by
        dsimp [m]
        rw [show Bivariate.natDegreeY H = H.natDegree from rfl]
        omega
      rw [hM]
      exact (Nat.add_le_add_left htermdeg ((s - 1 + i) * (D - m + 1))).trans harith
    calc
      weight
          (Polynomial.C ((d : F[X]) * Q.coeff (d - H.natDegree)) * Polynomial.X ^ (d - 1) %ₘ
              monicize H) H D
          = weight (p %ₘ monicize H) H D := by rfl
      _ = weight ((-(Polynomial.C c * Polynomial.X ^ (s - 1) * lower)) %ₘ monicize H) H D := by rw
          [hmod]
      _ ≤ weight (-(Polynomial.C c * Polynomial.X ^ (s - 1) * lower)) H D :=
        weight_modByMonic_monicize_le hD_H hH _
      _ ≤ (WithBot.some ((d - 1) * (D - H.natDegree + 1)) : WithBot ℕ) := hraw

/-- `Λ` on `𝒪` is bounded by the max under addition, transported from `weight_add_le` through
canonical representatives. -/
theorem regularWeight_add_le {H : F[X][Y]} {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (a b : 𝒪 H) :
    regularWeight hH (a + b) D ≤
      max (regularWeight hH a D) (regularWeight hH b D) := by
  let pa := canonicalRepOf𝒪 hH a
  let pb := canonicalRepOf𝒪 hH b
  have hpa : regularWeight hH (Ideal.Quotient.mk (Ideal.span {monicize H}) pa : 𝒪 H) D = weight
      pa H D := by
    exact regularWeight_mk_eq_self_of_degree_lt hH (canonicalRepOf𝒪_degree_lt hH a) D
  have hpb : regularWeight hH (Ideal.Quotient.mk (Ideal.span {monicize H}) pb : 𝒪 H) D = weight
      pb H D := by
    exact regularWeight_mk_eq_self_of_degree_lt hH (canonicalRepOf𝒪_degree_lt hH b) D
  rw [← mk_canonicalRepOf𝒪 hH a, ← mk_canonicalRepOf𝒪 hH b]
  rw [hpa, hpb]
  exact le_trans (regularWeight_mk_le hD_H hH (pa + pb)) (weight_add_le pa pb H D)

/-- The low-degree part of the explicit representative of `ξ`: `∑_{i<d-1} (Pᵢ · W^{d-2-i}) Tⁱ`
with `P = ∂R/∂Y(x₀,·,Z)`.  These are the terms of `W^{d-2}·ζ` whose `W`-power is non-negative. -/
noncomputable def xiPreLower (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  ∑ i ∈ Finset.range (d - 1),
    Polynomial.C (P.coeff i * W ^ (d - 2 - i)) * Polynomial.X ^ i

omit H_irreducible H_natDegree_pos in
/-- Degree of a single low-part coefficient `Pᵢ · W^{d-2-i}`, from the degree bounds on `P` and
on `W`. -/
theorem xiPreLower_coeff_natDegree_le (x₀ : F) {D i : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    (((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
        H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree) ≤
      (D - (i + 1)) + (R.natDegree - 2 - i) * (D - H.natDegree) := by
  have hcoeff := natDegree_derivative_evalX_coeff_le (i := i) x₀ R hD_Rx0
  have hlc := leadingCoeff_natDegree_le_of_totalDegree_le hD_H
  have hmul :
      (((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i * H.leadingCoeff ^
          (R.natDegree - 2 - i)).natDegree) ≤
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i).natDegree +
          (H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree := Polynomial.natDegree_mul_le
  have hpow : (H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree ≤ (R.natDegree - 2 - i) *
      H.leadingCoeff.natDegree := Polynomial.natDegree_pow_le
  exact le_trans hmul
      (Nat.add_le_add hcoeff (le_trans hpow (Nat.mul_le_mul_left (R.natDegree - 2 - i) hlc)))

omit H_irreducible H_natDegree_pos in
/-- Each monomial of `xiPreLower` has `Λ`-weight at most `(d-1)·(D - dH + 1)`, the bound claimed
for `ξ`. -/
theorem xiPreLower_term_weight_le (x₀ : F) (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hRdeg : 2 ≤ R.natDegree)
    {D i : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    (hi : i < R.natDegree - 1) :
    weight
      (Polynomial.C
        ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
          H.leadingCoeff ^ (R.natDegree - 2 - i)) *
        Polynomial.X ^ i)
      H D
      ≤ WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) := by
  refine le_trans
      (weight_C_mul_X_pow_le H D
          ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i * H.leadingCoeff ^
          (R.natDegree - 2 - i)) i) ?_
  rw [WithBot.coe_le_coe]
  rw [show Bivariate.natDegreeY H = H.natDegree from rfl]
  have hcoeff := xiPreLower_coeff_natDegree_le x₀ hD_H hD_Rx0 (D := D) (i := i)
  have hdH_le_R : H.natDegree ≤ R.natDegree := natDegree_H_le_natDegree_R_of_hypotheses hHyp
  have hHpos : 0 < H.natDegree := hH
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hHpos
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hdH_le_D : H.natDegree ≤ D := by
    have : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  have hD1sub : D + 1 - H.natDegree = D - H.natDegree + 1 := by omega
  rw [hD1sub]
  set m : ℕ := D - H.natDegree
  have hcoeff_m :
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
          H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree ≤
        D - (i + 1) + (R.natDegree - 2 - i) * m := by
    simpa [m] using hcoeff
  have hi_le : i ≤ R.natDegree - 2 := by omega
  calc
    i * (m + 1) +
        ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i *
          H.leadingCoeff ^ (R.natDegree - 2 - i)).natDegree
        ≤ i * (m + 1) +
          ((D - (i + 1)) + (R.natDegree - 2 - i) * m) := by
          exact Nat.add_le_add_left hcoeff_m _
    _ ≤ (R.natDegree - 1) * (m + 1) := by
      by_cases hcase : i + 1 ≤ D
      · have hDpos : 1 ≤ D := by omega
        have hleft_eq :
            i * (m + 1) + (D - (i + 1) + (R.natDegree - 2 - i) * m) =
              (R.natDegree - 2) * m + (D - 1) := by
          zify [hcase, hRdeg, hi_le, hDpos]
          ring
        rw [hleft_eq]
        have hDminus : D - 1 ≤ m + (R.natDegree - 1) := by
          subst m
          omega
        have hright_eq :
            (R.natDegree - 2) * m + (m + (R.natDegree - 1)) =
              (R.natDegree - 1) * (m + 1) := by
          have hR1 : 1 ≤ R.natDegree := by omega
          zify [hRdeg, hR1]
          ring
        calc
          (R.natDegree - 2) * m + (D - 1)
              ≤ (R.natDegree - 2) * m + (m + (R.natDegree - 1)) := by
                exact Nat.add_le_add_left hDminus _
          _ = (R.natDegree - 1) * (m + 1) := hright_eq
      · have hDsub : D - (i + 1) = 0 := by omega
        rw [hDsub]
        rw [zero_add]
        have hleft_eq :
            i * (m + 1) + (R.natDegree - 2 - i) * m =
              (R.natDegree - 2) * m + i := by
          zify [hi_le]
          ring
        rw [hleft_eq]
        have hmul : (R.natDegree - 2) * m ≤ (R.natDegree - 1) * m := by
          exact Nat.mul_le_mul_right m (by omega)
        have hi_le_n1 : i ≤ R.natDegree - 1 := by omega
        have htarget_expand :
            (R.natDegree - 1) * (m + 1) = (R.natDegree - 1) * m + (R.natDegree - 1) := by
          ring
        rw [htarget_expand]
        exact Nat.add_le_add hmul hi_le_n1

omit H_irreducible H_natDegree_pos in
/-- The low-degree part of `ξ` obeys `Λ ≤ (d-1)·(D - dH + 1)`, by taking the max over its
monomials. -/
theorem xiPreLower_weight_le (x₀ : F) (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    (hRdeg : 2 ≤ R.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    weight (xiPreLower x₀ R H) H D ≤
      WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) := by
  unfold xiPreLower
  refine le_trans
      (weight_sum_le (Finset.range (R.natDegree - 1))
          (fun i => Polynomial.C
          ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff i * H.leadingCoeff ^
          (R.natDegree - 2 - i)) * Polynomial.X ^ i) H D) ?_
  apply Finset.sup_le
  intro i hi
  exact xiPreLower_term_weight_le x₀ hHyp hH hRdeg hD_H hD_Rx0 (Finset.mem_range.mp hi)

/-- The top term of the explicit representative of `ξ`: `(P_{d-1} / W) · T^{d-1}`.  Its `W`-power
would be negative, so the division is exact by `leadingCoeff_dvd_evalX_derivative_coeff_pred` —
this is the paper's "we can save a little" step. -/
noncomputable def xiPreTop (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) : F[X][Y] :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let W : F[X] := H.leadingCoeff
  Polynomial.C (P.coeff (d - 1) / W) * Polynomial.X ^ (d - 1)

omit H_irreducible H_natDegree_pos in
/-- When `dH = d` the top coefficient `P_{d-1} / W` is a constant, so the top term contributes no
`Z`-degree. -/
theorem xiPreTop_coeff_natDegree_zero_of_H_natDegree_eq_R_natDegree (x₀ : F) (hH : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) (heq : H.natDegree = R.natDegree) :
    ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) /
      H.leadingCoeff).natDegree = 0 := by
  classical
  set P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R with hP_def
  rcases hHyp.dvd_evalX with ⟨Q, hQ⟩
  have hP_ne : P ≠ 0 := by
    rw [hP_def]
    exact evalX_ne_zero_of_hypotheses hHyp
  have hQ_ne : Q ≠ 0 := by
    intro h0
    apply hP_ne
    rw [hP_def, hQ, h0, mul_zero]
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hdegP : P.natDegree ≤ R.natDegree := by
    rw [hP_def]
    exact evalX_natDegree_le (Polynomial.C x₀) R
  have hQdeg : Q.natDegree = 0 := by
    have hmuldeg : (H * Q).natDegree = H.natDegree + Q.natDegree := by
      exact Polynomial.natDegree_mul hH_ne hQ_ne
    have hPdeg_eq : P.natDegree = (H * Q).natDegree := by
      rw [hP_def, hQ]
    omega
  let q : F[X] := Q.coeff 0
  have hQ_C : Q = Polynomial.C q := by
    exact Polynomial.eq_C_of_natDegree_le_zero (p := Q) (by omega)
  have hsepHQ : (H * Polynomial.C q).Separable := by
    rw [← hQ_C]
    rw [← hQ, ← hP_def]
    exact hHyp.separable_evalX
  have hq_unit : IsUnit q := by
    rw [Polynomial.separable_def'] at hsepHQ
    rcases hsepHQ with ⟨A, B, hAB⟩
    have hderiv : (H * Polynomial.C q).derivative = H.derivative * Polynomial.C q := by
      simp [Polynomial.derivative_mul]
    have hfactor : (A * H + B * H.derivative) * Polynomial.C q = (1 : F[X][Y]) := by
      calc
        (A * H + B * H.derivative) * Polynomial.C q
            = A * (H * Polynomial.C q) + B * (H.derivative * Polynomial.C q) := by ring
        _ = A * (H * Polynomial.C q) + B * (H * Polynomial.C q).derivative := by rw [hderiv]
        _ = 1 := hAB
    have hCunit : IsUnit (Polynomial.C q : F[X][Y]) := by
      exact IsUnit.of_mul_eq_one (A * H + B * H.derivative) (by simpa [mul_comm] using hfactor)
    exact (Polynomial.isUnit_C.mp hCunit)
  have hsucc : R.natDegree - 1 + 1 = R.natDegree := by omega
  have hPtop : (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree = H.leadingCoeff * q := by
    rw [hQ, hQ_C]
    rw [← heq]
    simp [Polynomial.coeff_natDegree]
  have htop_coeff :
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) =
        H.leadingCoeff * (q * (R.natDegree : F[X])) := by
    rw [derivative_evalX_coeff, hsucc, hPtop]
    ring
  have hW_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH_ne
  have hdiv : H.leadingCoeff ∣
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) :=
    leadingCoeff_dvd_evalX_derivative_coeff_pred hHyp
  have hquot :
      (Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) /
          H.leadingCoeff = q * (R.natDegree : F[X]) := by
    exact (EuclideanDomain.div_eq_iff_eq_mul_of_dvd
      ((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1))
      H.leadingCoeff (q * (R.natDegree : F[X])) hW_ne hdiv).2 htop_coeff
  rw [hquot]
  have hqdeg0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hq_unit
  have hndeg0 : ((R.natDegree : F[X]).natDegree = 0) := by
    rw [← Polynomial.C_eq_natCast, Polynomial.natDegree_C]
  have hle : (q * (R.natDegree : F[X])).natDegree ≤ 0 := by
    calc
      (q * (R.natDegree : F[X])).natDegree ≤ q.natDegree + ((R.natDegree : F[X]).natDegree) :=
        Polynomial.natDegree_mul_le
      _ = 0 := by rw [hqdeg0, hndeg0, Nat.zero_add]
  omega

omit H_irreducible H_natDegree_pos in
/-- When `dH < d` the top term must be reduced modulo `H̃` before weighing, and the reduction obeys
the bound via `cofactor_top_reduction_weight_le`. -/
theorem xiPreTop_modByMonic_weight_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    (hlt : H.natDegree < R.natDegree) :
    weight (xiPreTop x₀ R H %ₘ monicize H) H D ≤
      (WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) : WithBot ℕ) := by
  classical
  rcases hHyp.dvd_evalX with ⟨Q, hQ⟩
  have hPne : Bivariate.evalX (Polynomial.C x₀) R ≠ 0 := evalX_ne_zero_of_hypotheses hHyp
  have hHne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hWne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHne
  have hQne : Q ≠ 0 := by
    intro hQ0
    apply hPne
    rw [hQ, hQ0, mul_zero]
  have hQdeg : Q.natDegree ≤ R.natDegree - H.natDegree := by
    have hproddeg : (H * Q).natDegree = H.natDegree + Q.natDegree := by
      rw [Polynomial.natDegree_mul hHne hQne]
    have hPdeg_eval : (Bivariate.evalX (Polynomial.C x₀) R).natDegree ≤ R.natDegree :=
        evalX_natDegree_le (Polynomial.C x₀) R
    rw [hQ] at hPdeg_eval
    omega
  have hD_HQ : Bivariate.totalDegree (H * Q) ≤ D := by
    simpa [← hQ] using hD_Rx0
  have hxi : xiPreTop x₀ R H = Polynomial.C
      ((R.natDegree : F[X]) * Q.coeff (R.natDegree - H.natDegree)) * Polynomial.X ^
          (R.natDegree - 1) := by
    change Polynomial.C
        (((Bivariate.evalX (Polynomial.C x₀) R.derivative).coeff (R.natDegree - 1) /
            H.leadingCoeff)) * Polynomial.X ^ (R.natDegree - 1) = Polynomial.C
            ((R.natDegree : F[X]) * Q.coeff (R.natDegree - H.natDegree)) * Polynomial.X ^
            (R.natDegree - 1)
    congr 1
    have hdpos : 0 < R.natDegree := by omega
    have hsucc : R.natDegree - 1 + 1 = R.natDegree := Nat.sub_add_cancel hdpos
    have hder := derivative_evalX_coeff x₀ R (R.natDegree - 1)
    rw [hsucc] at hder
    have hcoeffP : (Bivariate.evalX (Polynomial.C x₀) R).coeff R.natDegree = H.leadingCoeff *
        Q.coeff (R.natDegree - H.natDegree) := by
      have hmle : H.natDegree ≤ R.natDegree := by omega
      have hmulcoeff := Polynomial.coeff_mul_add_eq_of_natDegree_le (f := H) (g := Q)
          (df := H.natDegree) (dg := R.natDegree - H.natDegree) (le_rfl) hQdeg
      have hsum : H.natDegree + (R.natDegree - H.natDegree) = R.natDegree := Nat.add_sub_cancel'
          hmle
      rw [hQ]
      simpa [hsum, Polynomial.coeff_natDegree] using hmulcoeff
    rw [hder, hcoeffP]
    rw [mul_assoc]
    have hdiv : H.leadingCoeff ∣ H.leadingCoeff *
        (Q.coeff (R.natDegree - H.natDegree) * (R.natDegree : F[X])) := dvd_mul_right _ _
    have hcancel :=
        (EuclideanDomain.div_eq_iff_eq_mul_of_dvd
            (H.leadingCoeff * (Q.coeff (R.natDegree - H.natDegree) * (R.natDegree : F[X])) )
            H.leadingCoeff (Q.coeff (R.natDegree - H.natDegree) * (R.natDegree : F[X])) hWne hdiv).2
            (by ring)
    rw [hcancel]
    ring_nf
  simpa [hxi] using
      (cofactor_top_reduction_weight_le (H := H) hH (Q := Q) (d := R.natDegree) (D := D) hD_H hD_HQ
          hlt hQdeg)

omit H_irreducible H_natDegree_pos in
/-- Degree of the top coefficient after the exact division by `W`. -/
theorem xiPreTop_modByMonic_coeff_natDegree_le (x₀ : F) (hH : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    (hlt : H.natDegree < R.natDegree) (n : ℕ) :
    ((xiPreTop x₀ R H %ₘ monicize H).coeff n).natDegree ≤
      (R.natDegree - 1 - n) * (D - H.natDegree + 1) := by
  classical
  let f : F[X][Y] := xiPreTop x₀ R H %ₘ monicize H
  let m : ℕ := D - H.natDegree + 1
  have hwt : weight f H D ≤ (WithBot.some ((R.natDegree - 1) * m) : WithBot ℕ) := by
    dsimp [f, m]
    exact xiPreTop_modByMonic_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0 hlt
  have hHne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hHin : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHne)
  have hHdeg_le_D : H.natDegree ≤ D := by
    have htd : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hHin
    omega
  by_cases hcoeff : f.coeff n = 0
  · dsimp [f] at hcoeff ⊢
    simp only [hcoeff, Polynomial.natDegree_zero, zero_le]
  · have hnmem : n ∈ f.support := by
      rw [Polynomial.mem_support_iff]
      exact hcoeff
    have hineq := (weight_le_iff.mp hwt) n hnmem
    have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
    have hm_eq : D + 1 - Bivariate.natDegreeY H = m := by
      dsimp [m]
      rw [hbY]
      omega
    have hineq_m : n * m + (f.coeff n).natDegree ≤ (R.natDegree - 1) * m := by
      simpa only [hm_eq] using hineq
    have hineq_m' : (f.coeff n).natDegree + n * m ≤ (R.natDegree - 1) * m := by
      simpa only [Nat.add_comm] using hineq_m
    have hsub : (f.coeff n).natDegree ≤ (R.natDegree - 1) * m - n * m :=
      Nat.le_sub_of_add_le hineq_m'
    have hbound : (f.coeff n).natDegree ≤ (R.natDegree - 1 - n) * m := by
      rw [Nat.sub_mul]
      exact hsub
    exact hbound


omit H_irreducible H_natDegree_pos in
/-- The `𝒪`-weight of the top term when `dH < d`. -/
theorem xiPreTop_weight_over_𝒪_le_of_H_natDegree_lt_R_natDegree (x₀ : F) (hH : 0 < H.natDegree)
    (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D)
    (hlt : H.natDegree < R.natDegree) :
    regularWeight hH
      (Ideal.Quotient.mk (Ideal.span {monicize H}) (xiPreTop x₀ R H) : 𝒪 H) D
      ≤ WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) := by
  rw [regularWeight_mk]
  rw [weight_le_iff]
  intro n hn
  have hcoeff_bound :=
    xiPreTop_modByMonic_coeff_natDegree_le x₀ hH hHyp hRdeg hD_H hD_Rx0 hlt n
  have hbY : Bivariate.natDegreeY H = H.natDegree := rfl
  have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
  have hH_in : H.natDegree ∈ H.support :=
    Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
  have hHd_le_D : H.natDegree ≤ D := by
    have htd : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    omega
  have hq_ne_one : monicize H ≠ (1 : F[X][Y]) := by
    intro hq1
    have hnat : (monicize H).natDegree = (1 : F[X][Y]).natDegree := by
      rw [hq1]
    rw [natDegree_monicize hH] at hnat
    simp at hnat
    omega
  have hrem_nat_lt : (xiPreTop x₀ R H %ₘ monicize H).natDegree < H.natDegree := by
    have hltrem :=
      Polynomial.natDegree_modByMonic_lt (xiPreTop x₀ R H) (monicize_monic H hH) hq_ne_one
    rwa [natDegree_monicize hH] at hltrem
  have hn_le_rem : n ≤ (xiPreTop x₀ R H %ₘ monicize H).natDegree :=
    Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
  have hn_lt_H : n < H.natDegree := lt_of_le_of_lt hn_le_rem hrem_nat_lt
  have hn_le_Rminus1 : n ≤ R.natDegree - 1 := by
    omega
  rw [hbY]
  rw [show D + 1 - H.natDegree = D - H.natDegree + 1 by omega]
  calc
    n * (D - H.natDegree + 1) + ((xiPreTop x₀ R H %ₘ monicize H).coeff n).natDegree
        ≤ n * (D - H.natDegree + 1) + (R.natDegree - 1 - n) * (D - H.natDegree + 1) := by
          exact Nat.add_le_add_left hcoeff_bound _
    _ = (n + (R.natDegree - 1 - n)) * (D - H.natDegree + 1) := by
          rw [Nat.add_mul]
    _ = (R.natDegree - 1) * (D - H.natDegree + 1) := by
          have hsum : n + (R.natDegree - 1 - n) = R.natDegree - 1 := by omega
          rw [hsum]

omit H_irreducible H_natDegree_pos in
/-- The `𝒪`-weight of the top term, covering both `dH = d` and `dH < d`. -/
theorem xiPreTop_weight_over_𝒪_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ R.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_Rx0 : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D) :
    regularWeight hH
      (Ideal.Quotient.mk (Ideal.span {monicize H}) (xiPreTop x₀ R H) : 𝒪 H) D
      ≤ WithBot.some ((R.natDegree - 1) * (D - H.natDegree + 1)) := by
  classical
  have hHleR : H.natDegree ≤ R.natDegree := natDegree_H_le_natDegree_R_of_hypotheses hHyp
  rcases lt_or_eq_of_le hHleR with hlt | heq
  · exact xiPreTop_weight_over_𝒪_le_of_H_natDegree_lt_R_natDegree x₀ hH hHyp hRdeg hD_H hD_Rx0 hlt
  · have hH_ne : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH
    have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hH_ne)
    have hHleD : H.natDegree ≤ D := by
      have hcoeff_total := Bivariate.coeff_totalDegree_le H hH_in
      omega
    have hRleD : R.natDegree ≤ D := by omega
    have hsub : D + 1 - R.natDegree = D - R.natDegree + 1 := by omega
    unfold xiPreTop
    let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
    let d : ℕ := R.natDegree
    let W : F[X] := H.leadingCoeff
    have hcoeff0 : (P.coeff (d - 1) / W).natDegree = 0 := by
      dsimp [P, d, W]
      exact xiPreTop_coeff_natDegree_zero_of_H_natDegree_eq_R_natDegree x₀ hH hHyp hRdeg heq
    refine le_trans (regularWeight_mk_le hD_H hH _) ?_
    refine le_trans (weight_C_mul_X_pow_le H D (P.coeff (d - 1) / W) (d - 1)) ?_
    rw [WithBot.coe_le_coe]
    dsimp [P, d, W]
    rw [hcoeff0]
    rw [Bivariate.natDegreeY]
    rw [heq]
    rw [hsub]
    omega

omit H_irreducible H_natDegree_pos in
/-- The explicit representative of `ξ` splits as low part plus top term; this is how its weight
bound is assembled. -/
theorem xiPre_eq_lower_add_top (x₀ : F) (hRdeg : 2 ≤ R.natDegree) :
    xiPre x₀ R H = xiPreLower x₀ R H + xiPreTop x₀ R H := by
  simp only [xiPre, xiPreLower, xiPreTop, hRdeg, if_pos]


/-- The weight bound `Λ(ξ) ≤ (dY - 1)·(D - dH + 1)`.

The explicit hypothesis `2 ≤ R.natDegree` is needed because the paper uses `W^(d-2)`, while
Lean's natural-number exponent would otherwise totalize the low-degree cases by truncation. -/
lemma xi_weight_le (x₀ : F) (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    {D : ℕ} (hD_H : D ≥ Bivariate.totalDegree H)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)) :
    regularWeight hH (xi x₀ R H hHyp) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  have hRdeg' : 2 ≤ R.natDegree := by
    simpa [Bivariate.natDegreeY] using hRdeg
  have hD_H' : Bivariate.totalDegree H ≤ D := hD_H
  have hD_Rx0' : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) ≤ D := hD_Rx0
  unfold xi
  rw [xiPre_eq_lower_add_top x₀ hRdeg']
  refine (regularWeight_add_le hD_H' hH
    (Ideal.Quotient.mk (Ideal.span {monicize H}) (xiPreLower x₀ R H) : 𝒪 H)
    (Ideal.Quotient.mk (Ideal.span {monicize H}) (xiPreTop x₀ R H) : 𝒪 H)).trans ?_
  apply max_le
  · exact (regularWeight_mk_le hD_H' hH (xiPreLower x₀ R H)).trans
      (by simpa [Bivariate.natDegreeY] using xiPreLower_weight_le x₀ hHyp hH hRdeg' hD_H' hD_Rx0')
  · simpa [Bivariate.natDegreeY] using
      (xiPreTop_weight_over_𝒪_le x₀ hH hHyp hRdeg' hD_H' hD_Rx0')


end HenselNumerators
end HenselSetup
end RationalFunctions
