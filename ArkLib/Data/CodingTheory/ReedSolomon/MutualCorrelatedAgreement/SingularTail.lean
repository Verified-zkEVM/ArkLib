/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.HybridConstants
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.AutomaticBounds
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.Data.Polynomial.ResultantSpecialization

/-!
# Squarefree singular tails and list envelopes

Let `A : R[X][X]` be an equation in a root variable `Y` whose coefficients are polynomials in an
ordinary variable, and let `U : R[X]` be a content that does not depend on `Y`. The *singular
tail* `singularTail U A r` is `U` times the derivative resultant
`resultant A A.derivative r (r - 1)` of `A` at the declared degree `r`. A common root of a
specialization of `A` and of its derivative kills the image of the singular tail, for every
specialization, including one that lowers the degree of `A` in `Y`.

The degree of the singular tail in the ordinary variable is bounded through natural-number
envelopes. If `B` bounds the total degree budget and `M` bounds the degree in `Y`, the envelope is
`ordinaryDegreeEnvelope B M = max B ((2 * M - 1) * B - M ^ 2)`; the second argument comes from
the derivative-resultant bound `(2 * r - 1) * j - r ^ 2` and the first covers the degrees `r ≤ 1`
where that bound is truncated. The analogous envelope in a challenge variable is
`resultantChallengeEnvelope H M = (2 * M - 1) * H`.

The ordinary envelope also bounds a first-order squarefree list expression. Under a common
incidence and degree bound, this expression is at most `7 C³ n q²`.
For the automatic first-order parameters, the same expression is bounded by a rate-only constant
times `n / eta²`.

## Main definitions

* `ReedSolomon.FirstOrder.Squarefree.ordinaryDegreeEnvelope`: `max B ((2 * M - 1) * B - M ^ 2)`.
* `ReedSolomon.FirstOrder.Squarefree.resultantChallengeEnvelope`: `(2 * M - 1) * H`.
* `ReedSolomon.FirstOrder.Squarefree.singularTail`: the content times the derivative resultant.

## Main statements

* `ReedSolomon.FirstOrder.Squarefree.content_add_resultantDegree_le` and
  `ReedSolomon.FirstOrder.Squarefree.content_add_resultantChallenge_le`: a content degree plus a
  derivative-resultant degree fits the corresponding envelope.
* `ReedSolomon.FirstOrder.Squarefree.natDegree_singularTail_le`: the singular tail has degree at
  most `ordinaryDegreeEnvelope B M`.
* `ReedSolomon.FirstOrder.Squarefree.singularTail_map_eq_zero_of_common_root`: a common root of a
  specialized equation and its derivative kills the specialized singular tail.
* `ReedSolomon.FirstOrder.Squarefree.squarefreeListExpression_le`: the first-order list expression
  is bounded by a product envelope.
* `ReedSolomon.FirstOrder.Squarefree.squarefreeListExpression_le_rate_envelope`: the list
  expression is bounded by `7 C³ n q²` under common incidence and degree bounds.
* `ReedSolomon.FirstOrder.Squarefree.automaticSquarefreeListExpression_le`: the automatic
  parameters give an inverse-square slack bound for the list expression.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon.FirstOrder.Squarefree

open Polynomial
open ReedSolomon.HiddenDerivative

section Envelopes

/-- The degree envelope `max B ((2 * M - 1) * B - M ^ 2)` in the ordinary variable, for a total
degree budget `B` and a bound `M` on the degree in the root variable. -/
def ordinaryDegreeEnvelope (B M : ℕ) : ℕ :=
  max B ((2 * M - 1) * B - M ^ 2)

/-- With root degree bound `0`, the ordinary envelope is the budget `B`. -/
@[simp]
theorem ordinaryDegreeEnvelope_zero (B : ℕ) : ordinaryDegreeEnvelope B 0 = B := by
  simp [ordinaryDegreeEnvelope]

/-- The budget `B` is at most the ordinary envelope. -/
theorem self_le_ordinaryDegreeEnvelope (B M : ℕ) : B ≤ ordinaryDegreeEnvelope B M :=
  le_max_left _ _

/-- The truncated resultant bound `(2 * M - 1) * B - M ^ 2` is at most the ordinary envelope. -/
theorem mul_sub_sq_le_ordinaryDegreeEnvelope (B M : ℕ) :
    (2 * M - 1) * B - M ^ 2 ≤ ordinaryDegreeEnvelope B M :=
  le_max_right _ _

/-- **Content plus derivative resultant.** Let a content have degree `bU`, a derivative resultant
of declared root degree `r` have degree `d` with `d + r ^ 2 ≤ (2 * r - 1) * j`, and let
`bU + j ≤ B`. If `r ≤ M ≤ B`, then `bU + d ≤ ordinaryDegreeEnvelope B M`.

The resultant hypothesis is in the additive form produced by the determinant bound, so it loses
nothing to truncated subtraction. `M ≤ B` is needed: for `B = 10`, `r = 5`, `M = 100`, `j = 10`,
`bU = 0`, `d = 65` all other hypotheses hold and the envelope is `10`. -/
theorem content_add_resultantDegree_le {B M bU j r d : ℕ} (hrM : r ≤ M) (hMB : M ≤ B)
    (hbudget : bU + j ≤ B) (hresultant : d + r ^ 2 ≤ (2 * r - 1) * j) :
    bU + d ≤ ordinaryDegreeEnvelope B M := by
  rcases r with _ | s
  · refine (self_le_ordinaryDegreeEnvelope B M).trans' ?_
    simp at hresultant
    omega
  refine (mul_sub_sq_le_ordinaryDegreeEnvelope B M).trans' (Nat.le_sub_of_add_le ?_)
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hrM
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le hMB
  rw [show 2 * (s + 1 + e) - 1 = 2 * s + 2 * e + 1 by omega]
  rw [show 2 * (s + 1) - 1 = 2 * s + 1 by omega] at hresultant
  nlinarith [Nat.mul_le_mul_left (2 * s + 1) hbudget, Nat.zero_le (e * f), Nat.zero_le (s * bU)]

/-- The ordinary envelope is at most `B + 2 * B * M`. -/
theorem ordinaryDegreeEnvelope_le (B M : ℕ) : ordinaryDegreeEnvelope B M ≤ B + 2 * B * M := by
  refine max_le (Nat.le_add_right _ _) ((Nat.sub_le _ _).trans ?_)
  calc (2 * M - 1) * B ≤ 2 * M * B := Nat.mul_le_mul_right B (Nat.sub_le _ _)
    _ ≤ B + 2 * B * M := by nlinarith

/-- The first-order squarefree list expression is bounded by
`4 λ D B M + 2 B M + B`. -/
theorem squarefreeListExpression_le
    {D B M : ℕ} {lambda : ℝ}
    (hD : 1 ≤ D) (hM : 1 ≤ M) (hMB : M ≤ B) (hlambda : 0 ≤ lambda) :
    (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) * lambda +
        ordinaryDegreeEnvelope B M ≤
      4 * D * B * M * lambda + 2 * B * M + B := by
  have hstageNat :
      firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) ≤ 4 * D * B * M := by
    calc
      _ ≤ 2 * D * M * (2 * B - M) :=
        firstOrderCurveFiberStageOne_regularTaylorExponent_le hD hM hMB
      _ ≤ 4 * D * B * M := by
        have hsub : 2 * B - M ≤ 2 * B := Nat.sub_le _ _
        calc
          2 * D * M * (2 * B - M) ≤ 2 * D * M * (2 * B) :=
            Nat.mul_le_mul_left _ hsub
          _ = 4 * D * B * M := by ring
  have hstage :
      (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) ≤
        4 * D * B * M := by
    exact_mod_cast hstageNat
  have htail : (ordinaryDegreeEnvelope B M : ℝ) ≤ B + 2 * B * M := by
    exact_mod_cast ordinaryDegreeEnvelope_le B M
  nlinarith [mul_le_mul_of_nonneg_right hstage hlambda]

/-- A common incidence ratio and two degree caps give the inverse-square slack envelope. -/
theorem squarefreeListExpression_le_rate_envelope
    {C q lambda : ℝ} {n D B M : ℕ}
    (hC : 1 ≤ C) (hq : 1 ≤ q) (hn : 1 ≤ n) (hD : 1 ≤ D) (hDn : D ≤ n)
    (hM : 1 ≤ M) (hMB : M ≤ B) (hlambda0 : 0 ≤ lambda) (hlambda : lambda ≤ C)
    (hB : (B : ℝ) ≤ C * q) :
    (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) * lambda +
        ordinaryDegreeEnvelope B M ≤
      7 * C ^ 3 * n * q ^ 2 := by
  have hraw := squarefreeListExpression_le hD hM hMB hlambda0
  have hD' : (D : ℝ) ≤ n := by exact_mod_cast hDn
  have hM' : (M : ℝ) ≤ C * q := (Nat.cast_le.mpr hMB).trans hB
  have hrough :
      4 * (D : ℝ) * B * M * lambda + 2 * (B : ℝ) * M + B ≤
        4 * (n : ℝ) * (C * q) * (C * q) * C +
          2 * (C * q) * (C * q) + C * q := by
    gcongr
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hx : 1 ≤ C * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hq)]
  have hCN : 1 ≤ C * (n : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hN)]
  have htwo : (C * q) * (C * q) ≤ C ^ 3 * n * q ^ 2 := by
    have hnonneg : 0 ≤ (C * q) ^ 2 := sq_nonneg _
    have hmul : (C * q) ^ 2 ≤ (C * q) ^ 2 * (C * n) := by
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hCN)]
    nlinarith [hmul]
  have hone : C * q ≤ C ^ 3 * n * q ^ 2 := by
    have hsquare : C * q ≤ (C * q) ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hC0 hq0) (sub_nonneg.mpr hx)]
    exact hsquare.trans (by simpa only [pow_two] using htwo)
  calc
    (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) * lambda +
          ordinaryDegreeEnvelope B M ≤
        4 * (D : ℝ) * B * M * lambda + 2 * (B : ℝ) * M + B := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hraw
    _ ≤ 4 * (n : ℝ) * (C * q) * (C * q) * C +
          2 * (C * q) * (C * q) + C * q := hrough
    _ = 4 * (C ^ 3 * n * q ^ 2) + 2 * ((C * q) * (C * q)) + C * q := by ring
    _ ≤ 4 * (C ^ 3 * n * q ^ 2) + 2 * (C ^ 3 * n * q ^ 2) +
          C ^ 3 * n * q ^ 2 := by gcongr
    _ = 7 * C ^ 3 * n * q ^ 2 := by ring

/-- A rate-only coefficient for the squarefree inverse-square list envelope. -/
noncomputable def automaticSquarefreeListBoundConstant (rho : ℝ) : ℝ :=
  7 * automaticRateEnvelopeConstant rho ^ 3

/-- On the positive-derivative branch, the automatic squarefree list expression is bounded by a
rate-only constant times `n / eta²`. -/
theorem automaticSquarefreeListExpression_le
    {rho eta : ℝ} {n D A : ℕ}
    (hrho : 0 < rho) (hrhoOne : rho < 1) (heta : 0 < eta)
    (haOne : firstOrderRateThreshold rho + eta < 1)
    (hn : 1 ≤ n) (hD : 1 ≤ D) (hDn : D ≤ n) (hDA : D < A)
    (hDrate : (D : ℝ) ≤ rho * n)
    (hA : (firstOrderRateThreshold rho + eta) * n ≤ A)
    (hM : 1 ≤ automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)) :
    let B := automaticJetDegree rho (firstOrderRateThreshold rho + eta)
    let M := automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)
    let lambda := agreementIncidenceRatio n D A
    (firstOrderCurveFiberStageOne (D + 1) B M (regularTaylorExponent D) : ℝ) * lambda +
        ordinaryDegreeEnvelope B M ≤
      automaticSquarefreeListBoundConstant rho * n / eta ^ 2 := by
  dsimp only
  let C := automaticRateEnvelopeConstant rho
  let q := 1 / eta
  let B := automaticJetDegree rho (firstOrderRateThreshold rho + eta)
  let M := automaticDerivativeCap rho (firstOrderRateThreshold rho + eta)
  let lambda := agreementIncidenceRatio n D A
  have hC : 1 ≤ C := automaticRateEnvelopeConstant_one_le rho
  have hetaOne : eta ≤ 1 := by
    have hgap := automatic_eta_lt_rateGap haOne
    have hthresholdPos := (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans' hrho
    unfold automaticRateGap at hgap
    linarith
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact (one_le_div heta).2 hetaOne
  have hlambda0 : 0 ≤ lambda := by
    dsimp only [lambda]
    unfold agreementIncidenceRatio
    positivity
  have hthresholdGap : 0 < firstOrderRateThreshold rho - rho :=
    sub_pos.mpr (rate_lt_firstOrderRateThreshold hrho hrhoOne)
  have hlambdaRate := agreementIncidenceRatio_le_one_div_sub hDn hDA hDrate hA
    (show rho < firstOrderRateThreshold rho + eta by
      exact (rate_lt_firstOrderRateThreshold hrho hrhoOne).trans (by linarith))
  have hlambda : lambda ≤ C := by
    calc
      lambda ≤ 1 / (firstOrderRateThreshold rho + eta - rho) := hlambdaRate
      _ ≤ 1 / (firstOrderRateThreshold rho - rho) := by
        exact div_le_div_of_nonneg_left zero_le_one hthresholdGap (by linarith)
      _ ≤ C := automaticRateGapInv_le_rateEnvelopeConstant rho
  have hB : (B : ℝ) ≤ C * q := by
    calc
      (B : ℝ) ≤ automaticJetBoundConstant rho / eta :=
        automaticJetDegree_le_inv_eta hrho hrhoOne heta haOne
      _ = automaticJetBoundConstant rho * q := by dsimp only [q]; ring
      _ ≤ C * q := by
        gcongr
        exact automaticJetBoundConstant_le_envelope rho
  have hMB : M ≤ B := by
    dsimp only [M, B]
    unfold automaticDerivativeCap
    exact min_le_right _ _
  have hbound := squarefreeListExpression_le_rate_envelope hC hq hn hD hDn
    (by simpa only [M] using hM) hMB hlambda0 hlambda hB
  dsimp only [C, q, B, M, lambda] at hbound ⊢
  unfold automaticSquarefreeListBoundConstant
  field_simp [ne_of_gt heta] at hbound ⊢
  nlinarith

/-- The degree envelope `(2 * M - 1) * H` in the challenge variable, for a challenge-degree budget
`H` and a bound `M` on the degree in the root variable. -/
def resultantChallengeEnvelope (H M : ℕ) : ℕ :=
  (2 * M - 1) * H

/-- With root degree bound `0`, the challenge envelope is `0`. -/
@[simp]
theorem resultantChallengeEnvelope_zero (H : ℕ) : resultantChallengeEnvelope H 0 = 0 := by
  simp [resultantChallengeEnvelope]

/-- The challenge envelope is monotone in both arguments. -/
theorem resultantChallengeEnvelope_mono {H M h r : ℕ} (hh : h ≤ H) (hr : r ≤ M) :
    resultantChallengeEnvelope h r ≤ resultantChallengeEnvelope H M :=
  Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hr) 1) hh

/-- **Content plus derivative resultant in the challenge variable.** If a content has challenge
degree `hU`, a derivative resultant of root degree `r ≤ M` has challenge degree
`d ≤ (2 * r - 1) * hV`, and `hU + hV ≤ H`, then `hU + d ≤ resultantChallengeEnvelope H M`.

`0 < M` is needed: for `M = r = 0`, `H = hU = 1` and `hV = d = 0` the envelope is `0`. -/
theorem content_add_resultantChallenge_le {H M hU hV r d : ℕ} (hM : 0 < M) (hrM : r ≤ M)
    (hbudget : hU + hV ≤ H) (hresultant : d ≤ (2 * r - 1) * hV) :
    hU + d ≤ resultantChallengeEnvelope H M := by
  have hone : 1 ≤ 2 * M - 1 := by omega
  calc hU + d ≤ hU + (2 * M - 1) * hV :=
        Nat.add_le_add_left (hresultant.trans
          (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hrM) 1))) _
    _ ≤ (2 * M - 1) * hU + (2 * M - 1) * hV :=
        Nat.add_le_add_right (Nat.le_mul_of_pos_left _ hone) _
    _ = (2 * M - 1) * (hU + hV) := (Nat.mul_add _ _ _).symm
    _ ≤ resultantChallengeEnvelope H M := Nat.mul_le_mul_left _ hbudget

/-- The challenge envelope is at most `2 * H * M`. -/
theorem resultantChallengeEnvelope_le (H M : ℕ) : resultantChallengeEnvelope H M ≤ 2 * H * M :=
  (Nat.mul_le_mul_right H (Nat.sub_le _ _)).trans_eq (by ring)

end Envelopes

section SingularTail

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The singular tail `U * resultant A A.derivative r (r - 1)`: a content `U` times the
derivative resultant of `A` at the declared degree `r`. -/
noncomputable def singularTail (U : R[X]) (A : R[X][X]) (r : ℕ) : R[X] :=
  U * resultant A A.derivative r (r - 1)

/-- **Degree of the singular tail.** If `U` has degree at most `bU`, the coefficients of `A` satisfy
the triangle `i + (A.coeff i).natDegree ≤ j` for `i ≤ r`, `bU + j ≤ B` and `r ≤ M ≤ B`, then the
singular tail has degree at most `ordinaryDegreeEnvelope B M`. -/
theorem natDegree_singularTail_le (U : R[X]) (A : R[X][X]) {B M bU j r : ℕ} (hrM : r ≤ M)
    (hMB : M ≤ B) (hcontent : U.natDegree ≤ bU) (hbudget : bU + j ≤ B)
    (hcoeff : ∀ i ≤ r, i + (A.coeff i).natDegree ≤ j) :
    (singularTail U A r).natDegree ≤ ordinaryDegreeEnvelope B M :=
  natDegree_mul_le.trans ((Nat.add_le_add_right hcontent _).trans
    (content_add_resultantDegree_le hrM hMB hbudget
      (natDegree_resultant_derivative_padded_add_sq_le A r j hcoeff)))

/-- **Common roots kill the singular tail.** If `A` has degree at most `r > 0` and, for a ring
hom `f : R[X] →+* S`, some `u` is a root of both `A.map f` and its derivative, then
`f (singularTail U A r) = 0`. The specialization may lower the degree of `A`. -/
theorem singularTail_map_eq_zero_of_common_root (U : R[X]) (A : R[X][X]) {r : ℕ} (hr : 0 < r)
    (hdegree : A.natDegree ≤ r) (f : R[X] →+* S) (u : S) (hroot : (A.map f).eval u = 0)
    (hderivative : (A.map f).derivative.eval u = 0) :
    f (singularTail U A r) = 0 := by
  rw [singularTail, map_mul, map_resultant_eq_zero_of_common_root f A A.derivative hdegree
    ((natDegree_derivative_le A).trans (Nat.sub_le_sub_right hdegree 1)) (Or.inl hr.ne') u hroot
    (by rwa [← derivative_map]), mul_zero]

end SingularTail

end ReedSolomon.FirstOrder.Squarefree
