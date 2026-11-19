/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.LineRoots
public import ArkLib.Data.MvPolynomial.FrobeniusContraction
public import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback

/-!
# Frobenius normalization of an irreducible factor

Over a perfect field of exponential characteristic `p`, let `Q` be irreducible with positive
`Z`-degree.
There is an irreducible `R` with nonzero `Z`-derivative, built so that `Q(X^s, Y^s, Z) = R^s`,
where `s = p^e`.

A root `P` of `Q` along a multiplier `M` gives the root `P(X^s)` of `R` along `M^{1/s}`.
The multiplier `M^{1/s}` applies the inverse of the `s`-power map to each coefficient of `M`.
For the line `α + β X` it is the line `α^{1/s} + β^{1/s} X`.

## Main statements

* `ReedSolomon.exists_frobeniusFactor`: the normalized factor, its degree bounds, and the
  transport of roots along multipliers.

## References

This is the Frobenius normalization of Section 4 of [CWYZ26].
Appendix A of [CWYZ26] uses it along the multipliers of Reed–Muller codes.

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

variable {E : Type*} [Field E]

/-- Substituting `X^s, Y^s`, then evaluating along the `s`-th root multiplier, expands. -/
private theorem multiplierEval_variablePowerSubstitution (p e : ℕ) [ExpChar E p]
    [PerfectRing E p] (M P : E[X]) (Q : MvPolynomial AffineVar E) :
    multiplierEval (M.map ((iterateFrobeniusEquiv E p e).symm : E →+* E)) (expand E (p ^ e) P)
        (MvPolynomial.variablePowerSubstitution (fun v : AffineVar ↦ v.elim 1 fun _ ↦ p ^ e) Q) =
      expand E (p ^ e) (multiplierEval M P Q) := by
  rw [multiplierEval, multiplierEval, MvPolynomial.variablePowerSubstitution,
    MvPolynomial.aeval_bind₁, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext v
  rcases v with _ | i
  · simp
  · fin_cases i
    · simp
    · have hid : (iterateFrobenius E p e).comp ((iterateFrobeniusEquiv E p e).symm : E →+* E) =
          RingHom.id E := RingHom.ext fun x ↦ by
        rw [RingHom.comp_apply, ← coe_iterateFrobeniusEquiv]
        simp
      simp only [map_pow, MvPolynomial.aeval_X, Option.elim_some, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      rw [← map_iterateFrobenius_expand p, map_expand, map_map, hid, map_id]

/-- An irreducible `Q` of positive `Z`-degree has a Frobenius normalization `R`
over a perfect field of exponential characteristic `p`.

* `R` is irreducible with nonzero `Z`-derivative.
* The `(Y, Z)`-degree of `R` is at most that of `Q`.
* The exponent `s = p^e`, for some `e : ℕ`, is at most the `Z`-degree of `Q`.
* `R^s = Q(X^s, Y^s, Z)`.
* A root `P` of `Q` along a multiplier `M` gives the root `P(X^s)` of `R` along the multiplier
  obtained by taking the `s`-th root of each coefficient of `M`. -/
theorem exists_frobeniusFactor (p : ℕ) [ExpChar E p] [PerfectRing E p]
    {Q : MvPolynomial AffineVar E} (hirr : Irreducible Q) (hpos : 0 < Q.degreeOf none) :
    ∃ e, ∃ R : MvPolynomial AffineVar E, Irreducible R ∧ MvPolynomial.pderiv none R ≠ 0 ∧
      R.weightedTotalDegree affineYZWeight ≤ Q.weightedTotalDegree affineYZWeight ∧
      p ^ e ≤ Q.degreeOf none ∧
      R ^ (p ^ e) = MvPolynomial.variablePowerSubstitution
        (fun v : AffineVar ↦ v.elim 1 fun _ ↦ p ^ e) Q ∧ ∀ M P, multiplierEval M P Q = 0 →
        multiplierEval (M.map ((iterateFrobeniusEquiv E p e).symm : E →+* E))
          (expand E (p ^ e) P) R = 0 := by
  obtain ⟨e, G, hder, hGQ, hdeg, hGpos, hGirr, -⟩ :=
    MvPolynomial.exists_irreducible_frobeniusContraction_expChar p hpos hirr
  have hs : p ^ e ≠ 0 := pow_ne_zero e (expChar_pos E p).ne'
  have hF : Q = MvPolynomial.variablePowerSubstitution
      (fun v : AffineVar ↦ v.elim (p ^ e) fun _ ↦ 1) G := by
    rw [← hGQ, MvPolynomial.rootExpansion_eq_variablePowerSubstitution]
  have hidentity := MvPolynomial.inverseFrobeniusTwist_pow_eq_variablePowerSubstitution p e
    (q := fun v : AffineVar ↦ v.elim 1 fun _ ↦ p ^ e) (fun v ↦ by cases v <;> simp) hF
  refine ⟨e, MvPolynomial.inverseFrobeniusTwist p e G,
    (MvPolynomial.irreducible_inverseFrobeniusTwist_iff p e).mpr hGirr,
    (MvPolynomial.pderiv_inverseFrobeniusTwist_ne_zero_iff p e G none).mpr hder, ?_,
    hdeg ▸ Nat.le_mul_of_pos_left _ hGpos, hidentity, fun M P hroot ↦ ?_⟩
  · have hG : G = MvPolynomial.rootContraction (p ^ e) Q := by
      rw [← hGQ, MvPolynomial.rootContraction_rootExpansion hs]
    rw [MvPolynomial.inverseFrobeniusTwist, MvPolynomial.weightedTotalDegree,
      MvPolynomial.support_map_of_injective _ (iterateFrobeniusEquiv E p e).symm.injective]
    refine Finset.sup_le fun m hm ↦ ?_
    have hm' : m.some.optionElim (m none * p ^ e) ∈ Q.support := by
      rw [MvPolynomial.mem_support_iff] at hm ⊢
      rwa [hG, MvPolynomial.coeff_rootContraction hs] at hm
    refine le_trans ?_ (MvPolynomial.le_weightedTotalDegree affineYZWeight hm')
    rw [weight_affineYZWeight, weight_affineYZWeight]
    simp only [Finsupp.optionElim_apply_none, Finsupp.optionElim_apply_some, Finsupp.some_apply]
    have := Nat.le_mul_of_pos_right (m none) (Nat.pos_of_ne_zero hs)
    omega
  · have h := congrArg (multiplierEval (M.map ((iterateFrobeniusEquiv E p e).symm : E →+* E))
      (expand E (p ^ e) P)) hidentity
    rw [map_pow, multiplierEval_variablePowerSubstitution, hroot, map_zero] at h
    exact pow_eq_zero_iff hs |>.mp h

end ReedSolomon
