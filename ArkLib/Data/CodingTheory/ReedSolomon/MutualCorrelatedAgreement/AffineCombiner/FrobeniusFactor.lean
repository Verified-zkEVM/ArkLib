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

A root `P` of `Q` along the line `α + β X` gives the root `P(X^s)` of `R` along the line
`α^{1/s} + β^{1/s} X`.

## Main statements

* `ReedSolomon.exists_affineFrobeniusFactor`: the normalized factor, its degree bounds, and the
  transport of roots along lines.

## References

This is the Frobenius normalization of Section 4 of [CWYZ26].

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial

variable {E : Type*} [Field E]

/-- Expansion in the root variable is the substitution of `Z ^ s` for `Z`. -/
private theorem rootExpansion_eq_variablePowerSubstitution (s : ℕ)
    (G : MvPolynomial AffineVar E) :
    MvPolynomial.rootExpansion s G =
      MvPolynomial.variablePowerSubstitution (fun v : AffineVar ↦ v.elim s fun _ ↦ 1) G := by
  let φ : MvPolynomial AffineVar E →ₐ[E] MvPolynomial AffineVar E :=
    (MvPolynomial.optionEquivLeft E (Fin 2)).symm.toAlgHom.comp
      (((Polynomial.expand (MvPolynomial (Fin 2) E) s).restrictScalars E).comp
        (MvPolynomial.optionEquivLeft E (Fin 2)).toAlgHom)
  have hφ :
      φ = MvPolynomial.variablePowerSubstitution fun v : AffineVar ↦ v.elim s fun _ ↦ 1 := by
    apply MvPolynomial.algHom_ext
    rintro (_ | i)
    · simp [φ]
    · simp [φ]
  exact DFunLike.congr_fun hφ G

/-- Substituting `X^s, Y^s`, then evaluating on the `s`-th root line, expands the evaluation. -/
private theorem affineLineEval_variablePowerSubstitution (p e : ℕ) [ExpChar E p]
    [PerfectRing E p] (α β : E) (P : E[X]) (Q : MvPolynomial AffineVar E) :
    affineLineEval ((iterateFrobeniusEquiv E p e).symm α) ((iterateFrobeniusEquiv E p e).symm β)
        (expand E (p ^ e) P)
        (MvPolynomial.variablePowerSubstitution (fun v : AffineVar ↦ v.elim 1 fun _ ↦ p ^ e) Q) =
      expand E (p ^ e) (affineLineEval α β P Q) := by
  rw [affineLineEval, affineLineEval, MvPolynomial.variablePowerSubstitution,
    MvPolynomial.aeval_bind₁, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext v
  rcases v with _ | i
  · simp
  · fin_cases i
    · simp
    · simp only [Option.elim_some]
      have hfr (x : E) : ((iterateFrobeniusEquiv E p e).symm x) ^ p ^ e = x := by
        rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
      simp [affineMultiplier, add_pow_expChar_pow, mul_pow, ← C_pow, hfr]

/-- An irreducible `Q` of positive `Z`-degree has a Frobenius normalization `R`.

* `R` is irreducible with nonzero `Z`-derivative.
* Its `(Y, Z)`-degree is at most that of `Q`.
* The exponent `s = p^e` is at most the `Z`-degree of `Q`.
* A root `P` of `Q` on the line `α + β X` gives the root `P(X^s)` of `R` on the line
  `α^{1/s} + β^{1/s} X`. -/
theorem exists_affineFrobeniusFactor (p : ℕ) [ExpChar E p] [PerfectRing E p]
    {Q : MvPolynomial AffineVar E} (hirr : Irreducible Q) (hpos : 0 < Q.degreeOf none) :
    ∃ e, ∃ R : MvPolynomial AffineVar E, Irreducible R ∧ MvPolynomial.pderiv none R ≠ 0 ∧
      R.weightedTotalDegree affineYZWeight ≤ Q.weightedTotalDegree affineYZWeight ∧
      p ^ e ≤ Q.degreeOf none ∧ ∀ α β P, affineLineEval α β P Q = 0 →
        affineLineEval ((iterateFrobeniusEquiv E p e).symm α)
          ((iterateFrobeniusEquiv E p e).symm β) (expand E (p ^ e) P) R = 0 := by
  obtain ⟨e, G, hder, hGQ, hdeg, hGpos, hGirr, -⟩ :=
    MvPolynomial.exists_irreducible_frobeniusContraction_expChar p hpos hirr
  have hs : p ^ e ≠ 0 := pow_ne_zero e (expChar_pos E p).ne'
  refine ⟨e, MvPolynomial.inverseFrobeniusTwist p e G,
    (MvPolynomial.irreducible_inverseFrobeniusTwist_iff p e).mpr hGirr,
    (MvPolynomial.pderiv_inverseFrobeniusTwist_ne_zero_iff p e G none).mpr hder, ?_,
    hdeg ▸ Nat.le_mul_of_pos_left _ hGpos, fun α β P hroot ↦ ?_⟩
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
  · have hF : Q = MvPolynomial.variablePowerSubstitution
        (fun v : AffineVar ↦ v.elim (p ^ e) fun _ ↦ 1) G := by
      rw [← hGQ, rootExpansion_eq_variablePowerSubstitution]
    have h := congrArg (affineLineEval ((iterateFrobeniusEquiv E p e).symm α)
      ((iterateFrobeniusEquiv E p e).symm β) (expand E (p ^ e) P))
      (MvPolynomial.inverseFrobeniusTwist_pow_eq_variablePowerSubstitution p e
        (q := fun v : AffineVar ↦ v.elim 1 fun _ ↦ p ^ e) (fun v ↦ by cases v <;> simp) hF)
    rw [map_pow, affineLineEval_variablePowerSubstitution, hroot, map_zero] at h
    exact pow_eq_zero_iff hs |>.mp h

end ReedSolomon
