/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Semantics
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Newton

/-!
# Precision doubling and specialization of quotient Newton lifting

The proof works at an arbitrary geometric root of `h`, so quotient coefficients become ordinary
field coefficients. The multivariate Taylor formula puts its quadratic error in `(T^m)^2`.
The branch correction therefore gains `m` coefficients. The inverse update squares its own
error, restoring the same precision after the branch changes.

`newtonLoop_correct` maintains these two invariants and proves that the finite fuel bound cannot
truncate a run prematurely. `newtonLift_specializes` then identifies the computed series with
any polynomial solution of degree below `k`. No enumeration or base-field assumption on the
parameter root is used.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
open CompPoly CompPoly.CPolynomial
variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]
variable {L : Type*} [Field L]
noncomputable section

omit [BEq E] [LawfulBEq E] in
section
/-- The bivariate equation after substituting the centered variable and a branch series. -/
def evalAt (ι : E →+* L) (q : MvPolynomial (Fin 2) E) (c : L) (S : Polynomial L) : Polynomial L :=
  MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X + Polynomial.C c, S] q

/-- A perturbation divisible by `T^m` has Taylor error divisible by `T^(2m)`. -/
theorem residual_quadratic (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (c : L) (S d : Polynomial L) (m : ℕ) (hd : Polynomial.X ^ m ∣ d) :
    Polynomial.X ^ (2 * m) ∣ evalAt ι q c (S + d) - evalAt ι q c S -
      evalAt ι (MvPolynomial.pderiv 1 q) c S * d := by
  let values : Fin 2 → Polynomial L := ![Polynomial.X + Polynomial.C c, S]
  let increments : Fin 2 → Polynomial L := ![0, d]
  have h := MvPolynomial.eval₂Hom_add_sub_firstOrderIncrement_univ_mem_sq
    (Polynomial.C.comp ι) values increments (Ideal.span {Polynomial.X ^ m}) q (by
      intro i
      fin_cases i
      · exact Ideal.zero_mem _
      · exact Ideal.mem_span_singleton.mpr hd)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  have hv : values + increments = ![Polynomial.X + Polynomial.C c, S + d] := by
    funext i
    fin_cases i <;> simp [values, increments]
  simpa [hv, evalAt, MvPolynomial.firstOrderIncrement, Fin.sum_univ_two,
    values, increments, ← pow_mul, Nat.mul_comm] using h

/-- An inverse correct to precision `m` cancels the next `m` branch coefficients. -/
theorem newton_matches_double (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (c : L) (P S G : Polynomial L) (m : ℕ)
    (hmatch : Polynomial.X ^ m ∣ P - S)
    (hsolution : evalAt ι q c P = 0)
    (hinverse : Polynomial.X ^ m ∣ evalAt ι (MvPolynomial.pderiv 1 q) c S * G - 1) :
    Polynomial.X ^ (2 * m) ∣ P - (S - evalAt ι q c S * G) := by
  -- Q(P)=0 turns the Taylor remainder into Q(S) + Q_Y(S)(P-S).
  have ht := residual_quadratic ι q c S (P - S) m hmatch
  have hadd : S + (P - S) = P := by ring
  rw [hadd, hsolution, zero_sub] at ht
  have ht' : Polynomial.X ^ (2 * m) ∣
      evalAt ι q c S + evalAt ι (MvPolynomial.pderiv 1 q) c S * (P - S) := by
    convert dvd_neg.mpr ht using 1
    ring
  -- Both factors have order at least m, so the inverse error contributes only at order 2m.
  have hp : Polynomial.X ^ (2 * m) ∣
      (evalAt ι (MvPolynomial.pderiv 1 q) c S * G - 1) * (P - S) := by
    simpa [pow_add, two_mul] using mul_dvd_mul hinverse hmatch
  convert (dvd_mul_of_dvd_left ht' G).sub hp using 1
  ring

/-- Newton inversion squares the multiplicative error, in every characteristic. -/
theorem inverse_newton_double (D G : Polynomial L) (m : ℕ)
    (h : Polynomial.X ^ m ∣ D * G - 1) :
    Polynomial.X ^ (2 * m) ∣ D * (G * (2 - D * G)) - 1 := by
  have hh : Polynomial.X ^ (2 * m) ∣ (D * G - 1) * (D * G - 1) := by
    simpa [pow_add, two_mul] using mul_dvd_mul h h
  convert dvd_neg.mpr hh using 1
  ring

/-- Changing the branch modulo `T^m` preserves the derivative inverse to precision `m`. -/
theorem inverse_at_changed_series (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (c : L) (S Snew G : Polynomial L) (m : ℕ)
    (hchange : Polynomial.X ^ m ∣ Snew - S)
    (hinverse : Polynomial.X ^ m ∣ evalAt ι (MvPolynomial.pderiv 1 q) c S * G - 1) :
    Polynomial.X ^ m ∣ evalAt ι (MvPolynomial.pderiv 1 q) c Snew * G - 1 := by
  have hd := residual_congr ι (MvPolynomial.pderiv 1 q) c Snew S m hchange
  change Polynomial.X ^ m ∣
    evalAt ι (MvPolynomial.pderiv 1 q) c Snew - evalAt ι (MvPolynomial.pderiv 1 q) c S at hd
  convert (dvd_mul_of_dvd_left hd G).add hinverse using 1
  ring

end

/-- At a modulus root, coefficient reduction disappears and only precision truncation remains. -/
theorem coeff_specialize_reduceSeries (ι : E →+* L) (θ : L)
    (h : CPolynomial E) (m : ℕ) (S : Series E)
    (hmonic : h.monic) (hroot : h.toPoly.eval₂ ι θ = 0) (i : ℕ) :
    (specialize ι θ (reduceSeries h m S)).coeff i =
      if i < m then (specialize ι θ S).coeff i else 0 := by
  rw [coeff_specialize, coeff_reduceSeries]
  split_ifs with hi
  · rw [modByMonic_toPoly_eq_modByMonic _ _ hmonic,
      Polynomial.eval₂_modByMonic_eq_self_of_root hroot, coeff_specialize]
  · rw [toPoly_zero, Polynomial.eval₂_zero]

/-- Normalization preserves the first `m` specialized coefficients. -/
theorem specialize_reduceSeries_matches (ι : E →+* L) (θ : L)
    (h : CPolynomial E) (m : ℕ) (S : Series E)
    (hmonic : h.monic) (hroot : h.toPoly.eval₂ ι θ = 0) :
    Polynomial.X ^ m ∣ specialize ι θ (reduceSeries h m S) - specialize ι θ S := by
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  simp [Polynomial.coeff_sub, coeff_specialize_reduceSeries ι θ h m S hmonic hroot, hi]

/-- The normalized specialized series has no coefficient at or above the requested precision. -/
theorem specialize_reduceSeries_degree (ι : E →+* L) (θ : L)
    (h : CPolynomial E) (m : ℕ) (S : Series E)
    (hmonic : h.monic) (hroot : h.toPoly.eval₂ ι θ = 0) :
    (specialize ι θ (reduceSeries h m S)).degree < m := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_specialize_reduceSeries ι θ h m S hmonic hroot, if_neg (by omega)]
/-- Both loop invariants double: agreement with the true branch and inversion of its derivative. -/
theorem newtonStep_correct (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (h : CPolynomial E)
    (hmonic : h.monic) (hroot : h.toPoly.eval₂ ι θ = 0)
    (P : Polynomial L) (m : ℕ) (state : NewtonState (E := E))
    (hsolution : evalAt ι (CPoly.fromCMvPolynomial Q) (ι center) P = 0)
    (hmatch : Polynomial.X ^ m ∣ P - specialize ι θ state.series)
    (hinverse : Polynomial.X ^ m ∣
      evalAt ι (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) (ι center)
        (specialize ι θ state.series) * specialize ι θ state.inverse - 1) :
    Polynomial.X ^ (2 * m) ∣ P - specialize ι θ (newtonStep Q center h m state).series ∧
    Polynomial.X ^ (2 * m) ∣
      evalAt ι (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) (ι center)
        (specialize ι θ (newtonStep Q center h m state).series) *
          specialize ι θ (newtonStep Q center h m state).inverse - 1 := by
  let q := CPoly.fromCMvPolynomial Q
  let raw := state.series - residual Q center state.series * state.inverse
  let updated := reduceSeries h (2 * m) raw
  let D := evalAt ι (MvPolynomial.pderiv 1 q) (ι center) (specialize ι θ updated)
  have hraw : Polynomial.X ^ (2 * m) ∣ P - specialize ι θ raw := by
    simpa [raw, specialize_residual, evalAt] using
      newton_matches_double ι q (ι center) P (specialize ι θ state.series)
        (specialize ι θ state.inverse) m hmatch hsolution hinverse
  have hred := specialize_reduceSeries_matches ι θ h (2 * m) raw hmonic hroot
  have hnew : Polynomial.X ^ (2 * m) ∣ P - specialize ι θ updated := by
    convert hraw.sub hred using 1
    ring
  -- The new branch still agrees with the old one modulo T^m; reuse its inverse as a seed.
  have hchange : Polynomial.X ^ m ∣ specialize ι θ updated - specialize ι θ state.series := by
    have hsmall := (pow_dvd_pow (Polynomial.X : Polynomial L) (by omega : m ≤ 2 * m)).trans hnew
    convert hmatch.sub hsmall using 1
    ring
  have hi := inverse_at_changed_series ι q (ι center) (specialize ι θ state.series)
    (specialize ι θ updated) (specialize ι θ state.inverse) m hchange hinverse
  have hidouble := inverse_newton_double D (specialize ι θ state.inverse) m hi
  let rawInv := state.inverse *
    (2 - residual (CPoly.CMvPolynomial.partialDerivative 1 Q) center updated * state.inverse)
  have hrawInv : Polynomial.X ^ (2 * m) ∣ D * specialize ι θ rawInv - 1 := by
    simpa [rawInv, map_ofNat, specialize_residual,
      CPoly.CMvPolynomial.fromCMvPolynomial_partialDerivative,
      D, q, evalAt] using hidouble
  have hredInv := specialize_reduceSeries_matches ι θ h (2 * m) rawInv hmonic hroot
  constructor
  · exact hnew
  · change Polynomial.X ^ (2 * m) ∣ D * specialize ι θ (reduceSeries h (2 * m) rawInv) - 1
    convert hrawInv.add (dvd_mul_of_dvd_right hredInv D) using 1
    ring

/-- Trimming to a smaller requested precision preserves every required branch coefficient. -/
theorem reduceSeries_matches_solution (ι : E →+* L) (θ : L)
    (h : CPolynomial E) (hmonic : h.monic) (hroot : h.toPoly.eval₂ ι θ = 0)
    (P : Polynomial L) (S : Series E) (k m : ℕ) (hkm : k ≤ m)
    (hmatch : Polynomial.X ^ m ∣ P - specialize ι θ S) :
    Polynomial.X ^ k ∣ P - specialize ι θ (reduceSeries h k S) := by
  have hsmall := (pow_dvd_pow (Polynomial.X : Polynomial L) hkm).trans hmatch
  have hred := specialize_reduceSeries_matches ι θ h k S hmonic hroot
  convert hsmall.sub hred using 1
  ring

/-- The guarded loop reaches the requested precision before its termination fuel expires. -/
theorem newtonLoop_correct (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (h : CPolynomial E)
    (hmonic : h.monic) (hroot : h.toPoly.eval₂ ι θ = 0)
    (P : Polynomial L) (k fuel m : ℕ) (hm : 0 < m) (hbudget : k ≤ m + fuel)
    (state : NewtonState (E := E))
    (hsolution : evalAt ι (CPoly.fromCMvPolynomial Q) (ι center) P = 0)
    (hmatch : Polynomial.X ^ m ∣ P - specialize ι θ state.series)
    (hinverse : Polynomial.X ^ m ∣
      evalAt ι (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) (ι center)
        (specialize ι θ state.series) * specialize ι θ state.inverse - 1) :
    Polynomial.X ^ k ∣ P - specialize ι θ (newtonLoop Q center h k fuel m state) ∧
      (specialize ι θ (newtonLoop Q center h k fuel m state)).degree < k := by
  induction fuel generalizing m state with
  | zero =>
      exact ⟨reduceSeries_matches_solution ι θ h hmonic hroot P state.series k m
          (by omega) hmatch,
        specialize_reduceSeries_degree ι θ h k state.series hmonic hroot⟩
  | succ fuel ih =>
      rw [newtonLoop]
      split_ifs with hstop
      · exact ⟨reduceSeries_matches_solution ι θ h hmonic hroot P state.series k m
            hstop hmatch,
          specialize_reduceSeries_degree ι θ h k state.series hmonic hroot⟩
      · have hnext := newtonStep_correct ι θ Q center h hmonic hroot P m state
          hsolution hmatch hinverse
        exact ih (2 * m) (by omega) (by omega) (newtonStep Q center h m state)
          hnext.1 hnext.2

omit [BEq E] [LawfulBEq E] in
/-- The constant coefficient of a centered substitution is evaluation at its initial value. -/
theorem evalAt_coeff_zero (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (c : L) (S : Polynomial L) :
    (evalAt ι q c S).coeff 0 = MvPolynomial.eval₂ ι ![c, S.coeff 0] q := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change Polynomial.evalRingHom 0
    (MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X + Polynomial.C c, S] q) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp
  · funext i
    fin_cases i <;> simp [Polynomial.coeff_zero_eq_eval_zero]

/-- **Simultaneous Newton recovery.** At every geometric root of the modulus, the computed
series equals any degree-`< k` polynomial solution with that initial value. -/
theorem newtonLift_specializes (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) (h : CPolynomial E)
    (hmonic : h.monic) (hroot : h.toPoly.eval₂ ι θ = 0)
    (k : ℕ) (out : Series E) (hrun : newtonLift? Q center h k = some out)
    (P : Polynomial L) (hdegree : P.degree < k) (hconstant : P.coeff 0 = θ)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι)
      ![Polynomial.X + Polynomial.C (ι center), P] (CPoly.fromCMvPolynomial Q) = 0) :
    specialize ι θ out = P := by
  unfold newtonLift? at hrun
  cases hinverse : inverseMod? (slope Q center) h with
  | none => simp [hinverse] at hrun
  | some inverse =>
      rw [hinverse] at hrun
      change some (newtonLoop Q center h k k 1
        ⟨CPolynomial.C CPolynomial.X, CPolynomial.C inverse⟩) = some out at hrun
      have hout := Option.some.inj hrun
      subst out
      let state : NewtonState (E := E) :=
        ⟨CPolynomial.C CPolynomial.X, CPolynomial.C inverse⟩
      have hstart : Polynomial.X ^ 1 ∣ P - specialize ι θ state.series := by
        rw [pow_one, Polynomial.X_dvd_iff]
        simp [state, Polynomial.coeff_sub, hconstant, X_toPoly]
      have hstartInv : Polynomial.X ^ 1 ∣
          evalAt ι (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) (ι center)
            (specialize ι θ state.series) * specialize ι θ state.inverse - 1 := by
        have hi := eval₂_mul_inverseMod_eq_one ι θ hroot hinverse
        rw [pow_one, Polynomial.X_dvd_iff]
        simp only [Polynomial.coeff_sub, Polynomial.mul_coeff_zero, evalAt_coeff_zero]
        simpa [state, eval₂_slope, X_toPoly] using sub_eq_zero.mpr hi
      -- Both initial invariants hold modulo T: S(0)=theta and Q_Y(center,theta)G(0)=1.
      have hresult := newtonLoop_correct ι θ Q center h hmonic hroot P k k 1
        (by decide) (by omega) state hsolution hstart hstartInv
      ext j
      by_cases hj : j < k
      · have hc := Polynomial.X_pow_dvd_iff.mp hresult.1 j hj
        exact (sub_eq_zero.mp (by simpa only [Polynomial.coeff_sub] using hc)).symm
      · rw [Polynomial.coeff_eq_zero_of_degree_lt
            (hresult.2.trans_le (by exact_mod_cast Nat.le_of_not_gt hj)),
          Polynomial.coeff_eq_zero_of_degree_lt
            (hdegree.trans_le (by exact_mod_cast Nat.le_of_not_gt hj))]

end
end ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
