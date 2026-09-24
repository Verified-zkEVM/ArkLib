/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra
public import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients

/-!
# Degree bounds for rational Taylor numerators with a polynomial parameter

Let `Q` be a differential polynomial with coefficients in `F[X]`, where the variable `X` is a
parameter. The rational Taylor numerators of `Q`, computed over the `F`-algebra `F[X]` by
`rationalTaylorNumeratorOver`, are polynomials in the initial jet with coefficients in `F[X]`.
This file bounds their `MvPolynomial.jointTotalDegree`, the total degree in the jet coordinates
and the parameter together. It also bounds coefficient degree in the parameter and total degree
in the jet variables separately.

Taylor substitution at a constant center `C c` does not raise the degree in the parameter: if
every coefficient of `Q` has degree at most `h` in `X`, so does every coefficient of the initial
separant and of the universal residual (`MvPolynomial.CoeffNatDegreeLE`). If moreover `Q` has
total jet degree at most `v`, the numerator of `c_l` has joint degree at most
`(2(l - r) - 1) * (v - 1 + h) + 1`, linear in the order `l`. Padding to an exponent
`τ ≥ 2(l - r) - 1` gives the bound `1 + τ * (v - 1 + h)`, which does not depend on `l`.

## Main statements

* `coeffNatDegreeLE_initialJetSeparant`, `coeffNatDegreeLE_universalTaylorJet`,
  `coeffNatDegreeLE_universalTaylorResidual`, and
  `coeffNatDegreeLE_universalTaylorResidual_coeff`: at a constant center, the parameter degree
  of `Q` bounds that of the separant and of the residual.
* `jointTotalDegree_initialJetSeparant_le`: the separant has joint degree at most `v - 1 + h`.
* `jointTotalDegree_rationalTaylorNumeratorOver_le`: the recursion bound, from a bound `b` on
  the separant and `b + 1` on the residual coefficients.
* `jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE`: the bound
  `(2(l - r) - 1) * (v - 1 + h) + 1` at a constant center.
* `jointTotalDegree_commonTaylorNumeratorOver_le` and
  `jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE`: the common-exponent
  bounds `1 + τ * b` and `1 + τ * (v - 1 + h)`.
* `coeffNatDegreeLE_rationalTaylorNumeratorOver` and
  `coeffNatDegreeLE_commonTaylorNumeratorOver_le`: coefficient-degree bounds for the same
  numerators.
* `totalDegree_rationalTaylorNumeratorOver_le_of_jet` and
  `totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent`: bounds on degree in the jet
  variables alone.

## References

* [DKT26]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-! ### Parameter degree under Taylor substitution -/

section CommSemiring

variable {R : Type*} [CommSemiring R] {r h : ℕ}

/-- At a constant center, the initial separant has coefficient degree at most `h` in the
parameter when `Q` does. -/
theorem coeffNatDegreeLE_initialJetSeparant (Q : DifferentialPolynomial (Polynomial R) r)
    (c : R) (hQ : CoeffNatDegreeLE Q h) :
    CoeffNatDegreeLE (initialJetSeparant (Polynomial.C c) Q) h := by
  apply (hQ.pderiv (some (Fin.last r))).aeval
  intro i
  cases i with
  | none => exact coeffNatDegreeLE_C (by simp)
  | some i => exact coeffNatDegreeLE_X i

/-- The universal Taylor jet has constant coefficients. -/
theorem coeffNatDegreeLE_universalTaylorJet (K j : ℕ) :
    CoeffNatDegreeLE (universalTaylorJet (F := Polynomial R) K j) 0 := by
  rw [← map_universalTaylorJet (Polynomial.C : R →+* Polynomial R)]
  exact coeffNatDegreeLE_map_C _

/-- At a constant center, the universal residual has coefficient degree at most `h` in the
parameter when `Q` does. -/
theorem coeffNatDegreeLE_universalTaylorResidual (Q : DifferentialPolynomial (Polynomial R) r)
    (c : R) (hQ : CoeffNatDegreeLE Q h) (K : ℕ) :
    CoeffNatDegreeLE (universalTaylorResidual K (Polynomial.C c) Q) h := by
  apply hQ.aeval
  intro i
  cases i with
  | none => exact (coeffNatDegreeLE_C (by simp)).add (coeffNatDegreeLE_X none)
  | some j => exact coeffNatDegreeLE_universalTaylorJet K j.val

/-- At a constant center, every displacement coefficient of the universal residual has
coefficient degree at most `h` in the parameter when `Q` does. -/
theorem coeffNatDegreeLE_universalTaylorResidual_coeff
    (Q : DifferentialPolynomial (Polynomial R) r) (c : R) (hQ : CoeffNatDegreeLE Q h)
    (K t : ℕ) :
    CoeffNatDegreeLE ((optionEquivLeft (Polynomial R) (Fin K)
      (universalTaylorResidual K (Polynomial.C c) Q)).coeff t) h := by
  intro m
  rw [optionEquivLeft_coeff_coeff]
  exact coeffNatDegreeLE_universalTaylorResidual Q c hQ K _

/-- If `Q` has total jet degree at most `v` and the initial separant has coefficient degree at
most `h`, the initial separant has joint total degree at most `v - 1 + h`. -/
theorem jointTotalDegree_initialJetSeparant_le (center : Polynomial R)
    (Q : DifferentialPolynomial (Polynomial R) r) (v : ℕ) (hv : jetTotalDegree Q ≤ v)
    (hh : CoeffNatDegreeLE (initialJetSeparant center Q) h) :
    jointTotalDegree (initialJetSeparant center Q) ≤ v - 1 + h := by
  have hd := hh.jointTotalDegree_le
  have hs := (totalDegree_initialJetSeparant_le center Q).trans (Nat.sub_le_sub_right hv 1)
  omega

end CommSemiring

/-! ### Joint degree of the numerators -/

variable {F : Type*} [Field F] {r : ℕ}

/-- If the initial separant has joint total degree at most `b`, and for every `l > r` each
monomial `m` of the coefficient of `ξ ^ (l - r)` in the universal residual satisfies
`jointTotalDegree (C (coeff m)) + degree m ≤ b + 1`, then the numerator of `c_l` has joint total
degree at most `(2(l - r) - 1) * b + 1`. -/
theorem jointTotalDegree_rationalTaylorNumeratorOver_le
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r) (b : ℕ)
    (hS : jointTotalDegree (initialJetSeparant center Q) ≤ b)
    (hres : ∀ l, r < l → ∀ m ∈
      ((optionEquivLeft (Polynomial F) (Fin l)
        (universalTaylorResidual l center Q)).coeff (l - r)).support,
      jointTotalDegree (C (((optionEquivLeft (Polynomial F) (Fin l)
        (universalTaylorResidual l center Q)).coeff (l - r)).coeff m) :
          MvPolynomial (Fin (r + 1)) (Polynomial F)) + m.degree ≤ b + 1)
    (l : ℕ) :
    jointTotalDegree (rationalTaylorNumeratorOver F center Q l) ≤
      (2 * (l - r) - 1) * b + 1 := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · simp only [jointTotalDegree_X]
      omega
    · have hden : ∀ m ∈ ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r)).support,
          Finsupp.weight (fun i : Fin l ↦ 2 * (i.val - r) - 1) m ≤ 2 * (l - r) - 2 :=
        fun m hm ↦ denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (by omega : l ≤ r + (l - r)) center Q m hm
      have hd := jointTotalDegree_clearedSubstitution_le
        (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) b (b + 1)
        ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r)) hS
        (fun i ↦ ih i.val i.isLt) hden (hres l (by omega))
      have hm := jointTotalDegree_mul_le
        (-C (algebraMap F (Polynomial F) ((l.choose r : F)⁻¹)) :
          MvPolynomial (Fin (r + 1)) (Polynomial F))
        (clearedSubstitution C (initialJetSeparant center Q)
          (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
          (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
          ((optionEquivLeft (Polynomial F) (Fin l)
            (universalTaylorResidual l center Q)).coeff (l - r)))
      simp only [jointTotalDegree_neg, Polynomial.algebraMap_eq, jointTotalDegree_C_C,
        zero_add] at hm
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      rw [he]
      simp only [Polynomial.algebraMap_eq]
      nlinarith [hm.trans hd]

/-- Let `Q` have total jet degree at most `v`, and let the initial separant and every
displacement coefficient of every universal residual have coefficient degree at most `h` in the
parameter. Then the numerator of `c_l` has joint total degree at most
`(2(l - r) - 1) * (v - 1 + h) + 1`. -/
theorem jointTotalDegree_rationalTaylorNumeratorOver_le_of_natDegree_coeff_le
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : jetTotalDegree Q ≤ v)
    (hsep : CoeffNatDegreeLE (initialJetSeparant center Q) h)
    (hres : ∀ l t, CoeffNatDegreeLE ((optionEquivLeft (Polynomial F) (Fin l)
      (universalTaylorResidual l center Q)).coeff t) h)
    (l : ℕ) :
    jointTotalDegree (rationalTaylorNumeratorOver F center Q l) ≤
      (2 * (l - r) - 1) * (v - 1 + h) + 1 := by
  apply jointTotalDegree_rationalTaylorNumeratorOver_le center Q (v - 1 + h)
    (jointTotalDegree_initialJetSeparant_le center Q v hv hsep) _ l
  intro j _ m hm
  have hc := (jointTotalDegree_C_le (σ := Fin (r + 1))
    (((optionEquivLeft (Polynomial F) (Fin j)
      (universalTaylorResidual j center Q)).coeff (j - r)).coeff m)).trans (hres j (j - r) m)
  have hd := (le_totalDegree hm).trans
    ((totalDegree_universalTaylorResidual_coeff_le j center Q (j - r)).trans hv)
  change _ + (m.sum fun _ e ↦ e) ≤ _
  omega

/-- At a constant center, if `Q` has total jet degree at most `v` and coefficient degree at most
`h` in the parameter, the numerator of `c_l` has joint total degree at most
`(2(l - r) - 1) * (v - 1 + h) + 1`. -/
theorem jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE
    (center : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h : ℕ)
    (hv : jetTotalDegree Q ≤ v) (hQ : CoeffNatDegreeLE Q h) (l : ℕ) :
    jointTotalDegree (rationalTaylorNumeratorOver F (Polynomial.C center) Q l) ≤
      (2 * (l - r) - 1) * (v - 1 + h) + 1 :=
  jointTotalDegree_rationalTaylorNumeratorOver_le_of_natDegree_coeff_le
    (Polynomial.C center) Q v h hv (coeffNatDegreeLE_initialJetSeparant Q center hQ)
    (fun l t ↦ coeffNatDegreeLE_universalTaylorResidual_coeff Q center hQ l t) l

/-- If `2(l - r) - 1 ≤ τ`, the initial separant has joint total degree at most `b`, and the
numerator of `c_l` has joint total degree at most `(2(l - r) - 1) * b + 1`, then the common
numerator of `c_l` with exponent `τ` has joint total degree at most `1 + τ * b`. -/
theorem jointTotalDegree_commonTaylorNumeratorOver_le
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r) (b τ l : ℕ)
    (hl : 2 * (l - r) - 1 ≤ τ)
    (hS : jointTotalDegree (initialJetSeparant center Q) ≤ b)
    (hN : jointTotalDegree (rationalTaylorNumeratorOver F center Q l) ≤
      (2 * (l - r) - 1) * b + 1) :
    jointTotalDegree (commonTaylorNumeratorOver F center Q τ l) ≤ 1 + τ * b := by
  have hp := (jointTotalDegree_pow_le (initialJetSeparant center Q)
    (τ - (2 * (l - r) - 1))).trans (Nat.mul_le_mul_left _ hS)
  have hm := jointTotalDegree_mul_le
    (rationalTaylorNumeratorOver F center Q l)
    (initialJetSeparant center Q ^ (τ - (2 * (l - r) - 1)))
  have he := Nat.sub_add_cancel hl
  unfold commonTaylorNumeratorOver
  nlinarith

/-- At a constant center, if `Q` has total jet degree at most `v` and coefficient degree at most
`h` in the parameter, and `2(l - r) - 1 ≤ τ`, the common numerator of `c_l` with exponent `τ` has
joint total degree at most `1 + τ * (v - 1 + h)`. -/
theorem jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE
    (center : F) (Q : DifferentialPolynomial (Polynomial F) r) (v h τ l : ℕ)
    (hl : 2 * (l - r) - 1 ≤ τ)
    (hv : jetTotalDegree Q ≤ v) (hQ : CoeffNatDegreeLE Q h) :
    jointTotalDegree (commonTaylorNumeratorOver F (Polynomial.C center) Q τ l) ≤
      1 + τ * (v - 1 + h) :=
  jointTotalDegree_commonTaylorNumeratorOver_le (Polynomial.C center) Q (v - 1 + h) τ l hl
    (jointTotalDegree_initialJetSeparant_le _ Q v hv
      (coeffNatDegreeLE_initialJetSeparant Q center hQ))
    (jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE center Q v h hv hQ l)

/-! ### Separate coefficient and jet degree bounds -/

section SeparateDegrees

variable {F : Type*} [Field F] {r : ℕ}

/-- The coefficient degree of the rational Taylor numerator is at most
`(2(l - r) - 1) * h` when each coefficient of `Q` has degree at most `h` in the parameter. -/
theorem coeffNatDegreeLE_rationalTaylorNumeratorOver (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h : ℕ)
    (hQ : CoeffNatDegreeLE Q h) (l : ℕ) :
    CoeffNatDegreeLE (rationalTaylorNumeratorOver F (Polynomial.C center) Q l)
      ((2 * (l - r) - 1) * h) := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · exact (coeffNatDegreeLE_X _).mono (Nat.zero_le _)
    · have hh : 0 < l - r := by omega
      have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := r) (h := l - r) (by omega : l ≤ r + (l - r))
        (Polynomial.C center) Q
      have hd := CoeffNatDegreeLE.clearedSubstitution
        (initialJetSeparant (Polynomial.C center) Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver F (Polynomial.C center) Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) h h
        ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l (Polynomial.C center) Q)).coeff (l - r))
        (coeffNatDegreeLE_initialJetSeparant Q center hQ)
        (fun i ↦ ih i.val i.isLt) hden
        (fun m _ ↦ coeffNatDegreeLE_universalTaylorResidual_coeff Q center hQ
          l (l - r) m)
      have hc : CoeffNatDegreeLE
          (-MvPolynomial.C (algebraMap F (Polynomial F) ((l.choose r : F)⁻¹)) :
            MvPolynomial (Fin (r + 1)) (Polynomial F)) 0 := by
        intro m
        rw [coeff_neg, coeff_C]
        split_ifs <;> simp
      have hm := hc.mul hd
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      rw [he]
      simpa only [Polynomial.algebraMap_eq, zero_add, add_mul, one_mul] using hm

/-- The numerator padded to exponent `τ` has coefficient degree at most `τ * h` whenever the
exponent covers its denominator. -/
theorem coeffNatDegreeLE_commonTaylorNumeratorOver_le (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h τ l : ℕ)
    (hτ : 2 * (l - r) - 1 ≤ τ) (hQ : CoeffNatDegreeLE Q h) :
    CoeffNatDegreeLE (commonTaylorNumeratorOver F (Polynomial.C center) Q τ l) (τ * h) := by
  unfold commonTaylorNumeratorOver
  have hn := coeffNatDegreeLE_rationalTaylorNumeratorOver center Q h hQ l
  have hs := (coeffNatDegreeLE_initialJetSeparant Q center hQ).pow
    (τ - (2 * (l - r) - 1))
  have hm := hn.mul hs
  apply hm.mono
  rw [← Nat.add_mul, Nat.add_sub_of_le hτ]

/-- The rational Taylor numerator has total degree at most
`(2(l - r) - 1) * (v - 1) + 1` in the jet variables. -/
theorem totalDegree_rationalTaylorNumeratorOver_le_of_jet (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v : ℕ)
    (hv : 0 < v) (hjet : jetTotalDegree Q ≤ v) (l : ℕ) :
    (rationalTaylorNumeratorOver F center Q l).totalDegree ≤
      (2 * (l - r) - 1) * (v - 1) + 1 := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · simp only [totalDegree_X]
      omega
    · have hh : 0 < l - r := by omega
      have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := r) (h := l - r) (by omega : l ≤ r + (l - r)) center Q
      have hd := totalDegree_clearedSubstitution
        (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) (v - 1) v
        ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r))
        ((totalDegree_initialJetSeparant_le center Q).trans
          (Nat.sub_le_sub_right hjet 1))
        (fun i ↦ ih i.val i.isLt) hden
        ((totalDegree_universalTaylorResidual_coeff_le l center Q (l - r)).trans hjet)
      have hm := totalDegree_mul
        (-MvPolynomial.C (algebraMap F (Polynomial F) ((l.choose r : F)⁻¹)) :
          MvPolynomial (Fin (r + 1)) (Polynomial F))
        (clearedSubstitution C (initialJetSeparant center Q)
          (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
          (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
          ((optionEquivLeft (Polynomial F) (Fin l)
            (universalTaylorResidual l center Q)).coeff (l - r)))
      simp only [totalDegree_neg, totalDegree_C, zero_add] at hm
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      rw [he]
      have hbound := hm.trans hd
      have hvsub := Nat.sub_add_cancel (Nat.succ_le_of_lt hv)
      nlinarith [hbound, hvsub]

/-- For a sufficient exponent, the common Taylor numerator has total degree at most
`1 + τ * (v - 1)` in the jet variables. -/
theorem totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r)
    (v K τ : ℕ) (hv : 0 < v) (hτ : TaylorExponentSufficient r K τ)
    (hjet : jetTotalDegree Q ≤ v) (l : Fin K) :
    (commonTaylorNumeratorOver F center Q τ l.val).totalDegree ≤ 1 + τ * (v - 1) := by
  have hd := totalDegree_rationalTaylorNumeratorOver_le_of_jet center Q v hv hjet l.val
  have hs := (totalDegree_initialJetSeparant_le center Q).trans
    (Nat.sub_le_sub_right hjet 1)
  have hp := (totalDegree_pow (initialJetSeparant center Q)
    (τ - (2 * (l.val - r) - 1))).trans (Nat.mul_le_mul_left _ hs)
  have hm := totalDegree_mul (rationalTaylorNumeratorOver F center Q l.val)
    (initialJetSeparant center Q ^ (τ - (2 * (l.val - r) - 1)))
  have he := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumeratorOver
  nlinarith

end SeparateDegrees

end

end PolynomialDifferential
