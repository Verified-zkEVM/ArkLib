/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Univariate.Basic
-- The coefficient-array proofs below intentionally reduce these implementation definitions.
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Lowest-degree coefficient of a toric generalized characteristic polynomial

Rojas's toric perturbation `Pert_A` is the coefficient of the lowest-degree
power of the perturbation variable `s` in the toric generalized
characteristic polynomial `H(u; s)`. This file supplies exactly that
extraction step once an upstream sparse resultant producer has computed `H`.
It does not construct the toric resultant matrix or prove its root coverage.
-/

@[expose] public section

namespace ArkLib.Rojas

open CompPoly CompPoly.CPolynomial

variable {R : Type*} [Zero R] [BEq R] [LawfulBEq R]

/-- The first nonzero stored coefficient, scanning from degree zero upward. -/
def lowestNonzeroCoefficient? (f : CPolynomial R) : Option R :=
  f.val.toList.find? fun coefficient ↦ coefficient != 0

omit [BEq R] [LawfulBEq R] in
private theorem coeff_eq_getElem (f : CPolynomial R) {i : ℕ} (hi : i < f.val.size) :
    f.coeff i = f.val[i] := by
  rw [CPolynomial.coeff, CPolynomial.Raw.coeff, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hi]
  simp

theorem lowestNonzeroCoefficient?_eq_some_iff {f : CPolynomial R} {coefficient : R} :
    lowestNonzeroCoefficient? f = some coefficient ↔
      coefficient ≠ 0 ∧
        ∃ i, i < f.val.size ∧ f.coeff i = coefficient ∧
          ∀ j < i, f.coeff j = 0 := by
  rw [lowestNonzeroCoefficient?, List.find?_eq_some_iff_getElem]
  constructor
  · rintro ⟨hcoefficient, i, hi, hget, hlower⟩
    refine ⟨by simpa only [bne_iff_ne] using hcoefficient, i, ?_, ?_, ?_⟩
    · simpa using hi
    · rw [coeff_eq_getElem f (by simpa using hi)]
      simpa only [Array.getElem_toList hi] using hget
    · intro j hj
      have hjSize : j < f.val.size := hj.trans (by simpa using hi)
      have hjList : j < f.val.toList.length := by simpa using hjSize
      have hzero := hlower j hj
      rw [Bool.not_eq_true'] at hzero
      have hvalue : f.val.toList[j] = 0 :=
        bne_eq_false_iff_eq.mp hzero
      rw [coeff_eq_getElem f hjSize]
      simpa only [Array.getElem_toList hjList] using hvalue
  · rintro ⟨hcoefficient, i, hi, hcoeff, hlower⟩
    have hiList : i < f.val.toList.length := by simpa using hi
    refine ⟨by simpa only [bne_iff_ne] using hcoefficient, i, hiList, ?_, ?_⟩
    · rw [Array.getElem_toList hiList, ← coeff_eq_getElem f hi]
      exact hcoeff
    · intro j hj
      have hjSize : j < f.val.size := by simpa using hj.trans hiList
      have hjList : j < f.val.toList.length := by simpa using hjSize
      have hzero := hlower j hj
      rw [Bool.not_eq_true']
      apply bne_eq_false_iff_eq.mpr
      rw [Array.getElem_toList hjList, ← coeff_eq_getElem f hjSize]
      exact hzero

theorem lowestNonzeroCoefficient?_eq_none_iff (f : CPolynomial R) :
    lowestNonzeroCoefficient? f = none ↔ f = 0 := by
  constructor
  · intro hnone
    rw [CPolynomial.eq_iff_coeff]
    intro i
    rw [lowestNonzeroCoefficient?, List.find?_eq_none] at hnone
    by_cases hi : i < f.val.size
    · have hiList : i < f.val.toList.length := by simpa using hi
      have hmem : f.val.toList[i] ∈ f.val.toList := List.getElem_mem hiList
      have hzero := hnone f.val.toList[i] hmem
      rw [bne_iff_ne] at hzero
      rw [CPolynomial.coeff_zero, coeff_eq_getElem f hi]
      simpa only [Array.getElem_toList hiList] using not_ne_iff.mp hzero
    · have hfi : f.coeff i = 0 := by
        rw [CPolynomial.coeff, CPolynomial.Raw.coeff,
          Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hi)]
        simp
      rw [hfi, CPolynomial.coeff_zero]
  · rintro rfl
    rfl

variable {F : Type*} [Zero F] [BEq F] [LawfulBEq F]

/-- Extract `Pert_A(u)` from an already-computed nested `H(u; s)`. -/
def toricPerturbationCoefficient?
    (H : CPolynomial (CPolynomial F)) : Option (CPolynomial F) :=
  lowestNonzeroCoefficient? H

theorem toricPerturbationCoefficient?_eq_some_iff
    {H : CPolynomial (CPolynomial F)} {perturbation : CPolynomial F} :
    toricPerturbationCoefficient? H = some perturbation ↔
      perturbation ≠ 0 ∧
        ∃ i, i < H.val.size ∧ H.coeff i = perturbation ∧
          ∀ j < i, H.coeff j = 0 :=
  lowestNonzeroCoefficient?_eq_some_iff

theorem toricPerturbationCoefficient?_eq_none_iff
    (H : CPolynomial (CPolynomial F)) :
    toricPerturbationCoefficient? H = none ↔ H = 0 :=
  lowestNonzeroCoefficient?_eq_none_iff H

end ArkLib.Rojas
