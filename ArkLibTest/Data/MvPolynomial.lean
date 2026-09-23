/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.FrobeniusContraction
import ArkLib.Data.MvPolynomial.JointDegree
import ArkLib.Data.MvPolynomial.MapExponents
import ArkLib.Data.MvPolynomial.WeightAtMost
import ArkLib.Data.MvPolynomial.WeightedHomogeneous
import ArkLib.Data.MvPolynomial.WeightedOrder
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance tests for weighted multivariate polynomials
-/

open MvPolynomial
open scoped Polynomial

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example : (MvPolynomial.C (Polynomial.X ^ 2 : ℚ[X]) *
    MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ[X]) ∈
    MvPolynomial.restrictJointDegree (R := ℚ) (fun _ ↦ 1) (2 + 1) :=
  MvPolynomial.mul_mem_restrictJointDegree
    (MvPolynomial.C_mem_restrictJointDegree _ (by simp))
    (MvPolynomial.X_mem_restrictJointDegree _ 0 le_rfl)

example : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ[X]) ∉
    MvPolynomial.restrictJointDegree (R := ℚ) (fun _ ↦ 1) 0 := by
  intro h
  have := MvPolynomial.coeff_eq_zero_of_mem_restrictJointDegree h
    (e := Finsupp.single 0 1) (by simp [Finsupp.weight_single])
  simp at this

private noncomputable abbrev frobeniusContractionInput :
    MvPolynomial (Option (Fin 1)) (ZMod 2) :=
  X none ^ 2 + X (some 0)

private theorem irreducible_frobeniusContractionInput : Irreducible frobeniusContractionInput := by
  let τ : Option (Fin 1) ≃ Option (Fin 1) := Equiv.swap none (some 0)
  have hlin : Irreducible (Polynomial.X + Polynomial.C (X 0 ^ 2) :
      Polynomial (MvPolynomial (Fin 1) (ZMod 2))) := by
    simpa only [map_neg, sub_neg_eq_add] using
      Polynomial.irreducible_X_sub_C (-(X 0 ^ 2 : MvPolynomial (Fin 1) (ZMod 2)))
  have hlin' : (optionEquivLeft (ZMod 2) (Fin 1)).symm
      (Polynomial.X + Polynomial.C (X 0 ^ 2)) =
        renameEquiv (ZMod 2) τ frobeniusContractionInput := by
    apply (optionEquivLeft (ZMod 2) (Fin 1)).injective
    simp [frobeniusContractionInput, τ, optionEquivLeft_X_some, optionEquivLeft_X_none,
      add_comm]
  have h := hlin.map (optionEquivLeft (ZMod 2) (Fin 1)).symm
  rw [hlin'] at h
  exact (MulEquiv.irreducible_iff (renameEquiv (ZMod 2) τ).toMulEquiv).mp h

private theorem degreeOf_frobeniusContractionInput :
    frobeniusContractionInput.degreeOf none = 2 := by
  rw [← natDegree_optionEquivLeft]
  simp only [frobeniusContractionInput, map_add, map_pow, optionEquivLeft_X_none,
    optionEquivLeft_X_some]
  exact Polynomial.natDegree_X_pow_add_C

private theorem pderiv_frobeniusContractionInput :
    pderiv none frobeniusContractionInput = 0 := by
  have htwo : (2 : MvPolynomial (Option (Fin 1)) (ZMod 2)) = 0 := by
    exact CharP.cast_eq_zero (MvPolynomial (Option (Fin 1)) (ZMod 2)) 2
  simp [frobeniusContractionInput, htwo]

/-- In characteristic two, the terminal contraction of `X none ^ 2 + X (some 0)` has positive
Frobenius exponent. -/
example :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option (Fin 1)) (ZMod 2),
      0 < e ∧ rootExpansion (2 ^ e) G = frobeniusContractionInput ∧ pderiv none G ≠ 0 := by
  have hFpos : 0 < frobeniusContractionInput.degreeOf none := by
    rw [degreeOf_frobeniusContractionInput]
    norm_num
  obtain ⟨e, G, hder, hGF, -, -, -, -⟩ :=
    exists_irreducible_frobeniusContraction 2 hFpos irreducible_frobeniusContractionInput
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := by omega
    subst e
    rw [pow_zero, rootExpansion, Polynomial.expand_one, AlgEquiv.symm_apply_apply] at hGF
    apply hder
    rw [hGF]
    exact pderiv_frobeniusContractionInput
  exact ⟨e, G, he, hGF, hder⟩

/-- The same two-variable characteristic-two input has an irreducible separable image in its
fraction field. -/
example : ∃ e : ℕ, ∃ G : MvPolynomial (Option (Fin 1)) (ZMod 2),
    rootExpansion (2 ^ e) G = frobeniusContractionInput ∧
    Irreducible ((optionEquivLeft (ZMod 2) (Fin 1) G).map
      (algebraMap (MvPolynomial (Fin 1) (ZMod 2))
        (FractionRing (MvPolynomial (Fin 1) (ZMod 2))))) ∧
    ((optionEquivLeft (ZMod 2) (Fin 1) G).map
      (algebraMap (MvPolynomial (Fin 1) (ZMod 2))
        (FractionRing (MvPolynomial (Fin 1) (ZMod 2))))).Separable := by
  have hFpos : 0 < frobeniusContractionInput.degreeOf none := by
    rw [degreeOf_frobeniusContractionInput]
    norm_num
  obtain ⟨e, G, -, hGF, -, -, -, -, hIrr, hSep⟩ :=
    exists_frobeniusContraction_fractionRing (L := FractionRing
      (MvPolynomial (Fin 1) (ZMod 2))) 2 hFpos irreducible_frobeniusContractionInput
  exact ⟨e, G, hGF, hIrr, hSep⟩

example : mapExponents (2 • AddMonoidHom.id (Fin 1 →₀ ℕ)) (X 0 : MvPolynomial (Fin 1) ℚ) =
    X 0 ^ 2 := by
  simp only [X, mapExponents_monomial, monomial_pow, one_pow]
  simp [Finsupp.smul_single]

example : (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) ∈ restrictWeightAtMost ![(-1 : ℤ), 1] 0 := by
  simpa using mul_mem_restrictWeightAtMost
    (X_mem_restrictWeightAtMost (R := ℚ) ![(-1 : ℤ), 1] (a := -1) 0 le_rfl)
    (X_mem_restrictWeightAtMost (R := ℚ) ![(-1 : ℤ), 1] (a := 1) 1 le_rfl)

example : Module.finrank ℚ (restrictSupport ℚ
    (↑({0, Finsupp.single 0 1} : Finset (Fin 1 →₀ ℕ)) : Set (Fin 1 →₀ ℕ))) = 2 := by
  rw [finrank_restrictSupport_finset, Finset.card_pair]
  exact (Finsupp.single_ne_zero.mpr one_ne_zero).symm

example : degreeOf 0 (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) ≤ 2 ∧
    (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) ∈ restrictWeightAtMost ![3, 1] 7 := by
  have hmem : (X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) ∈ restrictWeightAtMost ![3, 1] 7 :=
    restrictWeightAtMost_mono _ (by norm_num : (6 : ℕ) ≤ 7)
      (pow_mem_restrictWeightAtMost (X_mem_restrictWeightAtMost (R := ℚ) ![3, 1] 0 le_rfl) 2)
  exact ⟨degreeOf_le_div_of_mem_restrictWeightAtMost hmem (by norm_num), hmem⟩

example :
    (bind₁ ![(X 0 * X 1 : MvPolynomial (Fin 2) ℚ), X 0 ^ 2] (X 0 * X 1)).IsWeightedHomogeneous
      (fun _ ↦ (1 : ℕ)) 4 := by
  have hφ : (X 0 * X 1 : MvPolynomial (Fin 2) ℚ).IsWeightedHomogeneous (fun _ ↦ (2 : ℕ)) 4 :=
    (isWeightedHomogeneous_X ℚ _ 0).mul (isWeightedHomogeneous_X ℚ _ 1)
  refine hφ.bind₁ fun i => ?_
  fin_cases i
  · exact (isWeightedHomogeneous_X ℚ _ 0).mul (isWeightedHomogeneous_X ℚ _ 1)
  · exact (isWeightedHomogeneous_X ℚ _ 0).pow 2

example : (filterSupport (fun e : Fin 2 →₀ ℕ => 0 < e 0)
    (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 : MvPolynomial (Fin 2) ℚ)).IsWeightedHomogeneous
      (fun _ ↦ (1 : ℕ)) 2 := by
  have hX := isWeightedHomogeneous_X ℚ (fun _ : Fin 2 => (1 : ℕ))
  exact ((((hX 0).pow 2).add ((hX 0).mul (hX 1))).add ((hX 1).pow 2)).filterSupport _

example : weightedTruncation (fun _ : Unit ↦ 1) 1
    (bind₁ (fun _ : Unit ↦ X () ^ 2)
      (weightedTruncation (fun _ : Unit ↦ 2) 1 (X () : MvPolynomial Unit ℚ))) =
    weightedTruncation (fun _ : Unit ↦ 1) 1
      (bind₁ (fun _ : Unit ↦ X () ^ 2) (X () : MvPolynomial Unit ℚ)) := by
  exact weightedTruncation_bind₁_weightedTruncation
    (fun _ ↦ pow_mem_restrictWeightedOrder
      (X_mem_restrictWeightedOrder (R := ℚ) (fun _ : Unit ↦ 1) () le_rfl) 2) 1 (X ())
