/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.ClearedSubstitution
import ArkLib.ToMathlib.MvPolynomial.CompleteHomogeneous
import ArkLib.ToMathlib.MvPolynomial.FirstOrderTaylor
import ArkLib.ToMathlib.MvPolynomial.FrobeniusPullback
import ArkLib.ToMathlib.MvPolynomial.OptionRoots
import ArkLib.ToMathlib.MvPolynomial.OptionWeightedDegree
import ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
import ArkLib.ToMathlib.MvPolynomial.RadicalSplit
import ArkLib.ToMathlib.MvPolynomial.SchwartzZippel
import ArkLib.ToMathlib.MvPolynomial.SupportWeight
import ArkLib.ToMathlib.MvPolynomial.SupportWeightOffset
import ArkLib.ToMathlib.MvPolynomial.UnivariateSpecialization
import ArkLib.Data.MvPolynomial.WeightedDegree
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Acceptance cases for multivariate polynomial results

Concrete examples exercise cleared substitution, symmetric polynomial evaluation, Taylor
divisibility, Frobenius twisting, polynomial root counting, weighted degrees, coefficient degrees,
and specialization.
-/

open Finset MvPolynomial
open scoped Polynomial

/-! ### Cleared substitution -/

/-- The test polynomial `X 0 ^ 2` in one variable. -/
private noncomputable abbrev squareQ : MvPolynomial (Fin 1) ℚ := X 0 ^ 2

private theorem support_squareQ : squareQ.support = {Finsupp.single 0 2} := by
  rw [squareQ, X_pow_eq_monomial, support_monomial]
  simp

/-- With `S = 3`, numerator `5`, and budget `3`, the cleared map agrees with rational evaluation. -/
example :
    (RingHom.id ℚ)
      (clearedSubstitution (RingHom.id ℚ) 3 (fun _ ↦ 5) (fun _ ↦ 1) 3 squareQ) =
      3 ^ 3 * eval₂ (RingHom.id ℚ) (fun _ ↦ (5 : ℚ) / 3 ^ 1) squareQ := by
  exact map_clearedSubstitution (RingHom.id ℚ) (RingHom.id ℚ) 3 (by norm_num)
    (fun _ ↦ 5) (fun _ ↦ 1) 3 squareQ (by simp [support_squareQ, Finsupp.weight_single])

/-! ### Complete homogeneous polynomials -/

/-- The power-sum identity evaluates `h₂(1, 2)` to `7`. -/
example : eval (![1, 2] : Fin 2 → ℝ) (hsymm (Fin 2) ℝ 2) = 7 := by
  have h := two_mul_eval_hsymm_two (![1, 2] : Fin 2 → ℝ)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  linarith

/-- The power-sum identity evaluates `h₃(1, 1)` to `4`. -/
example : eval (fun _ : Fin 2 ↦ (1 : ℝ)) (hsymm (Fin 2) ℝ 3) = 4 := by
  have h := six_mul_eval_hsymm_three (fun _ : Fin 2 ↦ (1 : ℝ))
  norm_num at h
  linarith

/-! ### First-order Taylor congruence -/

/-- For `x³` over `ℤ`, the remainder after its linear term is divisible by `t²`. -/
example : (3 : ℤ) ^ 2 ∣ (2 + 3) ^ 3 - 2 ^ 3 - 3 * 2 ^ 2 * 3 := by
  have h := pow_succ_dvd_eval₂Hom_add_sub_pderiv (RingHom.id ℤ) (fun _ : Fin 1 ↦ (2 : ℤ))
    (fun _ ↦ (3 : ℤ)) Finset.univ (X 0 ^ 3) 0 3 1 one_pos (Finset.mem_univ 0) (by simp)
    (fun i _ hi ↦ absurd (Subsingleton.elim i 0) hi) (fun i hi ↦ absurd (Finset.mem_univ i) hi)
  convert h using 1
  simp [Derivation.leibniz_pow]

/-! ### Frobenius twist -/

/-- Over `ZMod 2`, the inverse Frobenius twist of `X 0 + X 1` squares to its expansion. -/
example :
    inverseFrobeniusTwist 2 1 (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) ^ 2 =
      (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod 2)).expand 2 :=
  inverseFrobeniusTwist_pow 2 1 _

/-! ### Polynomial graph root count -/

/-- The two graphs `X` and `-X` on `y² = t²` meet the degree bound. -/
example : ({Polynomial.X, -Polynomial.X} : Finset ℚ[X]).card ≤ 2 := by
  let g : MvPolynomial (Option (Fin 1)) ℚ := X (some 0) ^ 2 - X none ^ 2
  have hg : g ≠ 0 := by
    intro h
    have := congrArg (aeval fun o : Option (Fin 1) ↦ o.elim (0 : ℚ) fun _ ↦ 1) h
    simp [g] at this
  have hgraphs : ∀ q ∈ ({Polynomial.X, -Polynomial.X} : Finset ℚ[X]),
      aeval (fun o : Option (Fin 1) ↦ o.elim Polynomial.X fun _ ↦ q) g = 0 := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [g]
  have h := card_le_degreeOf_some_of_aeval_eq_zero hg _ hgraphs
  have hdeg : g.degreeOf (some 0) ≤ 2 := by
    dsimp [g]
    refine (degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · exact (degreeOf_pow_le _ _ _).trans (by simp)
    · simp [degreeOf_X_pow_of_ne]
  have hX : (Polynomial.X : ℚ[X]) ≠ -Polynomial.X := by
    intro h
    have := congrArg (fun p : ℚ[X] ↦ p.eval 1) h
    norm_num at this
  have hcard : ({Polynomial.X, -Polynomial.X} : Finset ℚ[X]).card = 2 := by simp [hX]
  rw [hcard] at h
  omega

/-! ### Radical factor split -/

open UniqueFactorizationMonoid

/-- The two radicals of a nonzero polynomial multiply to its radical representative. -/
example :
    radicalContent 0 (X 1 * X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) *
        radicalPrimPart 0 (X 1 * X 0 ^ 2) = radicalRep (X 1 * X 0 ^ 2) :=
  radicalContent_mul_radicalPrimPart 0 (X 1 * X 0 ^ 2)

/-! ### Weighted degree -/

/-- The split exponent vector has weight `5 * 3 + 2 * 7 = 29`. -/
example :
    ((Finsupp.single (0 : Fin 1) 2).optionElim 3).weight
      (fun v : Option (Fin 1) ↦ v.elim 5 (fun _ ↦ 7)) = 29 := by
  rw [Finsupp.weight_optionElim]
  simp [Finsupp.weight_single]

/-- `X none ^ 5 * X (some 0)` maps to `X 0` with coefficient `X ^ 5`. -/
example :
    optionEquivRight ℚ (Fin 1)
        (monomial (Finsupp.single none 5 + Finsupp.single (some 0) 1) (1 : ℚ)) =
      monomial (Finsupp.single 0 1) (Polynomial.monomial 5 1) := by
  rw [optionEquivRight_monomial]
  congr 1
  · ext j
    simp
  · simp

/-! ### Polynomial coefficients -/

/-- The polynomial `t * Y`, with `t` in the coefficient ring `ℚ[t]`. -/
private noncomputable abbrev paramTimesVar : MvPolynomial Unit (Polynomial ℚ) :=
  C Polynomial.X * X ()

/-- Each coefficient of `t * Y` has degree at most `1` in `t`. -/
example : CoeffNatDegreeLE paramTimesVar 1 := by
  simpa using (coeffNatDegreeLE_C (σ := Unit) (p := (Polynomial.X : Polynomial ℚ))
    (by simp)).mul (coeffNatDegreeLE_X ())

/-- Moving `X none` out as a polynomial variable commutes with casting coefficients to `ℚ`. -/
example :
    Polynomial.map (map (Int.castRingHom ℚ))
        (optionEquivLeft ℤ Unit (X none : MvPolynomial (Option Unit) ℤ)) =
      optionEquivLeft ℚ Unit
        (map (Int.castRingHom ℚ) (X none : MvPolynomial (Option Unit) ℤ)) :=
  map_optionEquivLeft _ _

/-- The joint total degree of `t * Y` is `2`. -/
example : jointTotalDegree paramTimesVar = 2 := by
  have h : (optionEquivRight ℚ Unit).symm paramTimesVar =
      monomial (Finsupp.single none 1 + Finsupp.single (some ()) 1) 1 := by
    rw [paramTimesVar, map_mul, optionEquivRight_symm_C, optionEquivRight_symm_X,
      Polynomial.aeval_X, X, X, monomial_mul_monomial, one_mul]
  rw [jointTotalDegree, h, totalDegree_monomial _ one_ne_zero,
    Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
  simp

/-- Mapping coefficients from `ℤ` and evaluating at `2` commutes for `t * Y`. -/
example :
    map (Polynomial.evalRingHom (2 : ℚ))
        (map (Polynomial.mapRingHom (Int.castRingHom ℚ))
          (C (Polynomial.X : Polynomial ℤ) * X () : MvPolynomial Unit (Polynomial ℤ))) =
      map (Polynomial.eval₂RingHom (Int.castRingHom ℚ) (2 : ℚ))
        (C (Polynomial.X : Polynomial ℤ) * X () : MvPolynomial Unit (Polynomial ℤ)) :=
  eval_map_coefficients (σ := Unit) (Int.castRingHom ℚ) 2
    (C (Polynomial.X : Polynomial ℤ) * X ())

/-! ### Division-free Schwartz–Zippel -/

/-- `X 0` has exactly two zeros on `(ZMod 2)²`, attaining the degree bound `2`. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 2)) |
      eval x (X 0 : MvPolynomial (Fin 2) (ZMod 2)) = 0} = 2 ∧
    (X 0 : MvPolynomial (Fin 2) (ZMod 2)).totalDegree * #(univ : Finset (ZMod 2)) ^ 1 = 2 := by
  refine ⟨?_, by rw [totalDegree_X, card_univ, ZMod.card]; rfl⟩
  simp only [eval_X]
  decide

/-! ### Support weights -/

/-- With `t i = i` on `Fin 3`, the denominator budget `2 * 3 - 2 = 4` is attained. -/
example :
    Finsupp.weight (fun i : Fin 3 ↦ 2 * i.val - 1)
      (Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) = 4 ∧
    Finsupp.weight (fun i : Fin 3 ↦ 2 * i.val - 1)
      (Finsupp.single (1 : Fin 3) 1 + Finsupp.single (2 : Fin 3) 1) ≤ 2 * 3 - 2 := by
  refine ⟨by simp [Finsupp.weight_single], ?_⟩
  refine Finsupp.weight_two_mul_sub_one_le (fun i : Fin 3 ↦ i.val) _ ?_ ?_
  · simp [Finsupp.weight_single]
  · intro i _
    omega

/-- `X (some 0) * X none` satisfies the coefficient-variable support inequality. -/
example :
    (X (some 0) * X none : MvPolynomial (Option (Fin 1)) ℚ) ∈
      supportWeightLE (Finsupp.weight (fun i : Option (Fin 1) ↦ i.elim 0 (fun _ ↦ 1)))
        (Finsupp.applyAddHom none) := by
  rw [X, X, monomial_mul_monomial, one_mul]
  exact monomial_mem_supportWeightLE _ _ _ _ (by simp)

/-! ### Support-weight allowance -/

/-- `X 0 ^ 3 * X 1` has allowance `2`, and no smaller allowance. -/
example :
    SupportWeightOffset (Finsupp.applyAddHom 0) (Finsupp.applyAddHom 1) 2
        (monomial (Finsupp.single 0 3 + Finsupp.single 1 1) (1 : ℚ)) ∧
      ¬ SupportWeightOffset (Finsupp.applyAddHom 0) (Finsupp.applyAddHom 1) 1
        (monomial (Finsupp.single 0 3 + Finsupp.single 1 1) (1 : ℚ)) := by
  refine ⟨SupportWeightOffset.monomial _ _ (by simp [Finsupp.applyAddHom]), fun h ↦ ?_⟩
  have := h (Finsupp.single 0 3 + Finsupp.single 1 1) (by simp)
  simp at this

/-! ### Univariate specialization -/

/-- Specializing `X 0 * X 1` in `X 1` at `(3, 5)` and evaluating at `2` gives `6`. -/
example :
    (univariateSpecialization (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) 1 ![3, 5]).eval 2 = 6 := by
  rw [eval_univariateSpecialization]
  norm_num [Function.update]
