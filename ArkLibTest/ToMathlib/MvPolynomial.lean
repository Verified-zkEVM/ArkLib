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
import ArkLib.ToMathlib.MvPolynomial.RootContraction
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

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

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

/-- The polynomial `X 0 * Y ^ 2`, with coefficient `X 0` in `ℚ[X 0]`. -/
private noncomputable abbrev coeffSquareQ :
    MvPolynomial (Fin 1) (MvPolynomial (Fin 1) ℚ) :=
  monomial (Finsupp.single 0 2) (X 0)

private theorem support_coeffSquareQ :
    coeffSquareQ.support = {Finsupp.single 0 2} := by
  simp [coeffSquareQ, support_monomial, X_ne_zero]

/-- With `S = X 0`, `N = X 0 ^ 2`, and budget `2`, the total-degree bound `5` is attained. -/
example :
    (clearedSubstitution (RingHom.id _) (X 0 : MvPolynomial (Fin 1) ℚ)
      (fun _ ↦ X 0 ^ 2) (fun _ ↦ 1) 2 coeffSquareQ).totalDegree ≤ 5 ∧
    (clearedSubstitution (RingHom.id _) (X 0 : MvPolynomial (Fin 1) ℚ)
      (fun _ ↦ X 0 ^ 2) (fun _ ↦ 1) 2 coeffSquareQ).totalDegree = 5 := by
  have hbound := totalDegree_clearedSubstitution_le_of_coeff (RingHom.id _)
    (X 0 : MvPolynomial (Fin 1) ℚ) (fun _ ↦ X 0 ^ 2) (fun _ ↦ 1) 2 1 3 coeffSquareQ
    (by simp) (fun _ ↦ by simp [totalDegree_X_pow])
    (by simp [support_coeffSquareQ, Finsupp.weight_single])
    (by simp [support_coeffSquareQ, coeffSquareQ])
  have hvalue : clearedSubstitution (RingHom.id _) (X 0 : MvPolynomial (Fin 1) ℚ)
      (fun _ ↦ X 0 ^ 2) (fun _ ↦ 1) 2 coeffSquareQ = X 0 ^ 5 := by
    simp [clearedSubstitution, support_coeffSquareQ, coeffSquareQ, Finsupp.weight_single]
    ring
  rw [hvalue, totalDegree_X_pow] at hbound ⊢
  exact ⟨hbound, rfl⟩

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

/-- Over `ZMod 2`, the twist carries the root `1` of `X 0 + 1` to a root. -/
example :
    eval (fun _ : Fin 1 ↦ (1 : ZMod 2))
      (inverseFrobeniusTwist 2 1 (X 0 + 1 : MvPolynomial (Fin 1) (ZMod 2))) = 0 := by
  apply eval_inverseFrobeniusTwist_eq_zero 2 1 _ _
  norm_num [eval_add, eval_X]
  exact ZMod.natCast_self 2

/-- Complementary exponent pairs `(1, 2)` and `(2, 1)` recover the square substitution over
`ZMod 2` for two variables. -/
example :
    inverseFrobeniusTwist 2 1 (X 0 + X 1 + 1 : MvPolynomial (Fin 2) (ZMod 2)) ^ 2 =
      variablePowerSubstitution (![1, 2] : Fin 2 → ℕ)
        (variablePowerSubstitution (![2, 1] : Fin 2 → ℕ) (X 0 + X 1 + 1)) := by
  apply inverseFrobeniusTwist_pow_eq_variablePowerSubstitution 2 1
    (q := (![1, 2] : Fin 2 → ℕ)) (r := (![2, 1] : Fin 2 → ℕ))
  · intro i
    fin_cases i <;> norm_num
  · rfl

/-- Irreducibility of `X 0` is preserved by the `ZMod 2` coefficient twist. -/
example :
    Irreducible (inverseFrobeniusTwist 2 1 (X 0 : MvPolynomial (Fin 1) (ZMod 2))) ↔
      Irreducible (X 0 : MvPolynomial (Fin 1) (ZMod 2)) := by
  exact irreducible_inverseFrobeniusTwist_iff 2 1

/-- The `ZMod 2` twist preserves the degree of `X 0 ^ 2 + X 0`. -/
example :
    degreeOf 0 (inverseFrobeniusTwist 2 1
      (X 0 ^ 2 + X 0 : MvPolynomial (Fin 1) (ZMod 2))) =
      degreeOf 0 (X 0 ^ 2 + X 0 : MvPolynomial (Fin 1) (ZMod 2)) := by
  exact degreeOf_inverseFrobeniusTwist 2 1 _ _

/-- The `ZMod 2` twist commutes with the derivative of `X 0 ^ 2 + X 0`. -/
example :
    pderiv 0 (inverseFrobeniusTwist 2 1
      (X 0 ^ 2 + X 0 : MvPolynomial (Fin 1) (ZMod 2))) =
      inverseFrobeniusTwist 2 1
        (pderiv 0 (X 0 ^ 2 + X 0 : MvPolynomial (Fin 1) (ZMod 2))) := by
  exact pderiv_inverseFrobeniusTwist 2 1 _ _

/-! ### Polynomial graph root count -/

/-- The roots `0` and `1` of `X none * (X none - 1)` meet its degree bound over `ℚ`. -/
example : ({0, 1} : Finset ℚ).card ≤
    (X none * (X none - 1) : MvPolynomial (Option Empty) ℚ).degreeOf none := by
  have hφ : Function.Injective
      (aeval (R := ℚ) (fun i : Empty ↦ i.elim) :
        MvPolynomial Empty ℚ →ₐ[ℚ] ℚ) := by
    rw [aeval_injective_iff_of_isEmpty]
    exact RingHom.injective (algebraMap ℚ ℚ)
  have hg : (X none * (X none - 1) : MvPolynomial (Option Empty) ℚ) ≠ 0 := by
    intro h
    have := congrArg (eval (fun _ : Option Empty ↦ (2 : ℚ))) h
    norm_num at this
  apply card_le_degreeOf_none_of_aeval_eq_zero hφ hg
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl <;> norm_num

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

/-! ### Root contraction -/

/-- Expanding `X none + X (some 0)` by two evaluates at `2` as the original does at `4`. -/
example : eval (fun j : Option (Fin 1) ↦ j.elim (2 : ℚ) (fun _ ↦ 3))
    (rootExpansion 2 (X none + X (some 0) : MvPolynomial (Option (Fin 1)) ℚ)) = 7 := by
  rw [eval_rootExpansion]
  norm_num

/-- Mapping the coefficients of a monomial commutes with expansion by two. -/
example :
    map (Int.castRingHom ℚ)
        (rootExpansion 2
          (monomial (Finsupp.single none 2 + Finsupp.single (some ()) 1) 7 :
            MvPolynomial (Option Unit) ℤ)) =
      (monomial (Finsupp.single none 4 + Finsupp.single (some ()) 1) (7 : ℚ) :
        MvPolynomial (Option Unit) ℚ) := by
  rw [map_rootExpansion]
  apply (optionEquivLeft ℚ Unit).injective
  simp [rootExpansion, optionEquivLeft_monomial, Polynomial.expand_monomial]

/-- Evaluating a mapped monomial expansion over `ℤ → ℚ` at `(2, 3)` gives `336`. -/
example :
    eval₂ (Int.castRingHom ℚ) (fun o : Option Unit => o.elim 2 (fun _ => 3))
        (rootExpansion 2
          (monomial (Finsupp.single none 2 + Finsupp.single (some ()) 1) 7 :
            MvPolynomial (Option Unit) ℤ)) = 336 := by
  rw [eval₂_rootExpansion]
  norm_num

/-- Contracting the expansion by two recovers the two-variable linear polynomial. -/
example : rootContraction 2 (rootExpansion 2 (X none + X (some 0) :
    MvPolynomial (Option (Fin 1)) ℚ)) = X none + X (some 0) :=
  rootContraction_rootExpansion (by norm_num) _

/-- Contraction by two reads the coefficient at doubled distinguished exponent `4`. -/
example : (rootContraction 2 (X none ^ 4 * X (some 0) ^ 2 :
    MvPolynomial (Option (Fin 1)) ℚ)).coeff
      (Finsupp.single none 2 + Finsupp.single (some 0) 2) = 1 := by
  calc
    _ = (X none ^ 4 * X (some 0) ^ 2 : MvPolynomial (Option (Fin 1)) ℚ).coeff
          (Finsupp.single none 4 + Finsupp.single (some 0) 2) := by
      rw [coeff_rootContraction (s := 2) (by norm_num)
        (P := (X none ^ 4 * X (some 0) ^ 2 : MvPolynomial (Option (Fin 1)) ℚ))
        (m := Finsupp.single none 2 + Finsupp.single (some 0) 2)]
      congr 1
      ext j
      cases j with
      | none => simp
      | some i =>
          fin_cases i
          simp
    _ = 1 := by
      rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
      simp

/-- Contraction preserves the degree in the other variable for `X none ^ 4 * X (some 0) ^ 2`. -/
example : degreeOf (some (0 : Fin 1))
      (rootContraction 2 (X none ^ 4 * X (some 0) ^ 2 :
        MvPolynomial (Option (Fin 1)) ℚ)) ≤
    degreeOf (some (0 : Fin 1)) (X none ^ 4 * X (some 0) ^ 2 :
      MvPolynomial (Option (Fin 1)) ℚ) :=
  degreeOf_rootContraction_some_le (by norm_num) _ _

/-- In characteristic two, contracting `X none ^ 2 + X (some 0)` halves its degree in `none`. -/
example : (rootContraction 2 (X none ^ 2 + X (some 0) :
      MvPolynomial (Option (Fin 1)) (ZMod 2))).degreeOf none * 2 =
    (X none ^ 2 + X (some 0) : MvPolynomial (Option (Fin 1)) (ZMod 2)).degreeOf none := by
  apply degreeOf_rootContraction_none_mul 2 (by norm_num)
  have htwo : (2 : MvPolynomial (Option (Fin 1)) (ZMod 2)) = 0 :=
    CharP.cast_eq_zero _ 2
  simp [htwo]

/-! ### Radical factor split -/

open UniqueFactorizationMonoid

private noncomputable abbrev radicalSplitPolynomial : MvPolynomial (Fin 2) ℚ := X 0 * X 1

private noncomputable abbrev radicalSplitEvaluation : MvPolynomial (Fin 2) ℚ →+* ℚ :=
  eval₂Hom (RingHom.id ℚ) (fun _ : Fin 2 ↦ 0)

private theorem radicalSplitPolynomial_ne_zero : radicalSplitPolynomial ≠ 0 := by
  intro h
  have h' := congrArg (eval₂Hom (RingHom.id ℚ) (fun _ : Fin 2 ↦ (1 : ℚ))) h
  norm_num [radicalSplitPolynomial] at h'

private theorem rep_mk_X_degree :
    degreeOf (0 : Fin 1) (Associates.mk (X 0 : MvPolynomial (Fin 1) ℚ)).rep = 1 := by
  let c : Associates (MvPolynomial (Fin 1) ℚ) := Associates.mk (X 0)
  have hmk : Associates.mk c.rep = Associates.mk (X 0 : MvPolynomial (Fin 1) ℚ) := by
    simp [c]
  have hassoc : Associated c.rep (X 0 : MvPolynomial (Fin 1) ℚ) :=
    Associates.mk_eq_mk_iff_associated.mp hmk
  have hX : (X 0 : MvPolynomial (Fin 1) ℚ) ≠ 0 := X_ne_zero _
  have hc : c.rep ≠ 0 := by
    intro hz
    have hmk0 := hmk
    rw [hz] at hmk0
    exact (Associates.mk_ne_zero.mpr hX) (hmk0 ▸ rfl)
  rcases hassoc.dvd_dvd with ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hq
    exact hX hq
  have hr0 : r ≠ 0 := by
    intro hr0
    rw [hr0, mul_zero] at hr
    exact hc hr
  have hleft := MvPolynomial.degreeOf_mul_eq (n := (0 : Fin 1)) (p := c.rep) (q := q) hc hq0
  have hright := MvPolynomial.degreeOf_mul_eq (n := (0 : Fin 1))
    (p := (X 0 : MvPolynomial (Fin 1) ℚ)) (q := r) hX hr0
  rw [← hq, degreeOf_X_self] at hleft
  rw [← hr, degreeOf_X_self] at hright
  change degreeOf (0 : Fin 1) c.rep = 1
  omega

private theorem radicalContent_X :
    radicalContent (R := ℚ) (0 : Fin 1) (X 0 : MvPolynomial (Fin 1) ℚ) = 1 := by
  classical
  rw [radicalContent, show primeFactors (Associates.mk (X 0 : MvPolynomial (Fin 1) ℚ)) =
    {Associates.mk (X 0 : MvPolynomial (Fin 1) ℚ)} by
      rw [primeFactors, normalizedFactors_irreducible
        ((Associates.irreducible_mk).2 X_prime.irreducible)]
      simp]
  have hfilter :
      (({Associates.mk (X 0 : MvPolynomial (Fin 1) ℚ)} :
          Finset (Associates (MvPolynomial (Fin 1) ℚ))).filter
        (fun c ↦ degreeOf (0 : Fin 1) c.rep = 0)) = ∅ := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_filter, Finset.mem_singleton] at hc
      rcases hc with ⟨rfl, hdeg⟩
      rw [rep_mk_X_degree] at hdeg
      norm_num at hdeg
    · simp
  rw [hfilter]
  simp

private theorem radicalX_factor_sum_le :
    ∑ _c ∈ positiveDegreeFactorClasses (0 : Fin 1) (X 0 : MvPolynomial (Fin 1) ℚ), 1 ≤ 1 := by
  calc
    _ ≤ ∑ c ∈ positiveDegreeFactorClasses (0 : Fin 1) (X 0 : MvPolynomial (Fin 1) ℚ),
        degreeOf (0 : Fin 1) c.rep := by
      apply Finset.sum_le_sum
      intro _c hc
      exact Nat.succ_le_of_lt (mem_positiveDegreeFactorClasses.mp hc).2
    _ ≤ degreeOf (0 : Fin 1) (X 0 : MvPolynomial (Fin 1) ℚ) := by
      have h := add_sum_degreeOf_positiveDegreeFactorClasses_le
        (0 : Fin 1) (0 : Fin 1) (X 0 : MvPolynomial (Fin 1) ℚ)
      rw [degreeOf_radicalContent] at h
      simpa using h
    _ = 1 := by simp

private noncomputable abbrev exceptionalRootEvaluation (w : Fin 3) (v : Fin 2) :
    MvPolynomial (Fin 1) ℚ →+* ℚ :=
  eval₂Hom (RingHom.id ℚ) (fun _ : Fin 1 ↦
    if w = 0 then (v.val : ℚ) else (v.val : ℚ) - 1)

/-- The two radicals of a nonzero polynomial multiply to its radical representative. -/
example :
    radicalContent 0 (X 1 * X 0 ^ 2 : MvPolynomial (Fin 2) ℚ) *
        radicalPrimPart 0 (X 1 * X 0 ^ 2) = radicalRep (X 1 * X 0 ^ 2) :=
  radicalContent_mul_radicalPrimPart 0 (X 1 * X 0 ^ 2)

/-- At the origin, the split radical product and `X 0 * X 1` have the same zero value. -/
example : radicalSplitEvaluation (radicalContent 0 radicalSplitPolynomial *
    radicalPrimPart 0 radicalSplitPolynomial) = 0 ↔
    radicalSplitEvaluation radicalSplitPolynomial = 0 :=
  map_radicalContent_mul_radicalPrimPart_eq_zero_iff radicalSplitEvaluation 0
    radicalSplitPolynomial_ne_zero

/-- The total-degree budget for the factor split of `X 0 * X 1`. -/
example : totalDegree (radicalContent 0 radicalSplitPolynomial) +
    ∑ c ∈ positiveDegreeFactorClasses 0 radicalSplitPolynomial, totalDegree c.rep ≤
      totalDegree radicalSplitPolynomial :=
  add_sum_totalDegree_positiveDegreeFactorClasses_le 0 radicalSplitPolynomial

/-- For the nonconstant polynomial `X`, a proper challenge exception leaves a root whose challenge
is nonzero, so the combined exceptional-set conclusion has content. -/
example : ∃ ex : Finset (Fin 3), (ex.card : ℤ) ≤ 2 ∧
    ∃ w ∉ ex, ∃ v : Fin 2, exceptionalRootEvaluation w v (X 0) = 0 ∧ w ≠ 0 := by
  let Q : MvPolynomial (Fin 1) ℚ := X 0
  let Good : Fin 3 → Fin 2 → Prop := fun w _ ↦ w ≠ 0
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_of_factor_exceptional
    (R := ℚ) (σ := Fin 1) (K := ℚ) (Fn := MvPolynomial (Fin 1) ℚ →+* ℚ) (α := ℤ)
    0 (Q := Q) (X_ne_zero _) (fun w v ↦ exceptionalRootEvaluation w v) Good 1 (fun _ ↦ 1)
    (by
      refine ⟨{0}, by norm_num, ?_⟩
      intro w hw v
      simp [Q, radicalContent_X])
    (by
      intro c hc
      refine ⟨{0}, by norm_num, ?_⟩
      intro w hw v hzero
      change w ≠ 0
      simpa using hw)
  have hsum :
      (∑ c ∈ positiveDegreeFactorClasses (0 : Fin 1) Q, (1 : ℤ)) ≤ 1 := by
    exact_mod_cast radicalX_factor_sum_le
  have hcard' : (ex.card : ℤ) ≤ 2 := by
    calc
      (ex.card : ℤ) ≤ 1 + ∑ c ∈ positiveDegreeFactorClasses (0 : Fin 1) Q, (1 : ℤ) := hcard
      _ ≤ 2 := by linarith
  have hzero0 : exceptionalRootEvaluation 0 0 Q = 0 := by simp [exceptionalRootEvaluation, Q]
  have h0 : (0 : Fin 3) ∈ ex := by
    by_contra hnot
    have h := hgood 0 hnot 0 hzero0
    exact h (by decide)
  have hnotall : 1 ∉ ex ∨ 2 ∉ ex := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin 3)) ⊆ ex := by
      intro w hw
      fin_cases w
      · exact h0
      · exact h.1
      · exact h.2
    have hcardNat : ex.card ≤ 2 := by exact_mod_cast hcard'
    have hlarge : 3 ≤ ex.card := by
      simpa using Finset.card_le_card hsub
    omega
  rcases hnotall with h1 | h2
  · refine ⟨ex, hcard', 1, h1, 1, ?_, by decide⟩
    simp [exceptionalRootEvaluation]
  · refine ⟨ex, hcard', 2, h2, 1, ?_, by decide⟩
    simp [exceptionalRootEvaluation]

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

/-- The option-variable polynomial's total degree is its weighted degree after splitting. -/
example :
    (optionEquivRight ℚ (Fin 1)
      (monomial (Finsupp.single none 5 + Finsupp.single (some 0) 1) (1 : ℚ))).totalDegree = 1 := by
  rw [totalDegree_optionEquivRight, weightedTotalDegree_monomial _ _ _ one_ne_zero]
  rw [map_add]
  simp [Finsupp.weight_single]

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

/-- Flattening a constant coefficient of degree one bounds the distinguished-variable degree. -/
example :
    ((optionEquivRight ℚ Unit).symm (C (Polynomial.X : Polynomial ℚ)) :
      MvPolynomial (Option Unit) ℚ).weightedTotalDegree
        (fun i ↦ i.elim 1 (fun _ ↦ 0)) ≤ 1 := by
  exact weightedTotalDegree_optionEquivRight_symm_coefficientDegree_le
    ((coeffNatDegreeLE_C (p := (Polynomial.X : Polynomial ℚ)) (by simp)) :
      CoeffNatDegreeLE (C Polynomial.X : MvPolynomial Unit (Polynomial ℚ)) 1)

private noncomputable abbrev clearedDegreeTwoExample : MvPolynomial Unit (Polynomial ℚ) :=
  clearedSubstitution C (C (Polynomial.X : Polynomial ℚ))
    (fun _ : Unit ↦ C (Polynomial.X : Polynomial ℚ)) (fun _ ↦ 1) 1
    (C (Polynomial.X : Polynomial ℚ) * X ())

/-- Clearing a substitution attains the degree-two coefficient bound for `t * Y`. -/
example : CoeffNatDegreeLE clearedDegreeTwoExample 2 ∧
    (clearedDegreeTwoExample.coeff 0).natDegree = 2 := by
  constructor
  · apply CoeffNatDegreeLE.clearedSubstitution
      (S := C (Polynomial.X : Polynomial ℚ))
      (N := fun _ : Unit ↦ C (Polynomial.X : Polynomial ℚ))
      (d := fun _ ↦ 1) (H := 1) (h := 1)
      (Q := C (Polynomial.X : Polynomial ℚ) * X ())
    · exact coeffNatDegreeLE_C (by simp)
    · intro _
      exact coeffNatDegreeLE_C (by simp)
    · intro m hm
      have hm' : m = Finsupp.single () 1 := by
        change m ∈ (C (Polynomial.X : Polynomial ℚ) * X ()).support at hm
        rw [C_mul_X_eq_monomial] at hm
        exact Finset.mem_singleton.mp (support_monomial_subset hm)
      subst m
      simp [Finsupp.weight_apply]
    · intro m _
      have hcoeff : CoeffNatDegreeLE
          (C (Polynomial.X : Polynomial ℚ) * X ()) 1 := by
        exact (coeffNatDegreeLE_C (p := (Polynomial.X : Polynomial ℚ)) (by simp)).mul
          (coeffNatDegreeLE_X ())
      exact hcoeff m
  · simp [clearedDegreeTwoExample, clearedSubstitution, C_mul_X_eq_monomial,
      support_monomial, Finsupp.weight_apply]

/-- The coefficient and jet degree bounds flatten to bidegree `(1, 1)` for `t * Y`. -/
example : (optionEquivRight ℚ Unit).symm paramTimesVar ∈
    restrictBidegree Unit ℚ 1 1 := by
  have hheight : CoeffNatDegreeLE paramTimesVar 1 := by
    exact (coeffNatDegreeLE_C (p := (Polynomial.X : Polynomial ℚ)) (by simp)).mul
      (coeffNatDegreeLE_X ())
  have hjet : paramTimesVar.totalDegree ≤ 1 := by
    rw [paramTimesVar, C_mul_X_eq_monomial,
      totalDegree_monomial _ Polynomial.X_ne_zero]
    simp
  exact optionEquivRight_symm_mem_restrictBidegree hheight hjet

/-! ### Division-free Schwartz–Zippel -/

/-- `X 0` has exactly two zeros on `(ZMod 2)²`, attaining the degree bound `2`. -/
example : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 2)) |
      eval x (X 0 : MvPolynomial (Fin 2) (ZMod 2)) = 0} = 2 ∧
    (X 0 : MvPolynomial (Fin 2) (ZMod 2)).totalDegree * #(univ : Finset (ZMod 2)) ^ 1 = 2 ∧
    #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 2)) |
      eval x (X 0 : MvPolynomial (Fin 2) (ZMod 2)) = 0} ≤
      (X 0 : MvPolynomial (Fin 2) (ZMod 2)).totalDegree * #(univ : Finset (ZMod 2)) ^ 1 := by
  have hcount : #{x ∈ Fintype.piFinset fun _ : Fin 2 ↦ (univ : Finset (ZMod 2)) |
      eval x (X 0 : MvPolynomial (Fin 2) (ZMod 2)) = 0} = 2 := by
    simp only [eval_X]
    decide
  have hdegree : (X 0 : MvPolynomial (Fin 2) (ZMod 2)).totalDegree *
      #(univ : Finset (ZMod 2)) ^ 1 = 2 := by
    rw [totalDegree_X, card_univ, ZMod.card]
    rfl
  have hbound := card_filter_eval_eq_zero_le
    (p := (X 0 : MvPolynomial (Fin 2) (ZMod 2))) (X_ne_zero (0 : Fin 2))
    (univ : Finset (ZMod 2))
  exact ⟨hcount, hdegree, by simpa only [hcount, hdegree] using hbound⟩

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

/-- Substituting `X 0 ^ 2` for `X 0` gives the computed allowance `2`. -/
example :
    SupportWeightOffset (Finsupp.applyAddHom (0 : Fin 1))
      (0 : (Fin 1 →₀ ℕ) →+ ℕ) 2 (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ) := by
  have h := supportWeightOffset_aeval
    (Finsupp.applyAddHom (0 : Fin 1)) (0 : (Fin 1 →₀ ℕ) →+ ℕ)
    (fun _ : Fin 1 ↦ 2) (fun _ : Fin 1 ↦ (X 0 ^ 2 : MvPolynomial (Fin 1) ℚ))
    (by
      intro i
      fin_cases i
      simpa only [X_pow_eq_monomial] using
        SupportWeightOffset.monomial (Finsupp.single (0 : Fin 1) 2) (1 : ℚ)
          (by simp [Finsupp.applyAddHom]))
    (X 0 : MvPolynomial (Fin 1) ℚ)
  have hdeg : weightedTotalDegree (fun _ : Fin 1 ↦ 2) (X 0 : MvPolynomial (Fin 1) ℚ) = 2 := by
    simp [weightedTotalDegree, support_X, Finsupp.weight_single]
  simpa [hdeg] using h

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

private def rootCountBox (i : Fin 2) : Finset ℚ := if i = 0 then {0} else {0, 1}

private def rootCountPoints : Finset (Fin 2 → ℚ) := {![0, 0], ![0, 1]}

private noncomputable def rootCountPolynomial : MvPolynomial (Fin 2) ℚ := X 0

private noncomputable def rootCountSpecializationPolynomial : MvPolynomial (Fin 2) ℚ := X 0 ^ 2

/-- The specialization count includes the zero-derivative root of `X 0 ^ 2`. -/
example : rootCountPoints.card ≤ rootCountSpecializationPolynomial.degreeOf 0 *
    ∏ j ∈ (Finset.univ : Finset (Fin 2)).erase 0, (rootCountBox j).card := by
  apply card_le_degreeOf_mul_prod_of_univariateSpecialization_ne_zero
    rootCountBox 0 rootCountSpecializationPolynomial rootCountPoints
  intro x hx
  simp only [rootCountPoints, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · refine ⟨?_, by simp [rootCountSpecializationPolynomial], ?_⟩
    · simp [Fintype.mem_piFinset, rootCountBox]
    · simp [rootCountSpecializationPolynomial, univariateSpecialization]
  · refine ⟨?_, by simp [rootCountSpecializationPolynomial], ?_⟩
    · simp [Fintype.mem_piFinset, rootCountBox]
    · simp [rootCountSpecializationPolynomial, univariateSpecialization]

/-- The same two roots have nonzero `0`-derivative, giving the derivative root-count bound. -/
example : rootCountPoints.card ≤ rootCountPolynomial.degreeOf 0 *
    ∏ j ∈ (Finset.univ : Finset (Fin 2)).erase 0, (rootCountBox j).card := by
  apply card_le_degreeOf_mul_prod_of_eval_pderiv_ne_zero
    rootCountBox 0 rootCountPolynomial rootCountPoints
  intro x hx
  simp only [rootCountPoints, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · refine ⟨?_, by simp [rootCountPolynomial], by simp [rootCountPolynomial]⟩
    simp [Fintype.mem_piFinset, rootCountBox]
  · refine ⟨?_, by simp [rootCountPolynomial], by simp [rootCountPolynomial]⟩
    simp [Fintype.mem_piFinset, rootCountBox]

/-! ### Taylor-chart evaluation bridges -/

namespace MvPolynomialEvaluationTest

open MvPolynomial Polynomial

noncomputable section

private def point : Option Unit → ℚ
  | none => 2
  | some () => 3

/-- A flattened polynomial depending on both evaluation coordinates. -/
private abbrev flattened : MvPolynomial (Option Unit) ℚ :=
  X none ^ 2 * X (some ()) + X none + X (some ())

/-- A polynomial-coefficient polynomial depending on both evaluation coordinates. -/
private abbrev polynomialCoefficients : MvPolynomial Unit (Polynomial ℚ) :=
  MvPolynomial.C ((Polynomial.X : ℚ[X]) ^ 2 + 1) * MvPolynomial.X () +
    MvPolynomial.C ((Polynomial.X : ℚ[X]) + 2)

/-- Evaluation after flattening computes the same value as direct evaluation. -/
example :
    aeval (fun j : Unit ↦ point (some j))
        (map (Polynomial.aeval (point none)).toRingHom
          (optionEquivRight ℚ Unit flattened)) = 17 ∧
      aeval point flattened = 17 := by
  constructor
  · rw [aeval_map_optionEquivRight]
    norm_num [point, flattened]
  · norm_num [point, flattened]

/-- Evaluation after unflattening computes the same value as successive evaluation. -/
example :
    aeval point ((optionEquivRight ℚ Unit).symm polynomialCoefficients) = 19 ∧
      aeval (fun j : Unit ↦ point (some j))
        (map (Polynomial.aeval (point none)).toRingHom polynomialCoefficients) = 19 := by
  constructor
  · rw [aeval_optionEquivRight_symm]
    norm_num [point, polynomialCoefficients]
  · norm_num [point, polynomialCoefficients]

end

end MvPolynomialEvaluationTest
