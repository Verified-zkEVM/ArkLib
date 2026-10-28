/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/

import ArkLib.Commitments.Functional.BitZ.OutOfDomain
import ArkLib.ToCompPoly.Multilinear.Basic

/-!
# BitZ out-of-domain collisions: instances and axiom boundaries

Concrete instances over a finite field `F` with `r = 2` variables, showing that the hypotheses are
satisfiable, that the multilinearity hypothesis is needed, and that the collision bounds apply. A
last client applies the probability bound to CompPoly's evaluation tables, the representation the
protocol uses: the packed vector supplies the Boolean-cube *values* of the multilinear polynomial.
-/

open BitZ MvPolynomial Finset LinearMvExtension

variable {F : Type*} [Field F]

/-- The variables are multilinear. -/
private theorem X_mem (i : Fin 2) : (X i : MvPolynomial (Fin 2) F) ∈
    restrictDegree (Fin 2) F 1 := by
  rw [mem_restrictDegree]
  intro s hs j
  rw [MvPolynomial.support_X] at hs
  rw [mem_singleton.1 hs]
  by_cases h : i = j <;> simp [h]

/-- `powAlgHom` sends `X₀ + X₁` to `X + X²`. -/
example : powAlgHom (X 0 + X 1 : MvPolynomial (Fin 2) F) = Polynomial.X + Polynomial.X ^ 2 := by
  simp [powAlgHom]

/-- The bit encoding separates multilinear monomials: `X₀` encodes `1` and `X₁` encodes `2`. -/
example : bitsValue (Finsupp.single (0 : Fin 2) 1) = 1 ∧
    bitsValue (Finsupp.single (1 : Fin 2) 1) = 2 := by
  simp [bitsValue, Fin.sum_univ_two]

/-- Without multilinearity the substitution can cancel: `X₀² - X₁ ↦ X² - X² = 0`. -/
example : (X 0 ^ 2 - X 1 : MvPolynomial (Fin 2) F) ≠ 0 ∧
    powAlgHom (X 0 ^ 2 - X 1 : MvPolynomial (Fin 2) F) = 0 := by
  refine ⟨fun h => ?_, by simp [powAlgHom]⟩
  have := congrArg (MvPolynomial.eval ![(0 : F), 1]) h
  simp at this

/-- A multilinear polynomial in two variables is sent to a polynomial of degree `≤ 2² - 1 = 3`. -/
example : (powAlgHom (X 0 + X 1 : MvPolynomial (Fin 2) F)).natDegree ≤ 2 ^ 2 - 1 :=
  natDegree_powAlgHom_le (add_mem (X_mem 0) (X_mem 1))

/-- Injectivity needs no subtraction: it holds over the semiring `ℕ`. -/
example : Set.InjOn (powAlgHom (F := ℕ) (m := 2)) (restrictDegree (Fin 2) ℕ 1) :=
  powAlgHom_injOn

variable [Fintype F] [DecidableEq F]

/-- The union bound for the two-element list `{X₀, X₁}`: at most `C(2, 2) · 3` collisions. -/
example : #(collisionSet ({X 0, X 1} : Finset (MvPolynomial (Fin 2) F))) ≤
    (2 : ℕ).choose 2 * (2 ^ 2 - 1) := by
  have h := card_collisionSet_le ({X 0, X 1} : Finset (MvPolynomial (Fin 2) F)) (by
    intro P hP
    rcases mem_insert.1 hP with rfl | hP
    · exact X_mem 0
    · rw [mem_singleton.1 hP]; exact X_mem 1)
  rwa [card_pair (fun h => absurd (X_injective h) (by decide))] at h

/-- The OOD bound for `{X₀, X₁}`: collision probability at most `C(2, 2) · 3 / |F|`. -/
example {K : Type} [Field K] [Fintype K] [SampleableType K] :
    Pr{let ζ ← $ᵗ K}[¬ Set.InjOn (MvPolynomial.eval fun i : Fin 2 => ζ ^ (2 ^ (i : ℕ)))
      ({X 0, X 1} : Set (MvPolynomial (Fin 2) K))] ≤
      ENNReal.ofReal (((2 : ℕ).choose 2 * (2 ^ 2 - 1) : ℕ) / (Fintype.card K : ℝ)) :=
  prob_not_injOn_eval_le (Set.insert_subset_iff.2 ⟨X_mem 0, Set.singleton_subset_iff.2 (X_mem 1)⟩)
    ((Set.encard_insert_le _ _).trans (by simp; norm_num))

/-! ### Evaluation tables -/

section Tables

open CompPoly
open scoped ProbabilityTheory

/-- The multilinear polynomial whose Boolean-cube values are the entries of the table `v`. -/
private noncomputable def tableAsMLE {F : Type*} [CommRing F] {r : ℕ}
    (v : CMlPolynomialEval F r) : MvPolynomial (Fin r) F :=
  MLE fun x => v.get (finFunctionFinEquiv x)

private theorem tableAsMLE_injective {F : Type*} [CommRing F] {r : ℕ} :
    Function.Injective (tableAsMLE (F := F) (r := r)) := by
  intro v w h
  apply Vector.ext
  intro i hi
  have he := congrArg (fun P : MvPolynomial (Fin r) F =>
    toEvalsZeroOne P (finFunctionFinEquiv.symm ⟨i, hi⟩)) h
  simpa only [tableAsMLE, toEvalsZeroOne, MLE_eval_zeroOne, Equiv.apply_symm_apply,
    Vector.get_eq_getElem] using he

private theorem table_eval_eq {F : Type*} [CommRing F] {r : ℕ}
    (v : CMlPolynomialEval F r) (x : Fin r → F) :
    CMlPolynomialEval.eval v (Vector.ofFn x) = MvPolynomial.eval x (tableAsMLE v) := by
  have hv : (Vector.ofFn fun i : Fin (2 ^ r) =>
      v.get (finFunctionFinEquiv (finFunctionFinEquiv.symm i))) = v := by
    ext i hi
    simp [Vector.get_eq_getElem]
  have h := CMlPolynomialEval.eval_eq_MvPolynomial_MLE
    (fun b : Fin r → Fin 2 => v.get (finFunctionFinEquiv b)) x
  rw [hv] at h
  exact h

/-- The OOD bound for CompPoly's executable evaluator: for at most `L_δ` evaluation tables, a
uniform `ζ` makes two distinct tables agree at `(ζ, ζ², …, ζ^{2^{r-1}})` with probability at most
`C(L_δ, 2) · (2^r - 1) / |F|`. -/
theorem prob_table_collision_le {F : Type} [Field F] [Fintype F] [SampleableType F]
    {r Lδ : ℕ} {L : Set (CMlPolynomialEval F r)} (hcard : L.encard ≤ Lδ) :
    Pr{let ζ ← $ᵗ F}[¬ Set.InjOn
      (fun v => CMlPolynomialEval.eval v (Vector.ofFn fun i : Fin r => ζ ^ (2 ^ (i : ℕ)))) L] ≤
      ENNReal.ofReal ((Lδ.choose 2 * (2 ^ r - 1) : ℕ) / (Fintype.card F : ℝ)) := by
  have h := BitZ.prob_not_injOn_eval_le (L := tableAsMLE '' L) (Lδ := Lδ)
    (by rintro _ ⟨v, _, rfl⟩; exact MLE_mem_restrictDegree _)
    ((Set.encard_image_le _ _).trans hcard)
  have heq (ζ : F) :
      ¬ Set.InjOn
        (fun v => CMlPolynomialEval.eval v (Vector.ofFn fun i : Fin r => ζ ^ (2 ^ (i : ℕ)))) L ↔
      ¬ Set.InjOn (MvPolynomial.eval fun i : Fin r => ζ ^ (2 ^ (i : ℕ))) (tableAsMLE '' L) := by
    simp only [table_eval_eq]
    exact not_congr tableAsMLE_injective.injOn.comp_iff
  exact (prEvent_congr ($ᵗ F) _ _ heq).le.trans h

end Tables

/-! ### Axiom boundaries -/

/--
info: 'LinearMvExtension.powAlgHom_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMvExtension.powAlgHom_injOn

/--
info: 'BitZ.card_collisionSet_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.card_collisionSet_le

/--
info: 'BitZ.prob_not_injOn_eval_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BitZ.prob_not_injOn_eval_le

/--
info: 'prob_table_collision_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms prob_table_collision_le

/--
info: 'LinearMvExtension.coeff_powAlgHom_bitsValue' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMvExtension.coeff_powAlgHom_bitsValue
