/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.MvPolyEquiv
import CompPoly.Multivariate.Rename
import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Computable multilinear extension (`CMvPolynomial` carrier)

REQ-Binius step 1: computable `CMLE'` mirroring `MLE'` on `Fin (2 ^ n) → R`, with
`fromCMvPolynomial` bridges proved without `map_sub` (use `1 + C (-1) * X` instead of `1 - X`).

**Spec parity (hypercube eval):** `CMLE'_eval_zeroOne` matches `MLE'_eval_zeroOne` in
`ArkLib.Data.MvPolynomial.Multilinear` — same boolean-cube evaluation characterisation.

**Binius API:** `Binius.BinaryBasefold.MultilinearPoly.ofCMLEEvals` / `ofHypercubeEvals` live in
`ProofSystem/Binius/BinaryBasefold/Basic.lean` (see also `ofCMLEEvals_eval_zeroOne`,
`ofCMLEEvals_cmEval_eq_val_eval`).
-/

namespace MvPolynomial

open scoped BigOperators

variable {R : Type} [CommRing R] [BEq R] [LawfulBEq R]

namespace Computational

open CPoly Fintype

variable {n : ℕ}

/-- Bit as ring element (0 or 1). Kept for hypercube reindexing lemmas. -/
@[inline] def fin2ToR (r : Fin 2) : R :=
  (Nat.cast r.val : R)

omit [BEq R] [LawfulBEq R] in
@[simp] lemma fin2ToR_eq_coe (b : Fin 2) : fin2ToR b = (b : R) := by
  unfold fin2ToR
  fin_cases b <;> simp

/--
Pointwise equality gadget matching `singleEqPolynomial (r : R) (X j)` on `r : Fin 2`,
using only `+` / `*` so `fromCMvPolynomial` splits via `map_add` / `map_mul`.
-/
def singleEqCM (r : Fin 2) (j : Fin n) : CMvPolynomial n R :=
  match r with
  | ⟨0, _⟩ => 1 + CMvPolynomial.C (-1 : R) * CMvPolynomial.X j
  | ⟨1, _⟩ => CMvPolynomial.X j

def eqCM (x : Fin n → Fin 2) : CMvPolynomial n R :=
  ∏ j : Fin n, singleEqCM (x j) j

def CMLE' (evals : Fin (2 ^ n) → R) : CMvPolynomial n R :=
  ∑ i : Fin (2 ^ n),
    eqCM (finFunctionFinEquiv.symm i) * CMvPolynomial.C (evals i)

lemma fromCMvPolynomial_singleEqCM (r : Fin 2) (j : Fin n) :
    fromCMvPolynomial (singleEqCM r j) = singleEqPolynomial (r : R) (X j) := by
  fin_cases r
  · simp [singleEqCM, singleEqPolynomial_zero, CPoly.map_add, CPoly.map_mul, CPoly.map_one,
      fromCMvPolynomial_C, fromCMvPolynomial_X]
    ring
  · simp [singleEqCM, singleEqPolynomial_one, fromCMvPolynomial_X]

lemma fromCMvPolynomial_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → CMvPolynomial n R) :
    fromCMvPolynomial (∑ i ∈ s, f i) = ∑ i ∈ s, fromCMvPolynomial (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty, CPoly.map_zero]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, CPoly.map_add, ih]

lemma fromCMvPolynomial_finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → CMvPolynomial n R) :
    fromCMvPolynomial (∏ i ∈ s, f i) = ∏ i ∈ s, fromCMvPolynomial (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty, CPoly.map_one]
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, CPoly.map_mul, ih]

lemma fromCMvPolynomial_eqCM (x : Fin n → Fin 2) :
    fromCMvPolynomial (eqCM x) = eqPolynomial (fun j : Fin n => (x j : R)) := by
  simp only [eqCM, eqPolynomial]
  rw [fromCMvPolynomial_finset_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simpa using fromCMvPolynomial_singleEqCM (x j) j

theorem fromCMvPolynomial_CMLE'_eq_MLE' (evals : Fin (2 ^ n) → R) :
    fromCMvPolynomial (CMLE' evals) = MLE' evals := by
  simp only [CMLE', MLE', MLE]
  rw [fromCMvPolynomial_finset_sum]
  simp_rw [CPoly.map_mul, CPoly.fromCMvPolynomial_C, fromCMvPolynomial_eqCM]
  have hsum :=
    (Fintype.sum_equiv (finFunctionFinEquiv (m := 2) (n := n))
      (fun x : Fin n → Fin 2 =>
        eqPolynomial (fun j : Fin n => (x j : R)) * C (evals (finFunctionFinEquiv x)))
      (fun i : Fin (2 ^ n) =>
        eqPolynomial (fun j : Fin n => (finFunctionFinEquiv.symm i j : R)) * C (evals i))
      (by
        intro x
        refine congr_arg₂ HMul.hMul ?_ rfl
        · refine congr_arg eqPolynomial (funext fun j => ?_)
          let e : (Fin n → Fin 2) ≃ Fin (2 ^ n) := finFunctionFinEquiv
          exact congr_arg (fun t : Fin 2 => (t : R))
            (Eq.symm (congr_fun (Equiv.symm_apply_apply e x) j)))).symm
  simpa [Function.comp_apply] using hsum

/-- Hypercube evaluation for `CMLE'`; matches `MvPolynomial.MLE'_eval_zeroOne`. -/
theorem CMLE'_eval_zeroOne (x : Fin n → Fin 2) (evals : Fin (2 ^ n) → R) :
    CMvPolynomial.eval (x : Fin n → R) (CMLE' evals) =
      evals (finFunctionFinEquiv x) := by
  rw [eval_equiv, fromCMvPolynomial_CMLE'_eq_MLE']
  exact MLE'_eval_zeroOne x evals

/-- `CMvPolynomial.eval` on `CMLE'` agrees with `MvPolynomial.eval` on `MLE'`. -/
theorem CMLE'_eval_eq_MLE'_eval (x : Fin n → Fin 2) (evals : Fin (2 ^ n) → R) :
    CMvPolynomial.eval (x : Fin n → R) (CMLE' evals) =
      MvPolynomial.eval (x : Fin n → R) (MLE' evals) := by
  rw [CMLE'_eval_zeroOne, MLE'_eval_zeroOne]

end Computational

end MvPolynomial
