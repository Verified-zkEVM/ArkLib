/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Spartan.Algebra.Layout
import Mathlib.Data.ZMod.Basic

/-! Field-point checks for the unequal public/witness layout and executable dimension selection. -/

namespace SpartanTest.Layout

open MvPolynomial Spartan

/-- Six public coordinates followed by two private coordinates. -/
abbrev unequalParams : PublicParams := ⟨0, 3, 1, by decide⟩

def publicInput : R1CS.Statement (ZMod 5) unequalParams.toSizeR1CS := ![1, 2, 3, 4, 0, 1]

def witness : R1CS.Witness (ZMod 5) unequalParams.toSizeR1CS := ![2, 4]

-- The public contribution is two, and the witness contribution is also two.
example : eval ![2, 3, 4] (assignmentMLE unequalParams publicInput witness) = (4 : ZMod 5) := by
  rw [assignment_mle_split unequalParams publicInput witness (![2, 3, 4] : Fin 3 → ZMod 5)]
  change (∑ j : Fin 6, eqTilde
    ((finFunctionFinEquiv (m := 2) (n := 3)).symm
      (⟨j.val, by omega⟩ : Fin 8) : Fin 3 → ZMod 5)
      ![2, 3, 4] * (![1, 2, 3, 4, 0, 1] : Fin 6 → ZMod 5) j) +
    (∏ i : Fin 2, (![2, 3, 4] : Fin 3 → ZMod 5) ⟨1 + i.val, by omega⟩) *
      eval (fun i : Fin 1 => (![2, 3, 4] : Fin 3 → ZMod 5) ⟨i.val, by omega⟩)
        (MLE' (![2, 4] : Fin 2 → ZMod 5)) = 4
  rw [MLE'_eval (n := 1) _ (![2, 4] : Fin 2 → ZMod 5)]
  norm_num [eqTilde_eq_prod, Fin.sum_univ_two, Fin.sum_univ_succ, Fin.prod_univ_succ,
    finFunctionFinEquiv]
  decide

-- A zero high coordinate eliminates the private contribution, for every witness.
example (w : R1CS.Witness (ZMod 5) unequalParams.toSizeR1CS) :
    eval ![3, 0, 2] (assignmentMLE unequalParams publicInput w) = (2 : ZMod 5) := by
  rw [assignment_mle_split unequalParams publicInput w (![3, 0, 2] : Fin 3 → ZMod 5)]
  change (∑ j : Fin 6, eqTilde
    ((finFunctionFinEquiv (m := 2) (n := 3)).symm
      (⟨j.val, by omega⟩ : Fin 8) : Fin 3 → ZMod 5)
      ![3, 0, 2] * publicInput j) +
    (∏ i : Fin 2, (![3, 0, 2] : Fin 3 → ZMod 5) ⟨1 + i.val, by omega⟩) *
      eval (fun i : Fin 1 => (![3, 0, 2] : Fin 3 → ZMod 5) ⟨i.val, by omega⟩)
        (MLE' w) = 2
  norm_num [publicInput, eqTilde_eq_prod, Fin.sum_univ_succ, Fin.prod_univ_succ,
    finFunctionFinEquiv]

/-- A full-length witness leaves an empty public prefix. -/
abbrev emptyPublicParams : PublicParams := ⟨0, 1, 1, by decide⟩

example (w : R1CS.Witness (ZMod 5) emptyPublicParams.toSizeR1CS) (r : Fin 1 → ZMod 5) :
    eval r (assignmentMLE emptyPublicParams ![] w) = eval r (MLE' w) := by
  rw [assignment_mle_split emptyPublicParams ![] w r]
  simp [emptyPublicParams]

-- Even an empty source receives positive power-of-two dimensions.
/-- info: true -/
#guard_msgs in
#eval (PublicParams.forSize ⟨0, 0, 0, by decide⟩).toSizeR1CS.m == 1
/-- info: true -/
#guard_msgs in
#eval (PublicParams.forSize ⟨0, 0, 0, by decide⟩).toSizeR1CS.n == 2
/-- info: true -/
#guard_msgs in
#eval (PublicParams.forSize ⟨0, 0, 0, by decide⟩).toSizeR1CS.n_w == 1

-- Five public coordinates and three witness coordinates require two blocks of size eight.
/-- info: true -/
#guard_msgs in
#eval (PublicParams.forSize ⟨3, 8, 3, by decide⟩).toSizeR1CS.m == 4
/-- info: true -/
#guard_msgs in
#eval (PublicParams.forSize ⟨3, 8, 3, by decide⟩).toSizeR1CS.n == 16
/-- info: true -/
#guard_msgs in
#eval (PublicParams.forSize ⟨3, 8, 3, by decide⟩).toSizeR1CS.n_w == 8

end SpartanTest.Layout
