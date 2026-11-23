/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude.Fibers
public import ArkLib.ProofSystem.Sumcheck.Structured
public import CompPoly.Multilinear.Unique
public import CompPoly.Multivariate.Operations

/-!
# Executable Boolean-table witnesses for FRI-Binius

Ring switching produces a table of packed evaluations. The Binary Basefold opening expects
a multilinear polynomial. Convert the table to monomial coefficients with CompPoly's transform
and use the little-endian Boolean ordering in both directions.
-/

@[expose] public section

namespace Binius.FRIBinius

open CompPoly CPoly Finset MvPolynomial Sumcheck.Structured

variable {R : Type} [CommRing R] {n : ℕ}

@[no_expose] private def polynomialFromTable [DecidableEq R] (a : (Fin n → Fin 2) → R) :
    MvPolynomial (Fin n) R :=
  let table : CMlPolynomialEval R n := Vector.ofFn (a ∘ finFunctionFinEquiv.symm)
  let coeffs := CMlPolynomial.lagrangeToMono n table
  CPoly.fromCMvPolynomial (∑ j : Fin (2 ^ n),
    CMvPolynomial.monomial (Vector.ofFn fun (i : Fin n) => Nat.getBit i.val j.val) (coeffs.get j))

private theorem polynomialFromTable_eq [DecidableEq R] (a : (Fin n → Fin 2) → R) :
    polynomialFromTable a =
      (CMlPolynomialEval.toMvPolynomial (Vector.ofFn (a ∘ finFunctionFinEquiv.symm))) := by
  unfold polynomialFromTable CMlPolynomialEval.toMvPolynomial CMlPolynomial.toMvPolynomial
  rw [CMvPolynomial.fromCMvPolynomial_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [CMvPolynomial.fromCMvPolynomial_monomial]
  have hMono : CMvMonomial.toFinsupp (Vector.ofFn fun (i : Fin n) =>
      Nat.getBit i.val j.val) = CMlPolynomial.monomialOfNat j.val := by
    apply Finsupp.ext
    intro i
    simp [CMvMonomial.toFinsupp, CMlPolynomial.monomialOfNat]
  rw [hMono]
  rfl

/-- Construct the multilinear extension of the Boolean table with computable coefficients. -/
@[no_expose]
def multilinearOfTable [DecidableEq R] (a : (Fin n → Fin 2) → R) : MultilinearPoly R n :=
  ⟨polynomialFromTable a, by
    rw [polynomialFromTable_eq]
    exact CMlPolynomial.toMvPolynomial_is_multilinear _⟩

/-- Evaluating the constructed polynomial on a Boolean point recovers the table entry. -/
theorem eval_multilinearOfTable [DecidableEq R] (a : (Fin n → Fin 2) → R)
    (y : Fin n → Fin 2) : (multilinearOfTable a).val.eval (y : Fin n → R) = a y := by
  have h := CMlPolynomialEval.eval_toMvPolynomial_vertex
    (Vector.ofFn (a ∘ finFunctionFinEquiv.symm)) (finFunctionFinEquiv y)
  change (polynomialFromTable a).eval (y : Fin n → R) = a y
  rw [polynomialFromTable_eq]
  have hVertex : (CMlPolynomialEval.vertex (R := R) (finFunctionFinEquiv y)).get =
      (y : Fin n → R) := by
    calc
      _ = Binius.BinaryBasefold.bitsOfIndex (finFunctionFinEquiv y) := by
        funext i
        simp [CMlPolynomialEval.vertex, Binius.BinaryBasefold.bitsOfIndex,
          BitVec.getLsb]
      _ = ((finFunctionFinEquiv.symm (finFunctionFinEquiv y) : Fin n → Fin 2) : Fin n → R) :=
        (Binius.BinaryBasefold.coe_fin_pow_two_eq_bitsOfIndex _).symm
      _ = _ := congrArg (fun a : Fin n → Fin 2 => (a : Fin n → R))
        (Equiv.symm_apply_apply _ _)
  rw [hVertex] at h
  have ha : (Vector.ofFn (a ∘ finFunctionFinEquiv.symm))[finFunctionFinEquiv y] = a y := by
    change (Vector.ofFn (a ∘ finFunctionFinEquiv.symm)).get (finFunctionFinEquiv y) = _
    simp only [Vector.get_ofFn, Function.comp_apply, Equiv.symm_apply_apply]
  exact h.trans ha

private theorem toTable_multilinearOfTable [DecidableEq R] [IsDomain R]
    (a : (Fin n → Fin 2) → R) :
    MvPolynomial.MLEEquiv (R := R) (σ := Fin n) (multilinearOfTable a) = a :=
  funext (eval_multilinearOfTable a)

private theorem multilinearOfTable_toTable [DecidableEq R] [IsDomain R]
    (p : MultilinearPoly R n) :
    multilinearOfTable (fun x : Fin n → Fin 2 => p.val.eval (x : Fin n → R)) = p := by
  let e := MvPolynomial.MLEEquiv (R := R) (σ := Fin n)
  have hp : (fun x : Fin n → Fin 2 => p.val.eval (x : Fin n → R)) = e p := rfl
  rw [hp]
  exact e.injective (toTable_multilinearOfTable (e p))

/-- Equivalence of Boolean tables and multilinear witnesses, with executable conversions. -/
@[no_expose]
def tableWitnessEquiv [DecidableEq R] [IsDomain R] :
    ((Fin n → Fin 2) → R) ≃ MultilinearPoly R n where
  toFun := multilinearOfTable
  invFun t y := t.val.eval (y : Fin n → R)
  left_inv a := funext (eval_multilinearOfTable a)
  right_inv := multilinearOfTable_toTable

/-- The forward conversion constructs the multilinear extension of the table. -/
theorem tableWitnessEquiv_apply [DecidableEq R] [IsDomain R] (a : (Fin n → Fin 2) → R) :
    tableWitnessEquiv a = multilinearOfTable a := by
  unfold tableWitnessEquiv
  rfl

/-- Use the multilinear extension of a Boolean table as the witness in a relation,
leaving the statement unchanged. -/
def tableWitnessRelation [DecidableEq R] [IsDomain R] {Statement : Type}
    (relation : Set (Statement × MultilinearPoly R n)) :
    Set (Statement × ((Fin n → Fin 2) → R)) :=
  (fun ⟨stmt, table⟩ => (stmt, tableWitnessEquiv table)) ⁻¹' relation

end Binius.FRIBinius
