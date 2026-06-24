/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.Multivariate.CMvPolynomial
import CompPoly.Multivariate.Operations
import CompPoly.Multivariate.Rename
import CompPoly.Univariate.ToPoly.Impl
import ArkLib.OracleReduction.OracleInterface
import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Shared CompPoly Wrappers and Oracle Interfaces

Shared degree-bounded computable polynomial types used across protocols, together
with reusable `OracleInterface` instances.
-/

open CompPoly CPoly Std

set_option allowUnsafeReducibility true in
attribute [local reducible] instDecidableEqOfLawfulBEq
attribute [local instance] instDecidableEqOfLawfulBEq

namespace CPoly.CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- `p` has individual degree at most `deg` when every monomial exponent is
 bounded by `deg` in every coordinate. -/
def IndividualDegreeLE (deg : ℕ) (p : CMvPolynomial n R) : Prop :=
  ∀ i : Fin n, ∀ mono ∈ Lawful.monomials p, mono.degreeOf i ≤ deg

omit [BEq R] [LawfulBEq R] in
/-- Evaluation of a mathlib polynomial after conversion to `CMvPolynomial`
agrees with mathlib evaluation. -/
@[simp]
theorem eval_toCMvPolynomial (p : MvPolynomial (Fin n) R) (point : Fin n → R) :
    CMvPolynomial.eval point (toCMvPolynomial p) = MvPolynomial.eval point p := by
  rw [eval_equiv, fromCMvPolynomial_toCMvPolynomial]

omit [BEq R] [LawfulBEq R] in
/-- A bound on `CMvPolynomial.degreeOf` implies the monomial-level individual
degree predicate used by `CMvDegreeLE`. -/
theorem individualDegreeLE_of_degreeOf_le {deg : ℕ} (p : CMvPolynomial n R)
    (h : ∀ i : Fin n, CMvPolynomial.degreeOf i p ≤ deg) :
    IndividualDegreeLE (R := R) deg p := by
  intro i mono hmono
  exact Nat.le_trans
    (by
      unfold CMvPolynomial.degreeOf
      exact Finset.le_sup (s := (Lawful.monomials p).toFinset)
        (f := fun m => m.degreeOf i) (List.mem_toFinset.mpr hmono))
    (h i)

omit [BEq R] [LawfulBEq R] in
/-- Convert a mathlib polynomial into `CMvPolynomial` while transporting
individual degree bounds. -/
theorem individualDegreeLE_toCMvPolynomial_of_degreeOf_le {deg : ℕ}
    (p : MvPolynomial (Fin n) R)
    (h : ∀ i : Fin n, MvPolynomial.degreeOf i p ≤ deg) :
    IndividualDegreeLE (R := R) deg (toCMvPolynomial p) := by
  apply individualDegreeLE_of_degreeOf_le
  intro i
  rw [show CMvPolynomial.degreeOf i (toCMvPolynomial p) =
      MvPolynomial.degreeOf i (fromCMvPolynomial (toCMvPolynomial p)) from by
        exact congrFun (degreeOf_equiv (S := R) (p := toCMvPolynomial p)) i]
  rw [fromCMvPolynomial_toCMvPolynomial]
  exact h i

section Multilinear

variable {S : Type} [BEq S] [CommRing S] [LawfulBEq S]

/-- A computable single-coordinate equality polynomial. -/
abbrev singleEqPolynomial (r : S) (x : CMvPolynomial n S) : CMvPolynomial n S :=
  (1 - C r) * (1 - x) + C r * x

/-- Computable equality polynomial for a point in `Fin n → S`. -/
abbrev eqPolynomial (r : Fin n → S) : CMvPolynomial n S :=
  ∏ i : Fin n, singleEqPolynomial (r i) (X i)

/-- Computable multilinear extension of values indexed by little-endian
`Fin (2 ^ n)` Boolean points. -/
def MLE' (evals : Fin (2 ^ n) → S) : CMvPolynomial n S :=
  ∑ x : Fin n → Fin 2, eqPolynomial (x : Fin n → S) * C (evals (finFunctionFinEquiv x))

/-- The computable single-coordinate equality polynomial maps to the mathlib
single-coordinate equality polynomial. -/
theorem fromCMvPolynomial_singleEqPolynomial_X (r : S) (i : Fin n) :
    fromCMvPolynomial (singleEqPolynomial (n := n) r (X i)) =
      MvPolynomial.singleEqPolynomial r (MvPolynomial.X i) := by
  unfold singleEqPolynomial MvPolynomial.singleEqPolynomial
  rw [CPoly.map_add, CPoly.map_mul, CPoly.map_mul]
  rw [show fromCMvPolynomial (1 - C r : CMvPolynomial n S) =
      fromCMvPolynomial ((1 : CMvPolynomial n S) + -(C r)) from by rw [sub_eq_add_neg]]
  rw [show fromCMvPolynomial (1 - X i : CMvPolynomial n S) =
      fromCMvPolynomial ((1 : CMvPolynomial n S) + -(X i)) from by rw [sub_eq_add_neg]]
  rw [CPoly.map_add, CPoly.map_add, CPoly.map_neg, CPoly.map_neg]
  have hOne : fromCMvPolynomial (1 : CMvPolynomial n S) =
      (1 : MvPolynomial (Fin n) S) := CPoly.map_one
  have hC : fromCMvPolynomial (C r : CMvPolynomial n S) =
      MvPolynomial.C r := fromCMvPolynomial_C r
  have hX : fromCMvPolynomial (X i : CMvPolynomial n S) =
      MvPolynomial.X i := fromCMvPolynomial_X i
  rw [hOne, hC, hX]
  rw [← sub_eq_add_neg, ← sub_eq_add_neg]

/-- The computable equality polynomial maps to the mathlib equality
polynomial. -/
theorem fromCMvPolynomial_eqPolynomial (r : Fin n → S) :
    fromCMvPolynomial (eqPolynomial r) = MvPolynomial.eqPolynomial r := by
  unfold eqPolynomial MvPolynomial.eqPolynomial
  rw [show fromCMvPolynomial (∏ i : Fin n, singleEqPolynomial (r i) (X i)) =
      (polyRingEquiv (n := n) (R := S)) (∏ i : Fin n, singleEqPolynomial (r i) (X i)) from rfl]
  rw [RingEquiv.map_prod]
  congr
  funext i
  exact fromCMvPolynomial_singleEqPolynomial_X (S := S) (n := n) (r i) i

/-- The computable multilinear extension maps to the mathlib multilinear
extension. -/
theorem fromCMvPolynomial_MLE' (evals : Fin (2 ^ n) → S) :
    fromCMvPolynomial (MLE' evals) = MvPolynomial.MLE' evals := by
  unfold MLE' MvPolynomial.MLE' MvPolynomial.MLE
  rw [show fromCMvPolynomial (∑ x : Fin n → Fin 2,
      eqPolynomial (x : Fin n → S) * C (evals (finFunctionFinEquiv x))) =
      (polyRingEquiv (n := n) (R := S)) (∑ x : Fin n → Fin 2,
        eqPolynomial (x : Fin n → S) * C (evals (finFunctionFinEquiv x))) from rfl]
  rw [RingEquiv.map_sum]
  congr
  funext x
  rw [show (polyRingEquiv (n := n) (R := S))
      (eqPolynomial (fun i => ↑(x i)) * C (evals (finFunctionFinEquiv x))) =
      fromCMvPolynomial (eqPolynomial (fun i => ↑(x i)) *
        C (evals (finFunctionFinEquiv x))) from rfl]
  rw [CPoly.map_mul, fromCMvPolynomial_eqPolynomial, fromCMvPolynomial_C]
  rfl

/-- Computable multilinear extensions are multilinear. -/
theorem MLE'_degreeOf (evals : Fin (2 ^ n) → S) (i : Fin n) :
    CMvPolynomial.degreeOf i (MLE' evals) ≤ 1 := by
  rw [show CMvPolynomial.degreeOf i (MLE' evals) =
      MvPolynomial.degreeOf i (fromCMvPolynomial (MLE' evals)) from by
        exact congrFun (degreeOf_equiv (S := S) (p := MLE' evals)) i]
  rw [fromCMvPolynomial_MLE']
  exact MvPolynomial.MLE_degreeOf _ _

/-- Evaluation of the computable equality polynomial agrees with mathlib
evaluation. -/
theorem eval_eqPolynomial (r point : Fin n → S) :
    CMvPolynomial.eval point (eqPolynomial r) =
      MvPolynomial.eval point (MvPolynomial.eqPolynomial r) := by
  rw [eval_equiv, fromCMvPolynomial_eqPolynomial]

/-- Evaluation of a computable constant polynomial. -/
@[simp]
theorem eval_C (point : Fin n → S) (r : S) :
    CMvPolynomial.eval point (C r : CMvPolynomial n S) = r := by
  rw [eval_equiv, fromCMvPolynomial_C, MvPolynomial.eval_C]

/-- Evaluation distributes over addition. -/
@[simp]
theorem eval_add (point : Fin n → S) (p q : CMvPolynomial n S) :
    CMvPolynomial.eval point (p + q) =
      CMvPolynomial.eval point p + CMvPolynomial.eval point q := by
  rw [eval_equiv, CPoly.map_add]
  rw [eval_equiv (p := p), eval_equiv (p := q), MvPolynomial.eval_add]

/-- Evaluation distributes over multiplication. -/
@[simp]
theorem eval_mul (point : Fin n → S) (p q : CMvPolynomial n S) :
    CMvPolynomial.eval point (p * q) =
      CMvPolynomial.eval point p * CMvPolynomial.eval point q := by
  rw [eval_equiv, CPoly.map_mul]
  rw [eval_equiv (p := p), eval_equiv (p := q), MvPolynomial.eval_mul]

/-- Evaluation distributes over negation. -/
@[simp]
theorem eval_neg (point : Fin n → S) (p : CMvPolynomial n S) :
    CMvPolynomial.eval point (-p) = -CMvPolynomial.eval point p := by
  rw [eval_equiv, CPoly.map_neg]
  rw [eval_equiv (p := p), MvPolynomial.eval_neg]

/-- Evaluation distributes over subtraction. -/
@[simp]
theorem eval_sub (point : Fin n → S) (p q : CMvPolynomial n S) :
    CMvPolynomial.eval point (p - q) =
      CMvPolynomial.eval point p - CMvPolynomial.eval point q := by
  rw [show CMvPolynomial.eval point (p - q) =
    CMvPolynomial.eval point (p + -q) from by rw [sub_eq_add_neg]]
  rw [eval_add, eval_neg, sub_eq_add_neg]

/-- Evaluation distributes over finite sums. -/
@[simp]
theorem eval_sum {ι : Type} (point : Fin n → S) (s : Finset ι)
    (f : ι → CMvPolynomial n S) :
    CMvPolynomial.eval point (∑ j ∈ s, f j) =
      ∑ j ∈ s, CMvPolynomial.eval point (f j) := by
  rw [eval_equiv]
  rw [show fromCMvPolynomial (∑ j ∈ s, f j) =
      (polyRingEquiv (n := n) (R := S)) (∑ j ∈ s, f j) from rfl]
  rw [map_sum, MvPolynomial.eval_sum]
  congr
  funext j
  rw [show (polyRingEquiv (n := n) (R := S)) (f j) = fromCMvPolynomial (f j) from rfl]
  rw [← eval_equiv]

/-- The computable multilinear extension interpolates the given values on the
Boolean hypercube. -/
theorem MLE'_eval_zeroOne (evals : Fin (2 ^ n) → S) (x : Fin (2 ^ n)) :
    CMvPolynomial.eval (MvPolynomial.booleanPoint (R := S) n x) (MLE' evals) = evals x := by
  rw [eval_equiv, fromCMvPolynomial_MLE']
  unfold MvPolynomial.MLE'
  rw [show MvPolynomial.booleanPoint (R := S) n x =
      ((finFunctionFinEquiv.symm x : Fin n → Fin 2) : Fin n → S) from rfl]
  have h := MvPolynomial.MLE_eval_zeroOne (R := S)
    (x := finFunctionFinEquiv.symm x)
    (evals := evals ∘ finFunctionFinEquiv)
  simpa using h

/-- Constants have zero degree in every coordinate. -/
theorem degreeOf_C (r : S) (i : Fin n) :
    CMvPolynomial.degreeOf i (C r : CMvPolynomial n S) = 0 := by
  rw [show CMvPolynomial.degreeOf i (C r : CMvPolynomial n S) =
      MvPolynomial.degreeOf i (fromCMvPolynomial (C r : CMvPolynomial n S)) from by
        exact congrFun (degreeOf_equiv (S := S) (p := (C r : CMvPolynomial n S))) i]
  rw [fromCMvPolynomial_C]
  exact MvPolynomial.degreeOf_C r i

/-- Degree in one coordinate is subadditive under multiplication. -/
theorem degreeOf_mul_le (i : Fin n) (p q : CMvPolynomial n S) :
    CMvPolynomial.degreeOf i (p * q) ≤
      CMvPolynomial.degreeOf i p + CMvPolynomial.degreeOf i q := by
  rw [show CMvPolynomial.degreeOf i (p * q) =
      MvPolynomial.degreeOf i (fromCMvPolynomial (p * q)) from by
        exact congrFun (degreeOf_equiv (S := S) (p := p * q)) i]
  rw [show CMvPolynomial.degreeOf i p =
      MvPolynomial.degreeOf i (fromCMvPolynomial p) from by
        exact congrFun (degreeOf_equiv (S := S) (p := p)) i]
  rw [show CMvPolynomial.degreeOf i q =
      MvPolynomial.degreeOf i (fromCMvPolynomial q) from by
        exact congrFun (degreeOf_equiv (S := S) (p := q)) i]
  rw [CPoly.map_mul]
  exact MvPolynomial.degreeOf_mul_le i _ _

/-- Degree in one coordinate is bounded by the supremum across a finite sum. -/
theorem degreeOf_sum_le {ι : Type} (i : Fin n) (s : Finset ι)
    (f : ι → CMvPolynomial n S) :
    CMvPolynomial.degreeOf i (∑ j ∈ s, f j) ≤
      s.sup fun j => CMvPolynomial.degreeOf i (f j) := by
  rw [show CMvPolynomial.degreeOf i (∑ j ∈ s, f j) =
      MvPolynomial.degreeOf i (fromCMvPolynomial (∑ j ∈ s, f j)) from by
        exact congrFun (degreeOf_equiv (S := S) (p := ∑ j ∈ s, f j)) i]
  rw [show fromCMvPolynomial (∑ j ∈ s, f j) =
      (polyRingEquiv (n := n) (R := S)) (∑ j ∈ s, f j) from rfl]
  rw [map_sum]
  calc
    _ ≤ s.sup fun j => MvPolynomial.degreeOf i (fromCMvPolynomial (f j)) :=
      MvPolynomial.degreeOf_sum_le i s fun j => fromCMvPolynomial (f j)
    _ = s.sup fun j => CMvPolynomial.degreeOf i (f j) := by
      congr
      funext j
      exact (congrFun (degreeOf_equiv (S := S) (p := f j)) i).symm

/-- Degree in one coordinate is bounded by the maximum across subtraction. -/
theorem degreeOf_sub_le (i : Fin n) (p q : CMvPolynomial n S) :
    CMvPolynomial.degreeOf i (p - q) ≤
      max (CMvPolynomial.degreeOf i p) (CMvPolynomial.degreeOf i q) := by
  rw [show CMvPolynomial.degreeOf i (p - q) =
      MvPolynomial.degreeOf i (fromCMvPolynomial (p - q)) from by
        exact congrFun (degreeOf_equiv (S := S) (p := p - q)) i]
  rw [show CMvPolynomial.degreeOf i p =
      MvPolynomial.degreeOf i (fromCMvPolynomial p) from by
        exact congrFun (degreeOf_equiv (S := S) (p := p)) i]
  rw [show CMvPolynomial.degreeOf i q =
      MvPolynomial.degreeOf i (fromCMvPolynomial q) from by
        exact congrFun (degreeOf_equiv (S := S) (p := q)) i]
  rw [show fromCMvPolynomial (p - q) = fromCMvPolynomial (p + -q) from by
    rw [sub_eq_add_neg]]
  rw [CPoly.map_add, CPoly.map_neg]
  rw [← sub_eq_add_neg]
  exact MvPolynomial.degreeOf_sub_le i _ _

/-- Computable equality polynomials are multilinear. -/
theorem eqPolynomial_degreeOf (r : Fin n → S) (i : Fin n) :
    CMvPolynomial.degreeOf i (eqPolynomial r) ≤ 1 := by
  rw [show CMvPolynomial.degreeOf i (eqPolynomial r) =
      MvPolynomial.degreeOf i (fromCMvPolynomial (eqPolynomial r)) from by
        exact congrFun (degreeOf_equiv (S := S) (p := eqPolynomial r)) i]
  rw [fromCMvPolynomial_eqPolynomial]
  exact MvPolynomial.eqPolynomial_degreeOf r i

end Multilinear

end CPoly.CMvPolynomial

/-- A computable univariate polynomial with `natDegree ≤ d`. -/
def CDegreeLE (R : Type) [BEq R] [Semiring R] [LawfulBEq R] (d : ℕ) :=
  { p : CPolynomial R // p.natDegree ≤ d }

/-- A computable multivariate polynomial with individual degree at most `d` in
 every coordinate. -/
def CMvDegreeLE
    (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] (n d : ℕ) :=
  { p : CMvPolynomial n R // CMvPolynomial.IndividualDegreeLE (R := R) d p }

section OracleInterface

open OracleComp OracleSpec

variable {n : ℕ} {deg : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

instance instOracleInterfaceCMvPolynomial :
    OracleInterface (CMvPolynomial n R) where
   Query := Fin n → R
   toOC := {
     spec := (Fin n → R) →ₒ R
     impl := fun points => do return CMvPolynomial.eval points (← read)
   }

instance instOracleInterfaceCPolynomial [Nontrivial R] :
    OracleInterface (CPolynomial R) where
   Query := R
   toOC := {
     spec := R →ₒ R
     impl := fun point => do return CPolynomial.eval point (← read)
   }

instance instOracleInterfaceCDegreeLE [Semiring R] :
    OracleInterface (CDegreeLE R deg) where
   Query := R
   toOC := {
     spec := R →ₒ R
     impl := fun point => do return CPolynomial.eval point (← read).1
   }

instance instOracleInterfaceCMvDegreeLE :
    OracleInterface (CMvDegreeLE R n deg) where
   Query := Fin n → R
   toOC := {
     spec := (Fin n → R) →ₒ R
     impl := fun points => do return CMvPolynomial.eval points (← read).1
   }

end OracleInterface
