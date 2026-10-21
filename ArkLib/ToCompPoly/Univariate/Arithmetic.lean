/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.Primitive
public import CompPoly.Univariate.Raw.Proofs
public import Mathlib.Data.List.FinRange

import all CompPoly.Data.Array.Lemmas
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all VCVio.OracleComp.OracleQuery
import all ToMathlib.Control.WriterT

/-!
# Measured coefficient-array arithmetic

The programs expose field arithmetic and coefficient reads as instructions. Their certified
results agree with the corresponding raw polynomial operations. Profiles count designated
source-control ticks separately from field operations; they do not measure machine runtime.
-/

@[expose] public section

namespace CompPoly
open OracleComp OracleSpec
variable {F A B : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

@[simp]
theorem profileArithmetic_pure (a : A) :
    profileArithmetic (F := F) (pure a) = (a, 0) := by
  simp only [profileArithmetic, simulateQ_pure, AddWriterT.runAdd_pure]
  rfl

/-- A bind adds the profiles of its first program and selected continuation. -/
theorem profileArithmetic_bind (p : OracleComp (ArithmeticSpec F) A)
    (f : A → OracleComp (ArithmeticSpec F) B) :
    profileArithmetic (p >>= f) =
      let a := profileArithmetic p
      let b := profileArithmetic (f a.1)
      (b.1, a.2 + b.2) := by
  simp only [profileArithmetic, simulateQ_bind, AddWriterT.runAdd_bind]
  rfl

/-- One primitive request returns its certified answer and charges its own coordinate. -/
@[simp]
theorem profileArithmetic_query (op : ArithmeticOp F) :
    profileArithmetic (F := F) (liftM (OracleSpec.query (spec := ArithmeticSpec F) op)) =
      (arithmeticAnswer op, arithmeticCost op) := by
  simp [profileArithmetic, simulateQ_query, OracleSpec.query_def, arithmeticMeasured,
    QueryImpl.withCost_apply, AddWriterT.runAdd]
  rfl

/-- A certified program's result is the unique value specified by its response type. -/
@[simp]
theorem profileArithmetic_certified_fst {a : A}
    (program : OracleComp (ArithmeticSpec F) {b : A // b = a}) :
    (profileArithmetic program).1 = ⟨a, rfl⟩ :=
  Subtype.ext (profileArithmetic program).1.property

end CompPoly

namespace CompPoly.Arithmetic
open OracleComp OracleSpec
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- Traverse an explicit list using certified values, counting one control step per cell
and a terminal step. -/
def certifiedMap {A B : Type} (f : A → B)
    (step : (a : A) → OracleComp (ArithmeticSpec F) {b : B // b = f a}) :
    (xs : List A) → OracleComp (ArithmeticSpec F) {ys : List B // ys = xs.map f}
  | [] => do
    tick
    pure ⟨[], rfl⟩
  | x :: xs => do
    tick
    let y ← step x
    let ys ← certifiedMap f step xs
    pure ⟨y.val :: ys.val, by rw [y.property, ys.property]; rfl⟩

/-- Build an array by certified operations on its explicit index list. -/
def certifiedOfFn {n : ℕ} (f : Fin n → F)
    (step : (i : Fin n) → OracleComp (ArithmeticSpec F) {a : F // a = f i}) :
    OracleComp (ArithmeticSpec F) {a : Array F // a = Array.ofFn f} := do
  let values ← certifiedMap f step (List.finRange n)
  pure ⟨values.val.toArray, by rw [values.property, ← List.ofFn_eq_map, List.toArray_ofFn]⟩

/-- Instrumented coefficient-wise scalar multiplication. -/
def smulRaw (x : F) (p : CPolynomial.Raw F) :
    OracleComp (ArithmeticSpec F) {q : CPolynomial.Raw F // q = CPolynomial.Raw.smul x p} := do
  let q ← certifiedOfFn (fun i : Fin p.size ↦ x * p[i]) fun i ↦ do
    let a ← coefficientRead p i.val
    let b ← mul x a.val
    pure ⟨b.val, by simpa [a.property] using b.property⟩
  pure ⟨q.val, by
    rw [q.property]
    apply Array.ext
    · simp [CPolynomial.Raw.smul]
    · intro i hi hi'
      simp [CPolynomial.Raw.smul]⟩

/-- Instrumented padded coefficient addition. -/
def addRaw (p q : CPolynomial.Raw F) :
    OracleComp (ArithmeticSpec F) {r : CPolynomial.Raw F // r = CPolynomial.Raw.addRaw p q} := do
  let r ← certifiedOfFn
    (fun i : Fin (max p.size q.size) ↦ p[i.val]?.getD 0 + q[i.val]?.getD 0) fun i ↦ do
      let a ← coefficientRead p i.val
      let b ← coefficientRead q i.val
      let c ← add a.val b.val
      pure ⟨c.val, by rw [c.property, a.property, b.property]⟩
  pure ⟨r.val, by
    rw [r.property]
    apply Array.ext
    · simp [CPolynomial.Raw.addRaw, Array.size_rightpad, max_comm]
    · intro i hi hi'
      simp only [CPolynomial.Raw.addRaw, CPolynomial.Raw.mk,
        Array.getElem_zipWith]
      rw [Array.rightpad_getElem_eq_getD, Array.rightpad_getElem_eq_getD]
      simp [Array.getD_eq_getD_getElem?]⟩

end CompPoly.Arithmetic

namespace CompPoly.Arithmetic

open OracleComp OracleSpec

variable {F : Type} [Zero F] [Add F] [Sub F] [Monoid F] [Inv F] [DecidableEq F]

/-- Linear repeated multiplication, with an exact count of one multiplication per step. -/
def power (x : F) : (n : ℕ) → OracleComp (ArithmeticSpec F) {y : F // y = x ^ n}
  | 0 => do
    tick
    pure ⟨1, by simp⟩
  | n + 1 => do
    tick
    let y ← power x n
    let z ← mul y.val x
    pure ⟨z.val, by rw [z.property, y.property, pow_succ]⟩

end CompPoly.Arithmetic
